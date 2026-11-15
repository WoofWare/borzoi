//! The assembly env's reference resolution records its read set
//! (`docs/incremental-lsp-plan.md`, D3, Stage 6a), and the read set is sound.
//!
//! Over generated restored-project fixtures (an assets file with packages
//! whose DLLs are in the primary package folder, only in the fallback one,
//! or in neither, a framework pack with versions that hold the
//! project's TFM or not, and sibling F# projects built under the project's
//! TFM, another, both, or neither, recorded in the assets file or not, and
//! multi-targeted with a restore of their own that pins their TFM or not),
//! `borzoi_msbuild::observed::soundness::sweep_with` perturbs every file
//! and symlink under the fixture one at a time. Whenever every answer in the
//! read set still stands, resolving again gives the same reference DLLs; and
//! two perturbations the plan names must fail validation: a newer pack
//! version installed beside the recorded ones, and an unbuilt sibling's
//! output DLL created where the resolution found none.
//!
//! The entry project may be reached through a symlink ([`Layout`]): its
//! directory, its `obj` directory, its assets file, or a directory above
//! every project; and a sibling's `bin` may be a symlink, and its missing
//! output a dangling one. Each link's target is relative or absolute. A read
//! recorded under one spelling and confirmed under another then meets every
//! link the sweep deletes, dangles, retargets to another link's target, or
//! whose missing target it creates. Retargeting the entry's link must fail
//! validation, both to a copy whose assets file differs and to an identical
//! copy elsewhere: the assets file's text is then unchanged under the
//! spelling it was read by, but its canonical path, from which the
//! resolution resolves the project paths the assets file records, has
//! moved, and only the canonicalisation's read sees that.
//!
//! The env itself carries the read set, each DLL's stamp included, whether
//! the DLL's projection came from reading it or from the assembly cache.
//!
//! What a cached env confirms before it is served again (Stage 6b) is that
//! read set less the contents of the installed versions it trusts: the
//! framework pack's, and each committed package's in the NuGet folder. The
//! same sweep holds that to soundness over the project tree, where the
//! installed-version axiom says nothing.

use std::cell::RefCell;
use std::path::{Path, PathBuf};

use borzoi::assembly_cache::AssemblyCache;
use borzoi::sdk_discovery::SdkDiscoveryEnv;
use borzoi::semantic::SemanticState;
use borzoi::vfs::Nanos;
use borzoi::workspace::Workspace;
use borzoi_msbuild::observed::soundness::{Edit, Perturbation, Tally, Why, sweep_with};
use borzoi_msbuild::observed::{Observation, ReadSet};
use proptest::prelude::*;
use tempfile::TempDir;

use crate::common::host_fs;

const TFM: &str = "net8.0";
const OTHER_TFM: &str = "net9.0";

/// One sibling F# project the entry references.
#[derive(Clone, Debug)]
struct Sibling {
    /// The TFM directories its `bin/Debug` holds an output in.
    built: Vec<&'static str>,
    /// Whether the entry's assets file records it as a project reference.
    in_assets: bool,
    /// Whether the project names its output (`TargetName`), rather than
    /// leaving the name to the assets file.
    names_output: bool,
    /// Whether it targets both TFMs, with an assets file of its own
    /// declaring them: the entry's producer-TFM recovery then pins the TFM
    /// its output is looked for under, which nothing else does. It imports
    /// a file under the other TFM alone, which only the graph walk's
    /// evaluation of that TFM's branch reads, and references a built project
    /// of its own (`R<i>`), which an extra perturbation removes under that
    /// TFM alone through the import.
    multi: bool,
    /// Whether its `bin` directory is a symlink to a directory elsewhere.
    bin_linked: bool,
    /// Whether, unbuilt under the project's TFM, its output DLL's path is a
    /// symlink to a file that does not exist.
    dangling_output: bool,
}

/// How the entry project is reached through a symlink.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Layout {
    Plain,
    /// `ws/P` is a symlink to a directory elsewhere.
    ProjectDir,
    /// `ws/P/obj` is a symlink to a directory elsewhere.
    Obj,
    /// `ws/P/obj/project.assets.json` is a symlink to a file elsewhere.
    AssetsFile,
    /// Every project lies under `ws/tree`, and is reached as `ws/link/…`,
    /// `ws/link` being a symlink to it.
    Ancestor,
}

const LAYOUTS: [Layout; 5] = [
    Layout::Plain,
    Layout::ProjectDir,
    Layout::Obj,
    Layout::AssetsFile,
    Layout::Ancestor,
];

/// Which package folder holds a package.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Folder {
    Neither,
    Primary,
    Fallback,
}

#[derive(Clone, Debug)]
struct World {
    /// Where each package's compile DLL is.
    packages: Vec<Folder>,
    /// The framework pack's versions, and whether each holds `ref/net8.0`.
    pack_versions: Vec<(u32, bool)>,
    siblings: Vec<Sibling>,
    layout: Layout,
    /// Whether each symlink's target is absolute, rather than relative to
    /// the link's directory.
    absolute_links: bool,
}

fn sibling() -> impl Strategy<Value = Sibling> {
    (
        prop::sample::subsequence(vec![TFM, OTHER_TFM], 0..=2),
        any::<bool>(),
        prop::bool::weighted(0.8),
        any::<bool>(),
        prop::bool::weighted(0.3),
        prop::bool::weighted(0.3),
    )
        .prop_map(
            |(built, in_assets, names_output, multi, bin_linked, dangling_output)| Sibling {
                built,
                in_assets,
                names_output,
                multi,
                bin_linked,
                dangling_output,
            },
        )
}

fn world() -> impl Strategy<Value = World> {
    (
        prop::collection::vec(
            prop::sample::select(vec![Folder::Neither, Folder::Primary, Folder::Fallback]),
            0..3,
        ),
        prop::collection::vec((1u32..4, prop::bool::weighted(0.7)), 1..3),
        prop::collection::vec(sibling(), 0..3),
        prop::sample::select(LAYOUTS.to_vec()),
        any::<bool>(),
    )
        .prop_map(
            |(packages, pack_versions, siblings, layout, absolute_links)| World {
                packages,
                pack_versions,
                siblings,
                layout,
                absolute_links,
            },
        )
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// What laying a world down made: the entry project's path, the directory
/// every project's directory is spelt under (`ws`, or `ws/link`), and the
/// retargets of the entry's symlink, if it has one, each of which must fail
/// validation.
struct Laid {
    entry: PathBuf,
    base: PathBuf,
    retargets: Vec<Edit>,
}

/// The target to write in a symlink at `link` that leads to `target`, a path
/// under the canonical root: `target` itself, or the path to it from the
/// link's directory as the file system resolves that directory.
fn link_target(link: &Path, target: &Path, absolute: bool) -> PathBuf {
    if absolute {
        return target.to_path_buf();
    }
    let from = host_fs::canonicalize(link.parent().unwrap()).unwrap();
    let common = from
        .components()
        .zip(target.components())
        .take_while(|(a, b)| a == b)
        .count();
    let mut out = PathBuf::new();
    for _ in from.components().skip(common) {
        out.push("..");
    }
    for part in target.components().skip(common) {
        out.push(part);
    }
    out
}

fn symlink(link: &Path, target: &Path, absolute: bool) {
    std::fs::create_dir_all(link.parent().unwrap()).unwrap();
    let written = link_target(link, target, absolute);
    std::os::unix::fs::symlink(written, link).unwrap();
}

/// Move what is at `from` to `to`, and leave a symlink to it at `from`.
fn move_and_link(from: &Path, to: &Path, absolute: bool) {
    std::fs::create_dir_all(to.parent().unwrap()).unwrap();
    std::fs::rename(from, to).unwrap();
    symlink(from, to, absolute);
}

/// Copy the tree at `from` to `to`, a symlink as the same target.
fn copy_tree(from: &Path, to: &Path) {
    let meta = host_fs::symlink_metadata(from).unwrap();
    if meta.file_type().is_symlink() {
        std::os::unix::fs::symlink(host_fs::read_link(from).unwrap(), to).unwrap();
    } else if meta.is_dir() {
        std::fs::create_dir_all(to).unwrap();
        for entry in host_fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            copy_tree(&entry.path(), &to.join(entry.file_name()));
        }
    } else {
        write(to, &host_fs::read_to_string(from).unwrap());
    }
}

/// The entry's assets file at `path`, rewritten to name no package, project
/// or framework.
fn strip_assets(path: &Path) {
    let mut assets: serde_json::Value =
        serde_json::from_str(&host_fs::read_to_string(path).unwrap()).unwrap();
    assets["targets"][TFM] = serde_json::json!({});
    assets["libraries"] = serde_json::json!({});
    assets["project"]["frameworks"][TFM] = serde_json::json!({});
    write(path, &serde_json::to_string(&assets).unwrap());
}

/// Lay `world` down under `root`, which must be canonical.
fn lay_down(root: &Path, world: &World) -> Laid {
    let nuget = root.join("nuget");
    let fallback = root.join("fallback");
    std::fs::create_dir_all(&nuget).unwrap();
    std::fs::create_dir_all(&fallback).unwrap();
    for (version, holds_tfm) in &world.pack_versions {
        let dir = root
            .join("dotnet/packs/Microsoft.NETCore.App.Ref")
            .join(format!("{version}.0.0"));
        let tfm = if *holds_tfm { TFM } else { OTHER_TFM };
        write(&dir.join("ref").join(tfm).join("System.Runtime.dll"), "dll");
    }
    let mut targets = serde_json::Map::new();
    let mut libraries = serde_json::Map::new();
    for (i, folder) in world.packages.iter().enumerate() {
        let id = format!("pkg{i}");
        let rel = format!("lib/{TFM}/Pkg{i}.dll");
        let holder = match folder {
            Folder::Neither => None,
            Folder::Primary => Some(&nuget),
            Folder::Fallback => Some(&fallback),
        };
        if let Some(holder) = holder {
            write(&holder.join(&id).join("1.0.0").join(&rel), "dll");
        }
        targets.insert(
            format!("Pkg{i}/1.0.0"),
            serde_json::json!({ "type": "package", "compile": { rel: {} } }),
        );
        libraries.insert(
            format!("Pkg{i}/1.0.0"),
            serde_json::json!({ "type": "package", "path": format!("{id}/1.0.0") }),
        );
    }
    let mut refs = String::new();
    for (i, s) in world.siblings.iter().enumerate() {
        let name = format!("Q{i}");
        let dir = root.join("ws").join(&name);
        let target_name = if s.names_output {
            format!("<TargetName>{name}</TargetName>")
        } else {
            String::new()
        };
        let (tfms, import) = if s.multi {
            write(&dir.join("other.props"), "<Project />\n");
            let r = format!("R{i}");
            let r_dir = root.join("ws").join(&r);
            write(
                &r_dir.join(format!("{r}.fsproj")),
                &format!(
                    "<Project><PropertyGroup><TargetFramework>{TFM}</TargetFramework><TargetName>{r}</TargetName></PropertyGroup></Project>\n"
                ),
            );
            write(
                &r_dir.join("bin/Debug").join(TFM).join(format!("{r}.dll")),
                "dll",
            );
            (
                format!("<TargetFrameworks>{TFM};{OTHER_TFM}</TargetFrameworks>"),
                format!(
                    "<ItemGroup><ProjectReference Include=\"../{r}/{r}.fsproj\" /></ItemGroup><Import Project=\"other.props\" Condition=\"'$(TargetFramework)' == '{OTHER_TFM}'\" />"
                ),
            )
        } else {
            (
                format!("<TargetFramework>{TFM}</TargetFramework>"),
                String::new(),
            )
        };
        write(
            &dir.join(format!("{name}.fsproj")),
            &format!(
                "<Project><PropertyGroup>{tfms}{target_name}</PropertyGroup>{import}</Project>\n"
            ),
        );
        if s.multi {
            let own = serde_json::json!({
                "version": 3,
                "targets": { TFM: {}, OTHER_TFM: {} },
                "libraries": {},
                "packageFolders": { nuget.to_str().unwrap(): {} },
                "project": { "frameworks": { TFM: {}, OTHER_TFM: {} } },
            });
            write(
                &dir.join("obj/project.assets.json"),
                &serde_json::to_string(&own).unwrap(),
            );
        }
        for tfm in &s.built {
            write(
                &dir.join("bin/Debug").join(tfm).join(format!("{name}.dll")),
                "dll",
            );
        }
        refs.push_str(&format!(
            "<ProjectReference Include=\"../{name}/{name}.fsproj\" />"
        ));
        if s.in_assets {
            targets.insert(
                format!("{name}/1.0.0"),
                serde_json::json!({
                    "type": "project",
                    "framework": ".NETCoreApp,Version=v8.0",
                    "compile": { format!("bin/placeholder/{name}.dll"): {} },
                }),
            );
            libraries.insert(
                format!("{name}/1.0.0"),
                serde_json::json!({
                    "type": "project",
                    "path": format!("../{name}/{name}.fsproj"),
                    "msbuildProject": format!("../{name}/{name}.fsproj"),
                }),
            );
        }
    }
    let entry = root.join("ws/P/P.fsproj");
    write(
        &entry,
        &format!(
            "<Project><PropertyGroup><TargetFramework>{TFM}</TargetFramework></PropertyGroup><ItemGroup>{refs}</ItemGroup></Project>\n"
        ),
    );
    let assets = serde_json::json!({
        "version": 3,
        "targets": { TFM: targets },
        "libraries": libraries,
        "packageFolders": { nuget.to_str().unwrap(): {}, fallback.to_str().unwrap(): {} },
        "project": { "frameworks": { TFM: { "frameworkReferences": { "Microsoft.NETCore.App": {} } } } },
    });
    write(
        &root.join("ws/P/obj/project.assets.json"),
        &serde_json::to_string(&assets).unwrap(),
    );
    link_up(root, world, entry)
}

/// Turn the plain tree [`lay_down`] wrote into `world`'s symlinked one. Every
/// link target lies under `ws/vault` (or, for [`Layout::Ancestor`], is
/// `ws/tree`), and each link is made after the moves that would change what
/// a relative target resolves against.
fn link_up(root: &Path, world: &World, entry: PathBuf) -> Laid {
    let abs = world.absolute_links;
    let ws = root.join("ws");
    let vault = ws.join("vault");
    // The entry's link, its target, and where the assets file lies in the
    // target.
    let entry_link = match world.layout {
        Layout::Plain => None,
        Layout::ProjectDir => Some((ws.join("P"), vault.join("P"), "obj/project.assets.json")),
        Layout::Obj => Some((ws.join("P/obj"), vault.join("objP"), "project.assets.json")),
        Layout::AssetsFile => Some((
            ws.join("P/obj/project.assets.json"),
            vault.join("P.assets.json"),
            "",
        )),
        Layout::Ancestor => {
            let tree = ws.join("tree");
            std::fs::create_dir_all(&tree).unwrap();
            for dir in host_fs::read_dir(&ws).unwrap() {
                let dir = dir.unwrap();
                if dir.file_name() != "tree" {
                    std::fs::rename(dir.path(), tree.join(dir.file_name())).unwrap();
                }
            }
            symlink(&ws.join("link"), &tree, abs);
            None
        }
    };
    if let Some((link, target, _)) = &entry_link {
        move_and_link(link, target, abs);
    }
    let base = if world.layout == Layout::Ancestor {
        ws.join("link")
    } else {
        ws.clone()
    };
    for (i, s) in world.siblings.iter().enumerate() {
        let name = format!("Q{i}");
        let bin = base.join(&name).join("bin");
        if s.bin_linked {
            let target = vault.join(format!("bin{name}"));
            if host_fs::symlink_metadata(&bin).is_ok() {
                move_and_link(&bin, &target, abs);
            } else {
                std::fs::create_dir_all(&target).unwrap();
                symlink(&bin, &target, abs);
            }
        }
        if s.dangling_output && !s.built.contains(&TFM) {
            symlink(
                &bin.join("Debug").join(TFM).join(format!("{name}.dll")),
                &vault.join(format!("missing-{name}.dll")),
                abs,
            );
        }
    }
    // The retargets of the entry's link: to a copy of its target whose
    // assets file differs, and to an identical copy one directory deeper,
    // where the project paths the assets file records resolve elsewhere.
    let entry_link = match world.layout {
        Layout::Ancestor => Some((
            ws.join("link"),
            ws.join("tree"),
            "P/obj/project.assets.json",
        )),
        _ => entry_link,
    };
    let mut retargets = Vec::new();
    if let Some((link, target, assets)) = &entry_link {
        let mut differing = target.clone().into_os_string();
        differing.push("-alt");
        let differing = PathBuf::from(differing);
        copy_tree(target, &differing);
        strip_assets(&if assets.is_empty() {
            differing.clone()
        } else {
            differing.join(assets)
        });
        let identical = vault.join("deeper").join(target.file_name().unwrap());
        std::fs::create_dir_all(identical.parent().unwrap()).unwrap();
        copy_tree(target, &identical);
        for alt in [differing, identical] {
            retargets.push(Edit::Link(link.clone(), link_target(link, &alt, abs)));
        }
    }
    let entry = base.join(entry.strip_prefix(&ws).unwrap());
    Laid {
        entry,
        base,
        retargets,
    }
}

/// A workspace that finds no SDK of the host's.
fn workspace(root: &Path) -> Workspace {
    Workspace::with_env(SdkDiscoveryEnv {
        dotnet_root: Some(root.join("no-dotnet")),
        ..SdkDiscoveryEnv::default()
    })
}

/// What the plan names as having to fail validation: a newer pack version
/// installed, and each sibling's output built where it is not and the
/// resolution looked for it (it looks only for a sibling whose TFM and output
/// name it trusts). The rest of the siblings' outputs are built too, and the
/// sweep holds those to soundness alone.
fn extras(
    root: &Path,
    laid: &Laid,
    world: &World,
    searched: impl Fn(&Path) -> bool,
) -> (Vec<Perturbation>, usize) {
    let base = &laid.base;
    let newest = world
        .pack_versions
        .iter()
        .map(|(v, _)| *v)
        .max()
        .unwrap_or(0)
        + 1;
    let mut must_stale = 1;
    let mut out = vec![Perturbation {
        why: Why::Extra,
        edits: vec![Edit::Write(
            root.join("dotnet/packs/Microsoft.NETCore.App.Ref")
                .join(format!("{newest}.0.0/ref/{TFM}/System.Runtime.dll")),
            b"dll".to_vec(),
        )],
    }];
    for (i, s) in world.siblings.iter().enumerate() {
        if s.multi {
            out.push(Perturbation {
                why: Why::Extra,
                edits: vec![Edit::Write(
                    base.join(format!("Q{i}")).join("other.props"),
                    format!(
                        "<Project><ItemGroup><ProjectReference Remove=\"../R{i}/R{i}.fsproj\" /></ItemGroup></Project>\n"
                    )
                    .into_bytes(),
                )],
            });
        }
        if !s.built.contains(&TFM) {
            let name = format!("Q{i}");
            if searched(&base.join(&name).join("bin")) {
                must_stale += 1;
            }
            out.push(Perturbation {
                why: Why::Extra,
                edits: vec![Edit::Write(
                    base.join(&name).join(format!("bin/Debug/{TFM}/{name}.dll")),
                    b"dll".to_vec(),
                )],
            });
        }
    }
    for retarget in &laid.retargets {
        must_stale += 1;
        out.push(Perturbation {
            why: Why::Extra,
            edits: vec![retarget.clone()],
        });
    }
    (out, must_stale)
}

/// What resolving a world found, summed over cases.
#[derive(Debug, Default)]
struct Reached {
    package_dlls: u64,
    framework_dlls: u64,
    sibling_dlls: u64,
    layouts: std::collections::BTreeSet<Layout>,
    tally: Tally,
}

fn check(world: &World, reached: &mut Reached) {
    let tmp = TempDir::new().unwrap();
    // Canonical, so the read set's spellings lie under the swept root.
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    let laid = lay_down(&root, world);
    let entry = laid.entry.clone();
    let dotnet = root.join("dotnet");
    let compute = || {
        let mut ws = workspace(&root);
        let tfm = ws.served_tfm_for_project(&entry);
        let mut semantic = SemanticState::new();
        let (dlls, reads) =
            semantic.reference_resolution_for_project(&entry, Some(&dotnet), &tfm, &ws);
        ((tfm, dlls, reads.unrecorded), reads.reads)
    };
    let ((_, dlls, unrecorded), reads) = compute();
    assert!(unrecorded.is_empty(), "{unrecorded:?}");
    for dll in &dlls {
        let s = dll.to_string_lossy();
        if s.contains("/nuget/") || s.contains("/fallback/") {
            reached.package_dlls += 1;
        } else if s.contains("/packs/") {
            reached.framework_dlls += 1;
        } else {
            reached.sibling_dlls += 1;
        }
    }
    reached.layouts.insert(world.layout);
    let (extras, must_stale) = extras(&root, &laid, world, |bin| {
        reads.reads().iter().any(|read| read.path == bin)
    });
    let tally = sweep_with(&root, &compute, &extras);
    assert!(
        tally.stale.get(&Why::Extra).copied().unwrap_or(0) >= must_stale,
        "an installed pack version, a newly built sibling or the entry's link retargeted left \
         the read set standing: {tally:?}"
    );
    reached.tally.absorb(&tally);
}

/// What [`check_confirmed`] saw, summed over cases.
#[derive(Debug, Default)]
struct Confirmed {
    /// Reads the env trusts as installed contents rather than confirms.
    exempt: u64,
    /// Of those, reads inside a package version.
    exempt_packages: u64,
    tally: Tally,
}

/// Lay `world` down, with every package in the NuGet folder committed (its
/// `.nupkg.metadata` written), and sweep the project tree (`ws/`) holding
/// the reads a cached env confirms, inside a generation whose time is far
/// past every file's, to soundness. A DLL's stamp is left out of the
/// compared set: it is racy for as long as the fixture is fresh, and the
/// stamp test below holds it.
fn check_confirmed(world: &World, confirmed: &mut Confirmed) {
    let tmp = TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    let laid = lay_down(&root, world);
    let entry = laid.entry.clone();
    // NuGet reads its user settings from a home that exists.
    std::fs::create_dir_all(root.join("home")).unwrap();
    let nuget = root.join("nuget");
    for (i, folder) in world.packages.iter().enumerate() {
        if *folder == Folder::Primary {
            write(&nuget.join(format!("pkg{i}/1.0.0/.nupkg.metadata")), "{}");
        }
    }
    let dotnet = root.join("dotnet");
    let resolve = || {
        let mut ws = Workspace::with_env(SdkDiscoveryEnv {
            dotnet_root: Some(root.join("no-dotnet")),
            nuget_packages_dir: Some(nuget.clone()),
            home_dir: Some(root.join("home")),
            ..SdkDiscoveryEnv::default()
        });
        ws.begin_generation(Nanos(i128::MAX / 2));
        let tfm = ws.served_tfm_for_project(&entry);
        let mut semantic = SemanticState::new();
        // The DLLs the resolution names, whether or not they project: the
        // fixture's DLLs are not assemblies, so the env keeps none.
        let (dlls, _) = semantic.reference_resolution_for_project(&entry, Some(&dotnet), &tfm, &ws);
        let (reads, _) = semantic.env_reads_for_project(&entry, Some(&dotnet), &tfm, &ws);
        // An env a transient failure left incomplete is not cached, and
        // confirms nothing: what it read is what it depends on.
        let checks = semantic.env_confirmed_reads_for_project(&entry, Some(&dotnet), &tfm, &ws);
        ws.end_generation();
        let checks = checks.unwrap_or_else(|| reads.reads.reads().to_vec());
        (dlls, reads.reads.clone(), checks)
    };
    let (_, reads, checks) = resolve();
    for read in reads.reads() {
        if checks.contains(read) {
            continue;
        }
        confirmed.exempt += 1;
        let inside = |dir: &std::path::Path| read.path.starts_with(dir) && read.path != dir;
        assert!(
            inside(&dotnet.join("packs/Microsoft.NETCore.App.Ref")) || inside(&nuget),
            "a read outside the installs is not confirmed: {read:?}"
        );
        if inside(&nuget) {
            confirmed.exempt_packages += 1;
        }
    }
    let compute = || {
        let (dlls, _, checks) = resolve();
        let checks: ReadSet = checks
            .into_iter()
            .filter(|read| !matches!(read.observation, Observation::Stamp(_)))
            .collect();
        (dlls, checks)
    };
    // Installing a pack version is not an in-place change to an installed
    // one: the listing that chose the version is confirmed, and must fail.
    let newest = world
        .pack_versions
        .iter()
        .map(|(v, _)| *v)
        .max()
        .unwrap_or(0)
        + 1;
    let install = Perturbation {
        why: Why::Extra,
        edits: vec![Edit::Write(
            dotnet
                .join("packs/Microsoft.NETCore.App.Ref")
                .join(format!("{newest}.0.0/ref/{TFM}/System.Runtime.dll")),
            b"dll".to_vec(),
        )],
    };
    let mut extras = vec![install];
    extras.extend(laid.retargets.iter().map(|retarget| Perturbation {
        why: Why::Extra,
        edits: vec![retarget.clone()],
    }));
    let tally = sweep_with(&root.join("ws"), &compute, &extras);
    assert_eq!(
        tally.stale.get(&Why::Extra).copied().unwrap_or(0),
        extras.len(),
        "a pack version installed, or the entry's link retargeted, left what the env confirms \
         standing: {tally:?}"
    );
    confirmed.tally.absorb(&tally);
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 8, ..ProptestConfig::default() })]

    #[test]
    fn the_env_resolution_read_set_is_sound(world in world()) {
        check(&world, &mut Reached::default());
    }

    #[test]
    fn what_an_env_confirms_is_sound_outside_the_installs(world in world()) {
        check_confirmed(&world, &mut Confirmed::default());
    }
}

/// Over a fixed seed's worth of worlds, a cached env trusts reads inside the
/// framework pack and inside committed packages rather than confirming
/// them, and the sweep of the project tree moves the resolution.
#[test]
fn an_env_trusts_installed_contents_and_confirms_the_rest() {
    use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 8,
            failure_persistence: None,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &[5; 32]),
    );
    let confirmed = RefCell::new(Confirmed::default());
    runner
        .run(&world(), |world| {
            check_confirmed(&world, &mut confirmed.borrow_mut());
            Ok(())
        })
        .unwrap();
    let c = confirmed.into_inner();
    eprintln!("{c:?}");
    assert!(
        c.exempt > c.exempt_packages && c.exempt_packages > 0 && c.tally.moved(Why::Delete) > 0,
        "{c:?}"
    );
}

/// Over a fixed seed's worth of worlds, the resolution finds package,
/// framework and sibling DLLs; deletions and the plan's extras move it; and
/// creating what it recorded absent fails validation.
#[test]
fn the_generator_reaches_every_reference_kind_and_moves_the_resolution() {
    use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 8,
            failure_persistence: None,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &[3; 32]),
    );
    let reached = RefCell::new(Reached::default());
    runner
        .run(&world(), |world| {
            check(&world, &mut reached.borrow_mut());
            Ok(())
        })
        .unwrap();
    let r = reached.into_inner();
    eprintln!("{r:?}");
    assert!(
        r.package_dlls > 0
            && r.framework_dlls > 0
            && r.sibling_dlls > 0
            && r.tally.moved(Why::Delete) > 0
            && r.tally
                .stale
                .get(&Why::CreateAbsent)
                .is_some_and(|n| *n > 0)
            && r.tally.moved(Why::Extra) > 0
            && r.tally.moved(Why::Relink) > 0
            && r.layouts.len() == LAYOUTS.len(),
        "{r:?}"
    );
}

/// The env carries its resolution's read set, and with it each DLL's stamp:
/// rewriting a DLL the env folded fails validation, whether the env read the
/// DLL or took its projection from the assembly cache. The pack's
/// `System.Runtime.dll` is a real assembly, so the cache holds its
/// projection after the first build and the second build is a hit. A
/// stamp taken within the racy window of the DLL's last change holds only
/// while the DLL holds the bytes the env read: a same-size rewrite fails it.
#[test]
fn the_env_records_each_dll_stamp_with_or_without_the_cache() {
    let world = World {
        packages: vec![Folder::Primary],
        pack_versions: vec![(1, true)],
        siblings: vec![Sibling {
            built: vec![TFM],
            in_assets: true,
            names_output: true,
            multi: false,
            bin_linked: false,
            dangling_output: false,
        }],
        layout: Layout::Plain,
        absolute_links: false,
    };
    let system_runtime = host_fs::read(crate::common::ensure_system_runtime_dll()).unwrap();
    for cached in [false, true] {
        let tmp = TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        let entry = lay_down(&root, &world).entry;
        let dotnet = root.join("dotnet");
        let pack_dll = dotnet.join(format!(
            "packs/Microsoft.NETCore.App.Ref/1.0.0/ref/{TFM}/System.Runtime.dll"
        ));
        std::fs::write(&pack_dll, &system_runtime).unwrap();
        let cache_dir = root.join("cache");
        let run = || {
            let mut ws = workspace(&root);
            let tfm = ws.served_tfm_for_project(&entry);
            let mut semantic = SemanticState::new();
            if cached {
                semantic.set_assembly_cache(AssemblyCache::at(cache_dir.clone()));
            }
            let (dlls, _) =
                semantic.reference_resolution_for_project(&entry, Some(&dotnet), &tfm, &ws);
            let (reads, _) = semantic.env_reads_for_project(&entry, Some(&dotnet), &tfm, &ws);
            (dlls, reads)
        };
        // Built straight after the fixture was written, every DLL's stamp is
        // racy: it carries a digest of the bytes read, and holds while they
        // stand, and no longer.
        let (_, racy) = run();
        let racy_stamps = racy
            .reads
            .reads()
            .iter()
            .filter(|read| read.observation.is_racy_stamp())
            .count();
        assert!(racy_stamps > 0, "precondition: the DLLs' stamps are racy");
        assert!(
            racy.reads
                .reads()
                .iter()
                .all(|read| match &read.observation {
                    Observation::Stamp(Ok(stamp)) if stamp.racy => stamp.digest.is_some(),
                    _ => true,
                }),
            "a racy DLL stamp carries no digest of what was read (cached: {cached})"
        );
        assert_eq!(racy.reads.first_stale(), None, "cached: {cached}");
        let racy_pack = host_fs::read(&pack_dll).unwrap();
        let mut same_size = racy_pack.clone();
        same_size[0] ^= 0xff;
        std::fs::write(&pack_dll, &same_size).unwrap();
        assert!(
            racy.reads
                .first_stale()
                .is_some_and(|read| read.path == pack_dll),
            "a same-size rewrite within the racy window left the read set standing (cached: {cached})"
        );
        std::fs::write(&pack_dll, &racy_pack).unwrap();
        std::thread::sleep(
            borzoi_msbuild::observed::STAMP_RACY_WINDOW + std::time::Duration::from_millis(200),
        );
        let (dlls, reads) = if cached {
            run();
            assert!(
                host_fs::read_dir(&cache_dir).unwrap().count() > 0,
                "precondition: the first build cached a projection"
            );
            run()
        } else {
            run()
        };
        assert_eq!(dlls.len(), 3, "{dlls:?}");
        assert!(dlls.contains(&pack_dll), "{dlls:?}");
        for dll in &dlls {
            assert!(
                reads.reads.reads().iter().any(|read| read.path == *dll
                    && matches!(read.observation, Observation::Stamp(Ok(_)))),
                "no stamp of {dll:?} (cached: {cached})"
            );
        }
        assert_eq!(reads.reads.first_stale(), None);
        if cached {
            // The same bytes written again with their modification time put
            // back (as an extraction that keeps an archive's times does):
            // the cache keys on size and modification time, so it holds a
            // projection for them, but the change time is new and the stamp
            // racy. A projection served under a racy stamp could never be
            // confirmed again, so the DLL is read, and its stamp carries a
            // digest.
            let mtime = host_fs::metadata(&pack_dll).unwrap().modified().unwrap();
            std::fs::write(&pack_dll, &system_runtime).unwrap();
            host_fs::set_modified(&pack_dll, mtime).unwrap();
            let (_, again) = run();
            let pack_stamp = again
                .reads
                .reads()
                .iter()
                .find_map(|read| match &read.observation {
                    Observation::Stamp(Ok(stamp)) if read.path == pack_dll => Some(*stamp),
                    _ => None,
                })
                .expect("the env stamps the pack's DLL");
            assert!(
                pack_stamp.racy,
                "precondition: the rewrite left a racy stamp"
            );
            assert!(
                pack_stamp.digest.is_some(),
                "a racy DLL stamp a cache hit rests on carries no digest"
            );
        }
        std::fs::write(&pack_dll, b"a rewritten dll").unwrap();
        assert!(
            reads.reads.first_stale().is_some(),
            "a rewritten DLL left the env's read set standing (cached: {cached})"
        );
    }
}

/// For every layout that reaches the entry through a symlink, retargeting
/// the link to an identical copy of what it led to, one directory deeper,
/// fails validation: the assets file reads the same under the spelling the
/// resolution read it by, so only the canonicalisation of its path sees the
/// move. Seeing it matters because the project paths the assets file records
/// are resolved from that canonical path. A sibling recorded in the assets
/// file, built and named only there, makes the move change the answer too.
#[test]
fn a_link_retargeted_to_an_identical_copy_fails_validation() {
    for layout in LAYOUTS.into_iter().filter(|l| *l != Layout::Plain) {
        for absolute_links in [false, true] {
            let world = World {
                packages: vec![Folder::Primary],
                pack_versions: vec![(1, true)],
                siblings: vec![Sibling {
                    built: vec![TFM],
                    in_assets: true,
                    names_output: false,
                    multi: false,
                    bin_linked: false,
                    dangling_output: false,
                }],
                layout,
                absolute_links,
            };
            let tmp = TempDir::new().unwrap();
            let root = host_fs::canonicalize(tmp.path()).unwrap();
            let laid = lay_down(&root, &world);
            let dotnet = root.join("dotnet");
            let mut ws = workspace(&root);
            let tfm = ws.served_tfm_for_project(&laid.entry);
            let mut semantic = SemanticState::new();
            let (_, reads) =
                semantic.reference_resolution_for_project(&laid.entry, Some(&dotnet), &tfm, &ws);
            assert_eq!(reads.reads.first_stale(), None, "{layout:?}");
            let [_, Edit::Link(link, identical)] = &laid.retargets[..] else {
                panic!("{layout:?} has no retarget to an identical copy");
            };
            std::fs::remove_file(link).unwrap();
            std::os::unix::fs::symlink(identical, link).unwrap();
            assert!(
                reads.reads.first_stale().is_some(),
                "{layout:?} (absolute: {absolute_links}): the entry's link retargeted to an \
                 identical copy left the read set standing"
            );
        }
    }
}
