//! The read-set soundness oracle ([`crate::observed::soundness`]) over
//! generated worlds that reach every kind of query an evaluation makes:
//! SDK resolution against a dotnet root (its version listing and `Sdk.props`
//! probes), the `Directory.Build.*` walk, `Exists()` conditions, a
//! conditional and a wildcard `<Import>`, `GetDirectoryNameOfFileAbove`, a
//! Compile glob, and the `@(ProjectReference->Exists())` item function.
//!
//! Every helper in [`super`] runs the same sweep over its test's tree; this
//! module adds the worlds those trees never build, and the non-vacuity
//! check that the perturbations of each rule moved some evaluation.

use proptest::prelude::*;
use proptest::strategy::ValueTree as _;
use tempfile::TempDir;

use super::*;
use crate::observed::soundness::{Edit, Perturbation, Tally, Why, sweep};
use crate::observed::{Observation, Observer, ReadSet, TextDigest};
use crate::{resolve_sdk, workloads};

/// Which optional parts of the world exist.
#[derive(Clone, Debug)]
struct World {
    /// The SDK versions installed under `dotnet/sdk`.
    sdk_versions: Vec<&'static str>,
    /// Whether the project names the SDK.
    uses_sdk: bool,
    repo_props: bool,
    src_props: bool,
    src_targets: bool,
    shared_props: bool,
    /// Files under `src/imports`, which the wildcard import takes.
    imports: Vec<&'static str>,
    marker_in_repo: bool,
    marker_in_app: bool,
    /// Source files beside the project and below it.
    sources: Vec<&'static str>,
    lib_project: bool,
}

fn world() -> impl Strategy<Value = World> {
    (
        proptest::sample::subsequence(vec!["8.0.100", "9.0.200", "10.0.100"], 0..=3),
        any::<bool>(),
        any::<(bool, bool, bool, bool)>(),
        proptest::sample::subsequence(vec!["a.props", "b.props"], 0..=2),
        any::<(bool, bool)>(),
        proptest::sample::subsequence(vec!["A.fs", "sub/C.fs", "sub/deep/D.fs"], 0..=3),
        any::<bool>(),
    )
        .prop_map(
            |(
                sdk_versions,
                uses_sdk,
                (repo_props, src_props, src_targets, shared_props),
                imports,
                (marker_in_repo, marker_in_app),
                sources,
                lib_project,
            )| World {
                sdk_versions,
                uses_sdk,
                repo_props,
                src_props,
                src_targets,
                shared_props,
                imports,
                marker_in_repo,
                marker_in_app,
                sources,
                lib_project,
            },
        )
}

/// An MSBuild file that writes `name` = `value`.
fn writes(name: &str, value: &str) -> String {
    format!("<Project><PropertyGroup><{name}>{value}</{name}></PropertyGroup></Project>\n")
}

fn sdk_files(root: &Path, version: &str) -> Vec<(PathBuf, String)> {
    let sdk = root.join(format!("dotnet/sdk/{version}/Sdks/Fake.Sdk/Sdk"));
    vec![
        // The `dotnet.dll` the .NET host requires before it counts the version
        // (`crate::test_support::install_host_sdk_dir`).
        (
            root.join(format!("dotnet/sdk/{version}/dotnet.dll")),
            String::new(),
        ),
        (
            sdk.join("Sdk.props"),
            format!(
                "<Project><PropertyGroup><SdkSeen>{version}</SdkSeen></PropertyGroup>\
                 <Import Project=\"$(MSBuildThisFileDirectory)extra.props\" \
                 Condition=\"Exists('$(MSBuildThisFileDirectory)extra.props')\" /></Project>\n"
            ),
        ),
        (sdk.join("Sdk.targets"), writes("SdkTargets", version)),
    ]
}

const PROJECT: &str = r#"<Project{SDK}>
  <PropertyGroup>
    <MarkerDir>$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), marker.txt))</MarkerDir>
  </PropertyGroup>
  <Import Project="../shared.props" Condition="Exists('../shared.props')" />
  <Import Project="../imports/*.props" />
  <ItemGroup>
    <Compile Include="A.fs" Condition="Exists('A.fs')" />
    <Compile Include="sub/**/*.fs" />
    <ProjectReference Include="../Lib/Lib.fsproj;../Missing/Missing.fsproj" />
    <ProjectReferenceNonExistent Include="@(ProjectReference)" Exclude="@(ProjectReference->Exists())" />
    <ProjectReference Remove="@(ProjectReferenceNonExistent)" />
  </ItemGroup>
</Project>
"#;

/// Materialise `world` under `root`; returns the project's path and source.
fn build(root: &Path, world: &World) -> (PathBuf, String) {
    for version in &world.sdk_versions {
        for (path, text) in sdk_files(root, version) {
            write_at(
                root,
                path.strip_prefix(root).unwrap().to_str().unwrap(),
                &text,
            );
        }
    }
    let repo = root.join("repo");
    let optional = [
        (
            world.repo_props,
            "Directory.Build.props",
            writes("RepoProp", "1"),
        ),
        (
            world.src_props,
            "src/Directory.Build.props",
            writes("SrcProp", "1"),
        ),
        (
            world.src_targets,
            "src/Directory.Build.targets",
            writes("SrcTargets", "1"),
        ),
        (
            world.shared_props,
            "src/shared.props",
            writes("Shared", "1"),
        ),
        (world.marker_in_repo, "marker.txt", String::new()),
        (world.marker_in_app, "src/App/marker.txt", String::new()),
        (
            world.lib_project,
            "src/Lib/Lib.fsproj",
            "<Project />".to_string(),
        ),
    ];
    for (present, name, text) in optional {
        if present {
            write_at(&repo, name, &text);
        }
    }
    for name in &world.imports {
        write_at(
            &repo,
            &format!("src/imports/{name}"),
            &writes("Imported", name),
        );
    }
    for name in &world.sources {
        write_at(&repo, &format!("src/App/{name}"), "module M\n");
    }
    let source = PROJECT.replace(
        "{SDK}",
        if world.uses_sdk {
            " Sdk=\"Fake.Sdk\""
        } else {
            ""
        },
    );
    let project = write_at(&repo, "src/App/App.fsproj", &source);
    (canon(&project), source)
}

/// The world's own perturbations: a newer SDK installed, and an `extra.props`
/// beside every installed SDK's `Sdk.props`.
fn extras(root: &Path, world: &World) -> Vec<Perturbation> {
    let mut out = vec![Perturbation {
        why: Why::Extra,
        edits: sdk_files(root, "11.0.100")
            .into_iter()
            .map(|(path, text)| Edit::Write(path, text.into_bytes()))
            .collect(),
    }];
    for version in &world.sdk_versions {
        out.push(Perturbation {
            why: Why::Extra,
            edits: vec![Edit::Write(
                root.join(format!(
                    "dotnet/sdk/{version}/Sdks/Fake.Sdk/Sdk/extra.props"
                )),
                writes("Extra", version).into_bytes(),
            )],
        });
    }
    out
}

fn evaluate(root: &Path, project: &Path, source: &str, through: Through<'_>) -> ParsedProject {
    let dotnet = root.join("dotnet");
    let resolver = |name: &str, observer: &Observer| {
        resolve_sdk(
            &dotnet,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: None,
                overrides_present: false,
                global_json_pins_workload_set: false,
            },
            observer,
        )
    };
    let glob: &GlobResolver<'_> = &crate::glob_resolver::resolve;
    through
        .evaluate(
            source,
            project,
            &HashMap::new(),
            &HashMap::new(),
            Some(&resolver),
            Some(glob),
        )
        .expect("well-formed XML parses")
}

/// The sweep over `world`, with the reused entry point held to the reference
/// at every step, as every helper's is ([`super::sound`]).
fn sweep_world(world: &World) -> Tally {
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let (project, source) = build(&root, world);
    let documents = RefCell::new(ImportDocuments::default());
    let read_a_file = std::cell::Cell::new(false);
    let fifo = Fifo::new();
    let mut extra = extras(&root, world);
    if let Some(fifo) = &fifo {
        extra.extend(crate::observed::soundness::fifo_perturbations(
            &root, &fifo.path,
        ));
    }
    let tally = sweep(
        &root,
        &|| {
            let reused = same_as_reference(
                evaluate(&root, &project, &source, Through::Reference),
                evaluate(&root, &project, &source, Through::Reusing(&documents)),
            );
            // The world holds no workload manifests, so every file an
            // evaluation reads whole is an MSBuild file it reads through
            // `read_document`, and every one is well-formed: each is kept,
            // parsed from the bytes its read records.
            let documents = documents.borrow();
            for read in reused.read_set.reads() {
                if let Observation::Text(Ok(digest)) = &read.observation {
                    read_a_file.set(true);
                    assert_eq!(
                        documents.kept_digest(&read.path),
                        Some(*digest),
                        "{} is not kept as it was read",
                        read.path.display()
                    );
                }
            }
            reused
        },
        &extra,
    );
    // The sweep evaluates the world many times over a tree it changes one
    // file at a time, so once any evaluation reads a file the comparison is
    // vacuous unless some later one reused its document.
    let documents = documents.into_inner();
    if read_a_file.get() {
        assert!(
            documents.reused() > 0,
            "the sweep's evaluations reused no document: {documents:?}"
        );
    }
    tally
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 16,
        .. ProptestConfig::default()
    })]

    /// Sound, and (the world spelling each file one way) precise.
    #[test]
    fn an_evaluation_whose_read_set_stands_is_unchanged(world in world()) {
        let tally = sweep_world(&world);
        prop_assert_eq!(tally.imprecise, 0, "{:#?}", tally);
    }
}

/// Every rule of the sweep moves some evaluation over a fixed sample of
/// worlds, so none of them is vacuous: a rewrite, a same-size rewrite and a
/// delete of an imported file, a created file where the read set recorded an
/// absence, a new entry in a listed directory, a newly installed SDK, and an
/// imported file made a link to a FIFO.
#[test]
fn every_perturbation_rule_moves_some_evaluation() {
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let mut total = Tally::default();
    for _ in 0..8 {
        let world = world().new_tree(&mut runner).unwrap().current();
        total.absorb(&sweep_world(&world));
    }
    for why in [
        Why::Rewrite,
        Why::RewriteSameSize,
        Why::Delete,
        Why::CreateAbsent,
        Why::GrowListing,
        Why::Extra,
        #[cfg(unix)]
        Why::Fifo,
    ] {
        assert!(
            total.moved(why) > 0,
            "no {why:?} moved an evaluation: {total:#?}"
        );
    }
    assert!(
        total.untouched > 0,
        "no perturbation left the read set untouched, so precision was never checked: {total:#?}"
    );
    assert_eq!(
        total.imprecise, 0,
        "a change the read set does not name moved one of its answers: {total:#?}"
    );
}

/// The read set of a world with everything in it holds a query of every
/// kind, absences included.
#[test]
fn a_full_world_records_every_kind_of_query() {
    let world = World {
        sdk_versions: vec!["9.0.200", "10.0.100"],
        uses_sdk: true,
        repo_props: true,
        src_props: true,
        src_targets: true,
        shared_props: false,
        imports: vec!["a.props"],
        marker_in_repo: true,
        marker_in_app: false,
        sources: vec!["A.fs", "sub/C.fs"],
        lib_project: true,
    };
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let (project, source) = build(&root, &world);
    let parsed = evaluate(
        &root,
        &project,
        &source,
        Through::Reusing(&RefCell::default()),
    );
    // The world's SDK must resolve, or its reads are not in the set.
    assert!(
        !parsed.diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::SdkNotFound { .. }
                | DiagnosticKind::SdkVersionNotSatisfied { .. }
                | DiagnosticKind::SdkResolutionUnsupported { .. }
        )),
        "the world's SDK did not resolve: {:#?}",
        parsed.diagnostics
    );
    let read_set: &ReadSet = &parsed.read_set;
    let has =
        |pred: &dyn Fn(&Observation) -> bool| read_set.reads().iter().any(|r| pred(&r.observation));
    assert!(has(&|o| matches!(o, Observation::Text(Ok(_)))));
    assert!(has(&|o| matches!(o, Observation::Kind(Ok(_)))));
    assert!(has(
        &|o| matches!(o, Observation::Kind(Err(f)) if f.is_absent())
    ));
    assert!(has(&|o| matches!(o, Observation::LinkKind(_))));
    assert!(has(&|o| matches!(o, Observation::Listing(Ok(_)))));
    assert!(has(&|o| matches!(o, Observation::Canonical(Ok(_)))));
    let counts = parsed.read_counts;
    assert!(
        counts.opens > 0 && counts.stats > 0 && counts.listings > 0 && counts.canonicalizations > 0
    );
    assert!(
        read_set.len() as u64
            <= counts.opens + counts.stats + counts.listings + counts.canonicalizations,
        "the read set holds distinct queries, never more than were made"
    );
}

/// An evaluation that reads one file as text and as XML reads it once: the
/// workload locator reads the SDK's `KnownWorkloadManifests.txt` as text, and
/// a project that imports the same file reads it as XML, before the locator or
/// after it. [`super::sound`] holds each to the reference, which asks every
/// time, and to one query per read; the known list is empty (no XML) or an
/// empty `<Project />` (no manifest id).
#[test]
fn a_file_read_as_text_and_as_xml_is_read_once() {
    const LOCATOR: &str = r#"<Import Project="WorkloadManifest.targets" Sdk="Microsoft.NET.SDK.WorkloadManifestTargetsLocator" />"#;
    for known in ["", "<Project />"] {
        for locator_first in [true, false] {
            let tmp = TempDir::new().unwrap();
            let root = canon(tmp.path());
            let dotnet = root.join("dotnet");
            let list = write_at(&dotnet, "sdk/10.0.100/KnownWorkloadManifests.txt", known);
            crate::test_support::install_host_sdk_dir(&dotnet.join("sdk/10.0.100"));
            let import = format!(r#"<Import Project="{}" />"#, list.display());
            let (first, second) = if locator_first {
                (LOCATOR, import.as_str())
            } else {
                (import.as_str(), LOCATOR)
            };
            let source = format!("<Project>\n  {first}\n  {second}\n</Project>\n");
            let project = canon(&write_at(&root, "proj/Demo.fsproj", &source));
            let resolver = |name: &str, observer: &Observer| {
                resolve_sdk(
                    &dotnet,
                    None,
                    name,
                    None,
                    None,
                    &workloads::WorkloadEnvironment {
                        user_dotnet_root: None,
                        overrides_present: false,
                        global_json_pins_workload_set: false,
                    },
                    observer,
                )
            };
            let parsed = sound(&project, |through| {
                through
                    .evaluate(
                        &source,
                        &project,
                        &HashMap::new(),
                        &HashMap::new(),
                        Some(&resolver),
                        None,
                    )
                    .expect("well-formed XML parses")
            });
            let case = format!("known list {known:?}, locator first: {locator_first}");
            // The locator must find its host SDK, or the text read this test
            // is about never happens. (It may decline after the read: a known
            // list of `<Project />` names an id it does not certify.)
            assert!(
                !parsed.diagnostics.iter().any(|d| matches!(
                    d.kind,
                    DiagnosticKind::SdkNotFound { .. }
                        | DiagnosticKind::SdkVersionNotSatisfied { .. }
                )),
                "{case}: the locator found no host SDK: {:#?}",
                parsed.diagnostics
            );
            let texts_of_list: Vec<_> = parsed
                .read_set
                .reads()
                .iter()
                .filter(|read| {
                    read.path == list && matches!(read.observation, Observation::Text(_))
                })
                .collect();
            assert!(
                matches!(
                    texts_of_list[..],
                    [read] if read.observation == Observation::Text(Ok(TextDigest::of(known)))
                ),
                "{case}: {texts_of_list:#?}"
            );
            let malformed = parsed.diagnostics.iter().any(|d| {
                matches!(
                    &d.kind,
                    DiagnosticKind::ImportFailed {
                        reason: ImportFailReason::MalformedXml { .. },
                        ..
                    }
                )
            });
            assert_eq!(
                malformed,
                known.is_empty(),
                "{case}: {:#?}",
                parsed.diagnostics
            );
        }
    }
}

/// A project behind `Exists('alias')`, where `alias` is a symlink to
/// `target`; `target_exists` decides whether the link dangles. The sweep must
/// accept both: deleting or creating `target` moves the answer about `alias`,
/// which the precision check has to see as touching it, and a dangling link
/// is not an absent path to create a file at. Deleting the link, dangling
/// it, or creating a dangling link's target moves the answer too, and must
/// leave a read stale.
#[cfg(unix)]
fn sweep_symlinked_exists(target_exists: bool) {
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    if target_exists {
        write_at(&root, "proj/target", "x");
    }
    std::os::unix::fs::symlink(root.join("proj/target"), {
        std::fs::create_dir_all(root.join("proj")).unwrap();
        root.join("proj/alias")
    })
    .unwrap();
    let source = r#"<Project>
  <PropertyGroup Condition="Exists('alias')"><Linked>yes</Linked></PropertyGroup>
</Project>"#;
    let project = write_at(&root, "proj/Demo.fsproj", source);
    let evaluate = || {
        parse_fsproj_with_imports(
            source,
            &project,
            &HashMap::new(),
            &HashMap::new(),
            None,
            None,
        )
        .expect("well-formed XML parses")
    };
    let tally = sweep(&root, &evaluate, &[]);
    assert!(tally.moved(Why::Relink) > 0, "{tally:?}");
}

#[cfg(unix)]
#[test]
fn a_symlink_whose_target_moves_is_swept() {
    sweep_symlinked_exists(true);
}

#[cfg(unix)]
#[test]
fn a_dangling_symlink_is_swept() {
    sweep_symlinked_exists(false);
}

/// The directories a generated link tree holds, each with a file `f` whose
/// text is the directory's name.
#[cfg(unix)]
const LINK_TREE_DIRS: [&str; 4] = ["", "a", "b", "a/sub"];

/// What a generated link's target names, before it is spelt.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
enum LinkTarget {
    /// A directory's file `f`.
    File(usize),
    /// A directory.
    Dir(usize),
    /// Another generated link (or the link itself).
    Link(usize),
    /// A missing name in a directory that exists.
    Missing(usize),
    /// A missing name in a directory that does not exist.
    MissingParent,
    /// `hop/../f`, through the tree's `hop` link (to `a/sub`): the file
    /// system takes the `..` from `a/sub`, naming `a/f`, where a lexical
    /// reading names the root's `f`.
    Through,
}

#[cfg(unix)]
#[derive(Clone, Debug)]
struct LinkSpec {
    /// The directory the link lies in.
    dir: usize,
    target: LinkTarget,
    /// Whether the target is spelt absolute, rather than relative to the
    /// link's directory.
    absolute: bool,
}

#[cfg(unix)]
fn link_spec(links: usize) -> impl Strategy<Value = LinkSpec> {
    let dirs = LINK_TREE_DIRS.len();
    let target = prop_oneof![
        (0..dirs).prop_map(LinkTarget::File),
        (0..dirs).prop_map(LinkTarget::Dir),
        (0..links).prop_map(LinkTarget::Link),
        (0..dirs).prop_map(LinkTarget::Missing),
        Just(LinkTarget::MissingParent),
        Just(LinkTarget::Through),
    ];
    (0..dirs, target, any::<bool>()).prop_map(|(dir, target, absolute)| LinkSpec {
        dir,
        target,
        absolute,
    })
}

#[cfg(unix)]
fn link_tree() -> impl Strategy<Value = Vec<LinkSpec>> {
    (1usize..=5).prop_flat_map(|n| prop::collection::vec(link_spec(n), n))
}

/// Lay the tree down under `root`; every link's path, `hop` first.
#[cfg(unix)]
fn lay_link_tree(root: &Path, specs: &[LinkSpec]) -> Vec<PathBuf> {
    for dir in LINK_TREE_DIRS {
        write_at(
            &root.join(dir),
            "f",
            if dir.is_empty() { "root" } else { dir },
        );
    }
    std::os::unix::fs::symlink("a/sub", root.join("hop")).unwrap();
    let path_of = |i: usize| {
        root.join(LINK_TREE_DIRS[specs[i].dir])
            .join(format!("l{i}"))
    };
    // A relative spelling descends from the link's directory where the
    // target lies below it (so links in two directories can spell different
    // targets alike), and otherwise climbs to the root (no directory on the
    // way is a link) and descends from there.
    let spell = |spec: &LinkSpec, from_root: &str| {
        let below = LINK_TREE_DIRS[spec.dir];
        if spec.absolute {
            root.join(from_root)
        } else if below.is_empty() {
            // An empty target is no path (Linux refuses it): the root is `.`.
            PathBuf::from(if from_root.is_empty() { "." } else { from_root })
        } else if let Some(local) = from_root.strip_prefix(&format!("{below}/")) {
            PathBuf::from(local)
        } else {
            let up = LINK_TREE_DIRS[spec.dir]
                .split('/')
                .filter(|part| !part.is_empty())
                .map(|_| "..")
                .collect::<Vec<_>>()
                .join("/");
            PathBuf::from(if up.is_empty() { "." } else { &up }).join(from_root)
        }
    };
    let mut links = vec![root.join("hop")];
    for (i, spec) in specs.iter().enumerate() {
        let dir = |d: usize| LINK_TREE_DIRS[d].to_string();
        let from_root = match spec.target {
            LinkTarget::File(d) => Path::new(&dir(d)).join("f"),
            LinkTarget::Dir(d) => PathBuf::from(dir(d)),
            LinkTarget::Link(j) => Path::new(LINK_TREE_DIRS[specs[j].dir]).join(format!("l{j}")),
            LinkTarget::Missing(d) => Path::new(&dir(d)).join("missing"),
            LinkTarget::MissingParent => PathBuf::from("nodir/sub/missing"),
            LinkTarget::Through => PathBuf::from("hop/../f"),
        };
        let from_root = from_root
            .to_str()
            .unwrap()
            .trim_start_matches('/')
            .to_string();
        std::os::unix::fs::symlink(spell(spec, &from_root), path_of(i)).unwrap();
        links.push(path_of(i));
    }
    links
}

/// Every entry under `root`, with its kind and its text or target.
#[cfg(unix)]
fn link_tree_snapshot(root: &Path) -> Vec<(PathBuf, String)> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in host_fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            let meta = host_fs::symlink_metadata(&path).unwrap();
            let what = if meta.file_type().is_symlink() {
                format!("link {:?}", host_fs::read_link(&path).unwrap())
            } else if meta.is_dir() {
                stack.push(path.clone());
                "dir".to_string()
            } else {
                format!("file {:?}", host_fs::read_to_string(&path).ok())
            };
            out.push((path, what));
        }
    }
    out.sort();
    out
}

/// The sweep's symlink perturbations, held to the file system's own
/// resolution over a generated link tree, with no path resolution in the
/// check. For every link: some perturbation deletes it; some dangles it; for
/// every other link that names something, some perturbation makes it name
/// the same thing (`canonicalize` agreeing); and where the link dangles and
/// writing through it would make a file under the root, some perturbation
/// makes it name that very file. Every perturbation is undone exactly.
#[cfg(unix)]
fn check_link_perturbations(specs: &[LinkSpec]) -> Result<(), String> {
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let links = lay_link_tree(&root, specs);
    let before = link_tree_snapshot(&root);
    let planned = crate::observed::soundness::perturbations(&root, &ReadSet::default());
    let edits: Vec<&Edit> = planned
        .iter()
        .filter(|p| p.why == Why::Relink)
        .flat_map(|p| &p.edits)
        .collect();
    let some_edit = |pred: &dyn Fn() -> bool| {
        edits.iter().any(|edit| {
            let held = crate::observed::soundness::with_edits(std::slice::from_ref(*edit), pred);
            assert_eq!(link_tree_snapshot(&root), before, "{edit:?} was not undone");
            held == Some(true)
        })
    };
    for link in &links {
        let is_link = || host_fs::symlink_metadata(link).is_ok_and(|m| m.file_type().is_symlink());
        if !some_edit(&|| host_fs::symlink_metadata(link).is_err()) {
            return Err(format!("{link:?} is never deleted"));
        }
        if !some_edit(&|| is_link() && host_fs::metadata(link).is_err()) {
            return Err(format!("{link:?} is never dangled"));
        }
        for other in links.iter().filter(|other| *other != link) {
            let Ok(names) = host_fs::canonicalize(other) else {
                continue;
            };
            if !some_edit(&|| host_fs::canonicalize(link).ok().as_ref() == Some(&names)) {
                return Err(format!(
                    "{link:?} is never made to name {names:?}, which {other:?} names"
                ));
            }
        }
        if host_fs::metadata(link).is_err() {
            // The reference: what writing through the link makes, if anything.
            let made = std::fs::write(link, "x")
                .is_ok()
                .then(|| host_fs::canonicalize(link).unwrap());
            if let Some(made) = &made {
                std::fs::remove_file(made).unwrap();
            }
            assert_eq!(link_tree_snapshot(&root), before);
            if let Some(made) = made.filter(|made| made.starts_with(&root))
                && !some_edit(&|| host_fs::canonicalize(link).ok().as_ref() == Some(&made))
            {
                return Err(format!(
                    "{link:?} dangles, and {made:?}, its target, is never made"
                ));
            }
        }
    }
    Ok(())
}

#[cfg(unix)]
proptest! {
    #![proptest_config(ProptestConfig { cases: 128, ..ProptestConfig::default() })]

    #[test]
    fn the_sweep_perturbs_every_link_as_the_file_system_resolves_it(specs in link_tree()) {
        check_link_perturbations(&specs).map_err(TestCaseError::fail)?;
    }
}

/// The trees the planner's earlier versions got wrong, pinned: two links in
/// different directories whose relative targets are spelt alike; a target
/// through a link (`hop/..`); and a dangling link whose target's directory
/// does not exist. And a link in the root to the root, whose relative target
/// is spelt `.`, an empty target being no path.
#[cfg(unix)]
#[test]
fn the_sweep_perturbs_the_pinned_link_trees() {
    let spec = |dir, target, absolute| LinkSpec {
        dir,
        target,
        absolute,
    };
    for specs in [
        vec![
            spec(1, LinkTarget::File(1), false),
            spec(2, LinkTarget::File(2), false),
        ],
        vec![
            spec(0, LinkTarget::Through, false),
            spec(2, LinkTarget::File(2), false),
        ],
        vec![spec(1, LinkTarget::MissingParent, false)],
        vec![spec(0, LinkTarget::Dir(0), false)],
    ] {
        if let Err(why) = check_link_perturbations(&specs) {
            panic!("{specs:?}: {why}");
        }
    }
}

/// A query that climbs out of the swept root (`Exists('../outside/…')`) is
/// recorded, but the sweep plans no change outside its root.
#[test]
fn the_sweep_writes_only_under_its_root() {
    let tmp = TempDir::new().unwrap();
    let base = canon(tmp.path());
    let root = base.join("root");
    let source = r#"<Project>
  <PropertyGroup Condition="Exists('../outside/marker.props')"><Out>yes</Out></PropertyGroup>
</Project>"#;
    let project = write_at(&root, "Demo.fsproj", source);
    let evaluate = || {
        parse_fsproj_with_imports(
            source,
            &project,
            &HashMap::new(),
            &HashMap::new(),
            None,
            None,
        )
        .expect("well-formed XML parses")
    };
    assert!(
        evaluate()
            .read_set
            .reads()
            .iter()
            .any(|read| read.path.ends_with("outside/marker.props"))
    );
    let planned = crate::observed::soundness::perturbations(&root, &evaluate().read_set);
    for perturbation in &planned {
        for edit in &perturbation.edits {
            let path = edit.path();
            let lexical: PathBuf = path.components().fold(PathBuf::new(), |mut out, c| {
                match c {
                    std::path::Component::ParentDir => {
                        out.pop();
                    }
                    std::path::Component::CurDir => {}
                    other => out.push(other),
                }
                out
            });
            assert!(
                lexical.starts_with(&root),
                "{perturbation:?} leaves the root"
            );
        }
    }
    sweep(&root, &evaluate, &[]);
}

/// An unreadable import is left alone, and a read-only one is put back with
/// its permissions.
#[cfg(unix)]
#[test]
fn the_sweep_keeps_permissions() {
    use std::os::unix::fs::PermissionsExt as _;
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let unreadable = write_at(&root, "proj/unreadable.props", &writes("U", "1"));
    let read_only = write_at(&root, "proj/read_only.props", &writes("R", "1"));
    let mode = |path: &Path| {
        crate::observed::host_fs::metadata(path)
            .unwrap()
            .permissions()
            .mode()
            & 0o777
    };
    std::fs::set_permissions(&unreadable, std::fs::Permissions::from_mode(0o000)).unwrap();
    std::fs::set_permissions(&read_only, std::fs::Permissions::from_mode(0o444)).unwrap();
    let source = r#"<Project>
  <Import Project="unreadable.props" />
  <Import Project="read_only.props" />
</Project>"#;
    let project = write_at(&root, "proj/Demo.fsproj", source);
    let evaluate = || {
        parse_fsproj_with_imports(
            source,
            &project,
            &HashMap::new(),
            &HashMap::new(),
            None,
            None,
        )
        .expect("well-formed XML parses")
    };
    sweep(&root, &evaluate, &[]);
    assert_eq!(mode(&unreadable), 0o000);
    assert_eq!(mode(&read_only), 0o444);
    std::fs::set_permissions(&unreadable, std::fs::Permissions::from_mode(0o644)).unwrap();
}
