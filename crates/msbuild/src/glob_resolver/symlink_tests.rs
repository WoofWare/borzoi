//! The walk's handling of symbolic links to directories, held to an
//! executable model of MSBuild's rule.
//!
//! `FileMatcher.GetFilesRecursive` (MSBuild 18.9) returns at once from a
//! directory that is a symbolic link whose final target contains it:
//!
//! ```csharp
//! FileSystemInfo linkTarget = Directory.ResolveLinkTarget(recursionState.BaseDirectory, returnFinalTarget: true);
//! if (linkTarget is not null && IsSubdirectoryOf(recursionState.BaseDirectory, linkTarget.FullName, FileUtilities.PathComparison))
//!     return;
//! ```
//!
//! The comparison is `Ordinal` or `OrdinalIgnoreCase` by whether the build's
//! temp directory is case-sensitive, so [`msbuild_walk`] runs the rule under
//! each, and wherever the resolver commits, both must give its list.

use super::*;
use crate::observed::host_fs;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::symlink;
use tempfile::TempDir;

/// How `FileUtilities.PathComparison` compares, by the temp directory's case
/// sensitivity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Comparison {
    Ordinal,
    OrdinalIgnoreCase,
}

/// `OrdinalIgnoreCase`'s view of one UTF-16 unit: its simple upper-case
/// mapping where that is one unit of the Basic Multilingual Plane, else
/// itself.
fn fold_unit(unit: u16) -> u16 {
    let Some(c) = char::from_u32(u32::from(unit)) else {
        return unit;
    };
    let mut upper = c.to_uppercase();
    match (upper.next(), upper.next()) {
        (Some(u), None) if (u as u32) <= 0xFFFF => u as u32 as u16,
        _ => unit,
    }
}

/// MSBuild's `FileMatcher.IsSubdirectoryOf(child, parent, comparison)`, or
/// `None` where it throws (`child` equal in length to a matching `parent`
/// indexes past its end).
fn is_subdirectory_of(child: &str, parent: &str, comparison: Comparison) -> Option<bool> {
    if parent.is_empty() {
        return Some(true);
    }
    let child: Vec<u16> = child.encode_utf16().collect();
    let parent: Vec<u16> = parent.encode_utf16().collect();
    if child.len() < parent.len() {
        return Some(false);
    }
    let head = &child[..parent.len()];
    let prefix = match comparison {
        Comparison::Ordinal => head == parent.as_slice(),
        Comparison::OrdinalIgnoreCase => head
            .iter()
            .zip(&parent)
            .all(|(a, b)| fold_unit(*a) == fold_unit(*b)),
    };
    if !prefix {
        return Some(false);
    }
    // `FileUtilities.Slashes`.
    let separator = |unit: u16| unit == u16::from(b'/') || unit == u16::from(b'\\');
    if separator(parent[parent.len() - 1]) {
        return Some(true);
    }
    child.get(parent.len()).map(|unit| separator(*unit))
}

/// `Path.GetFullPath` of an absolute Unix path: runs of `/` collapsed, `.`
/// dropped, `..` taking the segment before it (and nothing at the root).
fn full_path(path: &str) -> String {
    let mut segs: Vec<&str> = Vec::new();
    for seg in path.split('/') {
        match seg {
            "" | "." => {}
            ".." => {
                segs.pop();
            }
            seg => segs.push(seg),
        }
    }
    format!("/{}", segs.join("/"))
}

/// What `Directory.ResolveLinkTarget(link, returnFinalTarget: true).FullName`
/// is: `Ok(None)` when `link` is no symbolic link, `Err(())` when it throws
/// (too many links). Each hop's target is joined to the directory of the path
/// so far as text, and only the last is made a full path, so the result is
/// lexical: a `..` takes the segment written before it, link or not.
fn final_target(link: &str) -> Result<Option<String>, ()> {
    let Ok(mut target) = host_fs::read_link(link) else {
        return Ok(None);
    };
    let mut path = link.to_string();
    for _ in 0..40 {
        let text = target.to_string_lossy().into_owned();
        if text.starts_with('/') {
            path = text;
        } else {
            let cut = path.rfind('/').expect("an absolute path has a separator");
            path.truncate(cut);
            path.push('/');
            path.push_str(&text);
        }
        match host_fs::read_link(&path) {
            Ok(next) => target = next,
            Err(_) => return Ok(Some(full_path(&path))),
        }
    }
    Err(())
}

/// A wildcard directory segment of the globs [`msbuild_walk`] expands.
#[derive(Clone, Copy, Debug)]
enum Wild {
    /// `*`: exactly one directory.
    Star,
    /// `**`, last: any number of directories.
    Globstar,
}

/// Why [`msbuild_walk`] has no list: MSBuild's walk would not end (a cycle it
/// does not skip, met at the depth bound), or `IsSubdirectoryOf` throws.
#[derive(Debug)]
struct NoList;

/// The `.fs` files below `dir` (spelt as MSBuild spells the directory) that
/// MSBuild's file matcher expands `<dir>/<wild>/*.fs` to, as full paths.
/// `skip` is the comparison the symbolic-link rule runs under; `None` never
/// skips, which is what following every link gives.
fn msbuild_walk(
    dir: &str,
    wild: &[Wild],
    skip: Option<Comparison>,
    depth: usize,
    out: &mut BTreeSet<String>,
) -> Result<(), NoList> {
    if depth > 12 {
        return Err(NoList);
    }
    if let Some(comparison) = skip {
        let is_link = host_fs::symlink_metadata(dir).is_ok_and(|m| m.file_type().is_symlink());
        if is_link && let Ok(Some(target)) = final_target(dir) {
            match is_subdirectory_of(dir, &target, comparison) {
                Some(true) => return Ok(()),
                Some(false) => {}
                None => return Err(NoList),
            }
        }
    }
    let Ok(entries) = host_fs::read_dir(dir) else {
        return Ok(());
    };
    let mut files = Vec::new();
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.expect("a fixture's listing reads");
        let name = entry.file_name().to_string_lossy().into_owned();
        let path = format!("{dir}/{name}");
        match host_fs::metadata(&path) {
            Ok(m) if m.is_dir() => dirs.push(path),
            Ok(m) if m.is_file() && name.ends_with(".fs") => files.push(path),
            _ => {}
        }
    }
    let (here, below): (bool, Option<&[Wild]>) = match wild {
        [] => (true, None),
        [Wild::Star, rest @ ..] => (false, Some(rest)),
        [Wild::Globstar, ..] => (true, Some(wild)),
    };
    if here {
        out.extend(files);
    }
    if let Some(below) = below {
        for sub in dirs {
            msbuild_walk(&sub, below, skip, depth + 1, out)?;
        }
    }
    Ok(())
}

/// The resolver's answer for `include` from `base`, as full path strings.
fn resolve_strings(
    base: &Path,
    include: &str,
    excludes: &[&str],
) -> Result<Vec<String>, GlobDecline> {
    let include = SpecFragment::split_escaped(include);
    let excludes: Vec<SpecFragment> = excludes
        .iter()
        .flat_map(|s| SpecFragment::split_escaped(s))
        .collect();
    resolve(&GlobRequest {
        base_dir: base,
        include: &include,
        excludes: &excludes,
        observer: &Observer::new(),
    })
    .map(|paths| {
        paths
            .into_iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect()
    })
}

/// A fresh temporary directory, canonical, so the paths the resolver reports
/// and the paths the model spells agree.
fn canonical_tempdir() -> (TempDir, PathBuf) {
    let tmp = TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    (tmp, root)
}

fn write(path: &Path) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, b"// f\n").unwrap();
}

/// Whether the file system under `dir` tells names apart by case.
fn case_sensitive(dir: &Path) -> bool {
    write(&dir.join("case-probe"));
    let sensitive = host_fs::symlink_metadata(dir.join("CASE-PROBE")).is_err();
    fs::remove_file(dir.join("case-probe")).unwrap();
    sensitive
}

fn is_symlinked_directory(result: &Result<Vec<String>, GlobDecline>) -> bool {
    matches!(result, Err(GlobDecline::SymlinkedDirectory { .. }))
}

/// Probed (dotnet 10.0.301, MSBuild 18.9): `src/*/*.fs` skips `src/link`, a
/// link to the project directory, which is above the walk's root; the walk
/// would enter it and list the project's files under it.
#[test]
fn a_link_to_an_ancestor_above_the_walk_root_declines() {
    let (_tmp, root) = canonical_tempdir();
    let proj = root.join("proj");
    write(&proj.join("a.fs"));
    write(&proj.join("src/real/r.fs"));
    symlink(&proj, proj.join("src/link")).unwrap();
    assert!(is_symlinked_directory(&resolve_strings(
        &proj,
        "src/*/*.fs",
        &[]
    )));
    // MSBuild's list, which the walk's own reading of the link is not.
    let base = format!("{}/src", proj.display());
    for comparison in [Comparison::Ordinal, Comparison::OrdinalIgnoreCase] {
        let mut msbuild = BTreeSet::new();
        msbuild_walk(&base, &[Wild::Star], Some(comparison), 0, &mut msbuild).unwrap();
        assert_eq!(
            msbuild.into_iter().collect::<Vec<_>>(),
            [format!("{}/src/real/r.fs", proj.display())]
        );
    }
}

/// Probed: `link/*.fs`, with `link` a link to the project directory, is empty
/// in MSBuild: the rule runs on the walk's root too.
#[test]
fn a_walk_root_that_links_to_its_own_parent_declines() {
    let (_tmp, root) = canonical_tempdir();
    let proj = root.join("proj");
    write(&proj.join("a.fs"));
    symlink(&proj, proj.join("link")).unwrap();
    assert!(is_symlinked_directory(&resolve_strings(
        &proj,
        "link/*.fs",
        &[]
    )));
}

/// Probed on macOS, whose temp directory ignores case: a link to the project
/// directory spelt in another case is skipped too. On a case-sensitive file
/// system the variant is a directory of its own, which an ordinal build walks
/// and a case-ignoring one skips. Both an ASCII and a non-ASCII case pair.
#[test]
fn a_link_to_a_case_variant_of_an_ancestor_declines() {
    for (name, variant) in [("proj", "PROJ"), ("pr\u{e9}j", "pr\u{c9}j")] {
        let (_tmp, root) = canonical_tempdir();
        let proj = root.join(name);
        write(&proj.join("a.fs"));
        write(&proj.join("src/real/r.fs"));
        if case_sensitive(&root) {
            write(&root.join(variant).join("v.fs"));
        }
        symlink(root.join(variant), proj.join("src/link")).unwrap();
        let ours = resolve_strings(&proj, "src/*/*.fs", &[]);
        assert!(is_symlinked_directory(&ours), "{name}: {ours:?}");
        let base = format!("{}/src", proj.display());
        let mut ordinal = BTreeSet::new();
        msbuild_walk(
            &base,
            &[Wild::Star],
            Some(Comparison::Ordinal),
            0,
            &mut ordinal,
        )
        .unwrap();
        let mut ignoring = BTreeSet::new();
        msbuild_walk(
            &base,
            &[Wild::Star],
            Some(Comparison::OrdinalIgnoreCase),
            0,
            &mut ignoring,
        )
        .unwrap();
        assert_ne!(ordinal, ignoring, "{name}: the temp directory decides");
    }
}

/// Probed (dotnet 10.0.301): MSBuild's `**` descends into a symlinked
/// directory whose target does not contain it, and reports its files under
/// the link's path. Whether the target contains the link is decided by its
/// lexical target and the build's temp directory, which the walk does not
/// see, so a glob that selects anything under the link declines; one that
/// selects nothing there commits.
#[test]
fn a_glob_selecting_under_a_directory_link_declines() {
    let (_ext, ext) = canonical_tempdir();
    write(&ext.join("hidden.fs"));
    let (_tmp, base) = canonical_tempdir();
    symlink(&ext, base.join("linkdir")).unwrap();
    write(&base.join("a.fs"));
    for include in ["**/*.fs", "*/*.fs", "linkdir/*.fs", "linkdir/**/*.fs"] {
        let ours = resolve_strings(&base, include, &[]);
        assert!(is_symlinked_directory(&ours), "{include}: {ours:?}");
    }
    let a = format!("{}/a.fs", base.display());
    // An excluded link, or one the glob never enters, costs nothing.
    assert_eq!(
        resolve_strings(&base, "**/*.fs", &["linkdir/**"]),
        Ok(vec![a.clone()])
    );
    assert_eq!(resolve_strings(&base, "*.fs", &[]), Ok(vec![a.clone()]));
    assert_eq!(resolve_strings(&base, "**/*.fsi", &[]), Ok(vec![]));
}

/// A tiny deterministic generator, so the sweep below reproduces exactly.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

/// Where a generated link points, relative to the link.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum TargetKind {
    /// A directory on the link's own path, the project's parent included.
    Ancestor,
    /// One of those spelt with its last name in another case (ASCII, or a
    /// non-ASCII case pair).
    CaseVariantOfAncestor,
    /// A directory below the link's own directory.
    Descendant,
    /// A directory neither above nor below it.
    Unrelated,
}

/// The project's directories, below the project root, and its files.
const DIRS: &[&str] = &["d", "d/e", "d\u{e9}"];
const FILES: &[&str] = &["a.fs", "d/b.fs", "d/e/c.fs", "d\u{e9}/u.fs"];

/// `name` with the case of each cased letter flipped, or of each non-ASCII
/// one alone where `non_ascii_only` and it has one.
fn flip_case(name: &str, non_ascii_only: bool) -> String {
    let non_ascii_only = non_ascii_only && !name.is_ascii();
    name.chars()
        .flat_map(|c| {
            if non_ascii_only && c.is_ascii() {
                vec![c]
            } else if c.is_lowercase() {
                c.to_uppercase().collect()
            } else {
                c.to_lowercase().collect()
            }
        })
        .collect()
}

/// `to` written relative to the directory `from`, both absolute and lexical.
fn relative(from: &Path, to: &Path) -> PathBuf {
    let from: Vec<_> = from.components().collect();
    let to: Vec<_> = to.components().collect();
    let common = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    let mut out = PathBuf::new();
    for _ in common..from.len() {
        out.push("..");
    }
    for c in &to[common..] {
        out.push(c);
    }
    out
}

/// The globs each generated tree is expanded with: a fixed directory (a link
/// among them) and a wildcard directory part, then `*.fs`.
fn globs(links: &[String]) -> Vec<(String, Vec<Wild>)> {
    let mut out = vec![
        (String::new(), vec![Wild::Globstar]),
        (String::new(), vec![Wild::Star]),
        (String::new(), vec![Wild::Star, Wild::Star]),
        (String::new(), vec![]),
        ("d".to_string(), vec![Wild::Globstar]),
        ("d".to_string(), vec![Wild::Star]),
    ];
    for link in links {
        out.push((link.clone(), vec![]));
        out.push((link.clone(), vec![Wild::Star]));
    }
    out
}

/// Every generated tree of links, expanded with every glob: where the resolver
/// commits, its list must be MSBuild's under both comparisons; a glob that
/// selects nothing through a link must not decline for the link; and the
/// generator must reach each target kind and each regime of the rule.
#[test]
fn the_walk_commits_only_what_msbuild_lists_under_either_case_rule() {
    let mut rng = SplitMix64(0x0959_5ca1_ab1e);
    let mut by_kind: BTreeMap<TargetKind, usize> = BTreeMap::new();
    let (mut checked, mut committed, mut skipped, mut temp_dir_decides) = (0, 0, 0, 0);
    for case in 0..160 {
        let (_tmp, root) = canonical_tempdir();
        let sensitive = case_sensitive(&root);
        let proj = root.join(if case % 2 == 0 { "proj" } else { "pr\u{e9}j" });
        for file in FILES {
            write(&proj.join(file));
        }
        write(&root.join("out/o.fs"));
        let mut links = Vec::new();
        for i in 0..1 + rng.below(3) {
            let parent_rel = *rng.pick(&["", "d", "d/e", "d\u{e9}"]);
            let parent = if parent_rel.is_empty() {
                proj.clone()
            } else {
                proj.join(parent_rel)
            };
            let kind = *rng.pick(&[
                TargetKind::Ancestor,
                TargetKind::CaseVariantOfAncestor,
                TargetKind::Descendant,
                TargetKind::Unrelated,
            ]);
            // The link's ancestors from its directory up to the project's
            // parent, and those within the project, whose names can change case.
            let ancestors: Vec<PathBuf> = parent
                .ancestors()
                .take_while(|a| a.starts_with(&root))
                .map(Path::to_path_buf)
                .collect();
            let target = match kind {
                TargetKind::Ancestor => rng.pick(&ancestors).clone(),
                TargetKind::CaseVariantOfAncestor => {
                    let within: Vec<&PathBuf> =
                        ancestors.iter().filter(|a| a.starts_with(&proj)).collect();
                    let ancestor = *rng.pick(&within);
                    let name = ancestor.file_name().unwrap().to_string_lossy();
                    let variant = ancestor.with_file_name(flip_case(&name, rng.below(2) == 0));
                    if sensitive {
                        write(&variant.join("v.fs"));
                    }
                    variant
                }
                TargetKind::Descendant => {
                    let below: Vec<PathBuf> = DIRS
                        .iter()
                        .map(|d| proj.join(d))
                        .filter(|d| d.starts_with(&parent) && *d != parent)
                        .collect();
                    if below.is_empty() {
                        continue;
                    }
                    rng.pick(&below).clone()
                }
                TargetKind::Unrelated => {
                    let others: Vec<PathBuf> = DIRS
                        .iter()
                        .map(|d| proj.join(d))
                        .filter(|d| !d.starts_with(&parent) && !parent.starts_with(d))
                        .chain([root.join("out")])
                        .collect();
                    rng.pick(&others).clone()
                }
            };
            let written = match relative(&parent, &target) {
                _ if rng.below(2) == 0 => target.clone(),
                rel if rel.as_os_str().is_empty() => PathBuf::from("."),
                rel => rel,
            };
            let name = format!("l{i}");
            symlink(&written, parent.join(&name)).unwrap();
            *by_kind.entry(kind).or_default() += 1;
            if parent_rel.is_empty() {
                links.push(name);
            }
        }
        for (fixed, wild) in globs(&links) {
            let base = if fixed.is_empty() {
                proj.display().to_string()
            } else {
                format!("{}/{fixed}", proj.display())
            };
            let walk = |skip| {
                let mut out = BTreeSet::new();
                msbuild_walk(&base, &wild, skip, 0, &mut out)
                    .ok()
                    .map(|()| out)
            };
            let ordinal = walk(Some(Comparison::Ordinal));
            let ignoring = walk(Some(Comparison::OrdinalIgnoreCase));
            let followed = walk(None);
            let include: String = [fixed.as_str()]
                .into_iter()
                .filter(|s| !s.is_empty())
                .chain(wild.iter().map(|w| match w {
                    Wild::Star => "*",
                    Wild::Globstar => "**",
                }))
                .chain(["*.fs"])
                .collect::<Vec<_>>()
                .join("/");
            let ours = resolve_strings(&proj, &include, &[]);
            let context = || {
                format!(
                    "case {case}, include {include}\nours: {ours:?}\nordinal: {ordinal:?}\n\
                     ignoring case: {ignoring:?}\nfollowing every link: {followed:?}"
                )
            };
            checked += 1;
            skipped += usize::from(ignoring != followed);
            temp_dir_decides += usize::from(ordinal != ignoring);
            if let Ok(list) = &ours {
                committed += 1;
                let list: BTreeSet<String> = list.iter().cloned().collect();
                assert_eq!(ordinal.as_ref(), Some(&list), "{}", context());
                assert_eq!(ignoring.as_ref(), Some(&list), "{}", context());
            }
            // A list that passes through no link cannot be moved by the rule.
            let through_link = |file: &String| {
                Path::new(file)
                    .strip_prefix(&proj)
                    .unwrap()
                    .ancestors()
                    .filter(|a| !a.as_os_str().is_empty())
                    .any(|a| {
                        host_fs::symlink_metadata(proj.join(a))
                            .is_ok_and(|m| m.file_type().is_symlink())
                    })
            };
            if let Some(followed) = &followed
                && !followed.iter().any(through_link)
            {
                assert!(!is_symlinked_directory(&ours), "{}", context());
            }
        }
    }
    eprintln!(
        "symlinked directories: {committed}/{checked} committed; {skipped} lists the rule \
         moves, {temp_dir_decides} the temp directory decides; links by target: {by_kind:?}"
    );
    for kind in [
        TargetKind::Ancestor,
        TargetKind::CaseVariantOfAncestor,
        TargetKind::Descendant,
        TargetKind::Unrelated,
    ] {
        assert!(
            by_kind.get(&kind).copied().unwrap_or(0) >= 30,
            "{by_kind:?}"
        );
    }
    assert!(skipped >= 50, "the rule moved only {skipped} lists");
    assert!(
        temp_dir_decides >= 20,
        "the temp directory decided only {temp_dir_decides} lists"
    );
    assert!(
        committed * 100 >= checked * 25,
        "only {committed}/{checked} committed"
    );
}
