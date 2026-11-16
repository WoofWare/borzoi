//! Generative differential: glob and literal item specs against **names that
//! differ from them only in case**, on disk trees that vary which case
//! variants exist, held to certain-implies-exact against the real MSBuild
//! evaluator (the oracle's `items` op) under two cultures.
//!
//! ## Why this exists
//!
//! How MSBuild treats case in an item spec is not one rule (#607):
//!
//! - A literal include meets its excludes through `FileSpecMatcherTester`,
//!   which ignores ASCII case throughout.
//! - A glob include is expanded by the file matcher, where the file system
//!   decides which directories exist (the include's fixed directory, and each
//!   exclude's, looked up as written: an exclude whose fixed directory does
//!   not exist is dropped) and every comparison past that ignores case. So
//!   `Exclude="SUB/a.fs"` keeps `sub/a.fs` unless a directory named `SUB`
//!   exists, empty or not, and then takes it.
//! - The file matcher compares a glob with a wildcard directory part by a
//!   regular expression, which ignores case by the build's culture: in Turkish
//!   `i` and `I` are two letters, and on any culture `k` takes the Kelvin sign
//!   and `i` takes `İ`.
//!
//! Each of those depends on something a fixed fixture holds still: which case
//! variants exist on disk, which part of a spec the case difference sits in,
//! and the culture. So every case here draws its own disk tree, its specs from
//! a grammar of fixed directories, wildcard directories and file names spelt
//! in several cases, and is checked against an oracle under the invariant
//! culture and one under Turkish. Where the resolver commits, both must agree
//! with it exactly; a decline makes no claim.
//!
//! The resolver ports the file matcher's walk, so the rule holds on every
//! host: the file system answers what exists (case-insensitively on a
//! case-insensitive one), and every comparison past that is the port's.
//!
//! Now and then a disk also holds symbolic links to directories: to the
//! project directory, to its parent, to the project directory spelt in upper
//! case, below it, and outside it. MSBuild skips such a directory when the
//! link's target contains it, comparing by its temp directory's case
//! sensitivity, so a link to a case variant of an ancestor is walked by an
//! oracle whose temp directory is case-sensitive (Linux) and skipped by one
//! whose is not (macOS). The resolver must decline wherever that could move
//! what it selects.
//!
//! Inputs are a fixed-seed sweep, so a failure reproduces exactly.

mod common;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::{DiagnosticKind, GlobDecline, glob_resolver};
use common::{Oracle, SplitMix64};
use std::collections::{BTreeMap, HashMap};

/// The Turkish culture, under which a .NET regular expression that ignores
/// case keeps `i` and `I` apart.
const TURKISH: &str = "tr_TR.UTF-8";

/// Stands for the project directory spelt in upper case: a rooted spec whose
/// fixed directory exists only on a case-insensitive file system.
const ROOT_UPPER: &str = "{ROOT_UPPER}";

/// Files on every disk. A trailing `/` makes an empty directory.
const BASE_FILES: &[&str] = &[
    "a.fs",
    "b.fs",
    "sub/a.fs",
    "sub/Deep/d.fs",
    "sub/Deep/in.fs",
];

/// Entries each disk holds a random selection of: case variants of the base
/// directories (empty, or holding a file) and files, and upper-case names.
const EXTRAS: &[&str] = &[
    "SUB/",
    "SUB/b.fs",
    "Sub/",
    "sub/deep/",
    "sub/DEEP/e.fs",
    "B.fs",
    "Up.fs",
    "sub/IN.fs",
    "sub/a/b.fs",
    "sub/Deep/a/b.fs",
];

/// Non-ASCII names, one of which a disk holds now and then, under `uni/` so
/// only the specs that reach it meet it: a case pair `OrdinalIgnoreCase`
/// folds, and the letters the file matcher folds onto ASCII ones (the Kelvin
/// sign and `İ` by its regular expressions, `ı` and `ſ` by
/// `OrdinalIgnoreCase`).
const NON_ASCII: &[&str] = &[
    "uni/\u{e9}.fs",
    "uni/\u{c9}.fs",
    "uni/\u{212a}.fs",
    "uni/\u{130}.fs",
    "uni/\u{131}.fs",
    "uni/\u{17f}.fs",
];

/// A spec's fixed directory: none, the base directories in several cases,
/// and rooted spellings (the project directory as MSBuild reports it, and
/// spelt in upper case).
const FIXED: &[&str] = &[
    "",
    "",
    "",
    "",
    "sub",
    "SUB",
    "Sub",
    "sub/Deep",
    "sub/deep",
    "SUB/DEEP",
    "uni",
    "$(MSBuildProjectDirectory)",
    ROOT_UPPER,
];

/// Fixed directories drawn now and then, as most of what they meet declines
/// by name: rooted ones below the project directory (which an exclude with a
/// wildcard directory part must match in anchoring), and `./`-prefixed ones
/// (which the file matcher relates to an exclude by spelling).
const RARE_FIXED: &[&str] = &[
    "$(MSBuildProjectDirectory)/SUB",
    "$(MSBuildProjectDirectory)/sub",
    ".",
    "./sub",
];

/// A spec's wildcard directory part: none, single-segment wildcards in either
/// case, recursive ones naming a directory (read by regular expression, or by
/// directory name for `**/x/**`), and a bare `**`.
const WILD: &[&str] = &[
    "",
    "",
    "",
    "**",
    "**",
    "s*",
    "S*",
    "*",
    "**/deep",
    "**/DEEP",
    "*/Deep",
    "*/DEEP",
    "D*",
    "d*",
    "**/Deep/**",
    "**/DEEP/**",
    "**/**",
    "S*/**",
];

/// A spec's file name: literal names and wildcard ones in several cases, and
/// names with `i`/`I` and `k` (which a culture or a non-ASCII letter can fold).
const NAME: &[&str] = &[
    "*.fs", "*.FS", "A*", "a*.fs", "a.fs", "A.FS", "b.fs", "B.FS", "?.fs", "*", "*.*", "d.fs",
    "D.FS", "in.fs", "IN.FS", "i*.fs", "I*.fs", "k.fs", "K.fs", "**", "up.fs", "UP.FS", "a*.*",
    "A*.*", "a?b.fs", "*.*.*",
];

/// Non-ASCII file names, outside the allow-list, drawn now and then.
const RARE_NAME: &[&str] = &["\u{e9}.fs", "\u{c9}.fs"];

/// Where a generated symbolic link points.
#[derive(Clone, Copy, Debug)]
enum LinkTarget {
    /// The project directory.
    Root,
    /// The project directory spelt with its name in upper case: on a
    /// case-sensitive file system a directory of its own, holding a file.
    RootUpper,
    /// The project directory's parent, written relative to the link.
    Parent,
    /// `sub`, below the link's own directory.
    Sub,
    /// A directory beside the project directory, holding a file.
    Outside,
}

/// Links a disk holds a random selection of, now and then, by path below the
/// project directory.
const LINKS: &[(&str, LinkTarget)] = &[
    ("sub/up", LinkTarget::Root),
    ("sub/upper", LinkTarget::RootUpper),
    ("sub/Deep/top", LinkTarget::Parent),
    ("lk", LinkTarget::Sub),
    ("sub/Deep/out", LinkTarget::Outside),
];

/// One spec fragment. `links` draws the link dimension apart from `rng`, so
/// adding it moved no other draw.
fn gen_fragment(rng: &mut SplitMix64, links: &mut SplitMix64) -> String {
    let fixed = if rng.below(8) == 0 {
        rng.pick(RARE_FIXED)
    } else {
        rng.pick(FIXED)
    };
    // Now and then a fixed directory that is a link, where the disk holds it.
    let fixed = if links.below(16) == 0 { "lk" } else { fixed };
    let name = if rng.below(12) == 0 {
        rng.pick(RARE_NAME)
    } else {
        rng.pick(NAME)
    };
    let parts: [&str; 3] = [fixed, rng.pick(WILD), name];
    parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .collect::<Vec<_>>()
        .join("/")
}

fn gen_spec(rng: &mut SplitMix64, links: &mut SplitMix64) -> String {
    (0..1 + rng.below(2))
        .map(|_| gen_fragment(rng, links))
        .collect::<Vec<_>>()
        .join(";")
}

struct Fixture {
    files: Vec<&'static str>,
    links: Vec<(&'static str, LinkTarget)>,
    include: String,
    exclude: Option<String>,
}

impl Fixture {
    /// A fixture, its link dimension drawn from `links` (see [`gen_fragment`]).
    fn generate(rng: &mut SplitMix64, links: &mut SplitMix64) -> Fixture {
        let mut files = BASE_FILES.to_vec();
        files.extend(EXTRAS.iter().filter(|_| rng.below(4) == 0));
        if rng.below(6) == 0 {
            files.push(rng.pick(NON_ASCII));
        }
        let linked = if links.below(4) == 0 {
            LINKS
                .iter()
                .copied()
                .filter(|_| links.below(2) == 0)
                .collect()
        } else {
            Vec::new()
        };
        let include = gen_spec(rng, links);
        let exclude = (rng.below(3) != 0).then(|| gen_spec(rng, links));
        Fixture {
            files,
            links: linked,
            include,
            exclude,
        }
    }

    /// Whether a spec spells a letter in upper case, outside a property
    /// reference: the fixtures where case can decide the answer.
    fn spells_upper_case(&self) -> bool {
        let upper = |spec: &str| {
            spec.contains(ROOT_UPPER)
                || spec
                    .replace("$(MSBuildProjectDirectory)", "")
                    .chars()
                    .any(|c| c.is_ascii_uppercase())
        };
        upper(&self.include) || self.exclude.as_deref().is_some_and(upper)
    }

    fn xml(&self, root_upper: &str) -> String {
        let spell = |spec: &str| spec.replace(ROOT_UPPER, root_upper);
        let exclude = self
            .exclude
            .as_deref()
            .map(|e| format!(" Exclude=\"{}\"", spell(e)))
            .unwrap_or_default();
        format!(
            "<Project>\n  <ItemGroup>\n    <Compile Include=\"{}\"{exclude} />\n  </ItemGroup>\n</Project>\n",
            spell(&self.include)
        )
    }
}

/// What the resolver seam made of a fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    /// It committed, and both oracles agreed exactly (or the check panicked).
    Committed,
    /// The resolver declined, naming why: the `GlobDecline` variant.
    ResolverDeclined(String),
    /// It declined for any other reason, which this harness's fixtures should
    /// never cause.
    Declined,
}

/// Lexical normalisation, as MSBuild's `FullPath` resolves `.` and `..`.
fn norm(path: &str) -> String {
    let mut out: Vec<&str> = Vec::new();
    for seg in path.split(['/', '\\']) {
        match seg {
            "." => {}
            ".." if out.len() > 1 => {
                out.pop();
            }
            _ => out.push(seg),
        }
    }
    out.join("/")
}

fn check(oracles: &mut [Oracle; 2], fixture: &Fixture) -> Outcome {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path())
        .expect("canonicalize")
        .join("proj");
    std::fs::create_dir_all(&root).expect("mkdir");
    for entry in &fixture.files {
        let path = root.join(entry);
        if entry.ends_with('/') {
            std::fs::create_dir_all(&path).expect("mkdir");
        } else {
            std::fs::create_dir_all(path.parent().expect("a file has a parent")).expect("mkdir");
            std::fs::write(path, "module M\n").expect("write source");
        }
    }
    #[cfg(unix)]
    for (path, target) in &fixture.links {
        use borzoi_msbuild::observed::host_fs::HostPath;
        let target = match target {
            LinkTarget::Root => root.clone(),
            LinkTarget::RootUpper => {
                let upper = root.with_file_name("PROJ");
                if !upper.host_exists() {
                    std::fs::create_dir_all(&upper).expect("mkdir");
                    std::fs::write(upper.join("v.fs"), "module M\n").expect("write source");
                }
                upper
            }
            LinkTarget::Parent => std::path::PathBuf::from("../../.."),
            LinkTarget::Sub => root.join("sub"),
            LinkTarget::Outside => {
                let outside = root.with_file_name("outside");
                std::fs::create_dir_all(&outside).expect("mkdir");
                std::fs::write(outside.join("o.fs"), "module M\n").expect("write source");
                outside
            }
        };
        std::os::unix::fs::symlink(target, root.join(path)).expect("symlink");
    }
    let proj = root.join("Demo.fsproj");
    let xml = fixture.xml(&root.to_string_lossy().to_ascii_uppercase());
    std::fs::write(&proj, &xml).expect("write project");

    let resolver: &borzoi_msbuild::GlobResolver<'_> = &glob_resolver::resolve;
    let parsed = parse_fsproj_with_imports(
        &xml,
        &proj,
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        Some(resolver),
    )
    .expect("well-formed XML parses");
    if !parsed.diagnostics.is_empty() || parsed.items_uncertain {
        let reasons: Vec<String> = parsed
            .diagnostics
            .iter()
            .filter_map(|d| match &d.kind {
                DiagnosticKind::GlobDeclined { reason, .. } => Some(match reason {
                    GlobDecline::OutsideModelledShape { shape, .. } => format!("{shape:?}"),
                    other => format!("{other:?}")
                        .split([' ', '{'])
                        .next()
                        .unwrap_or_default()
                        .to_string(),
                }),
                _ => None,
            })
            .collect();
        return match reasons.first() {
            Some(reason) if reasons.len() == parsed.diagnostics.len() => {
                Outcome::ResolverDeclined(reason.clone())
            }
            _ => Outcome::Declined,
        };
    }

    let ours: Vec<String> = parsed
        .items
        .iter()
        .map(|i| norm(&i.include.to_string_lossy()))
        .collect();
    for (oracle, culture) in oracles.iter_mut().zip(["invariant", TURKISH]) {
        let theirs: Vec<String> = oracle
            .items(&xml, &proj, "Compile", &[])
            .expect("MSBuild evaluates these documents")
            .iter()
            .map(|p| norm(p))
            .collect();
        assert_eq!(
            ours, theirs,
            "certain-implies-exact violated under the {culture} culture.\ndisk: {:?}\nlinks: {:?}\n\
             project:\n{xml}",
            fixture.files, fixture.links
        );
    }
    Outcome::Committed
}

fn oracles() -> [Oracle; 2] {
    [Oracle::spawn(), Oracle::spawn_with_locale(TURKISH)]
}

/// The Turkish oracle must keep `i` and `I` apart in a glob read by regular
/// expression, or the culture axis of this harness checks nothing.
#[test]
fn the_turkish_oracle_keeps_i_apart() {
    let mut oracles = oracles();
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root = dir.path().join("proj");
    std::fs::create_dir_all(root.join("sub/x")).expect("mkdir");
    std::fs::write(root.join("sub/x/bi.fs"), "").expect("write");
    let proj = root.join("Demo.fsproj");
    let xml = "<Project><ItemGroup><Compile Include=\"s*/x/BI.fs\" /></ItemGroup></Project>";
    std::fs::write(&proj, xml).expect("write project");
    let counts: Vec<usize> = oracles
        .iter_mut()
        .map(|o| {
            o.items(xml, &proj, "Compile", &[])
                .expect("evaluates")
                .len()
        })
        .collect();
    assert_eq!(counts, [1, 0], "invariant, then Turkish");
}

/// The oracle table on #607 (disk `a.fs`, `b.fs`, `sub/a.fs`), the directory
/// existence corners found reviewing a first implementation, and the
/// culture-dependent ones. Every modelled corner must commit, and each culture
/// or working-directory corner must decline by name.
#[test]
fn case_corners() {
    let mut oracles = oracles();
    const TABLE: &[&str] = &["a.fs", "b.fs", "sub/a.fs"];
    let corner = |files: &[&'static str], include: &str, exclude: Option<&str>| Fixture {
        files: files.to_vec(),
        links: Vec::new(),
        include: include.to_string(),
        exclude: exclude.map(str::to_string),
    };
    let committing = [
        // Literal includes: `FileSpecMatcherTester`, case folded throughout.
        corner(TABLE, "a.fs;b.fs", Some("A.fs")),
        corner(TABLE, "a.fs;b.fs", Some("./A.fs")),
        corner(TABLE, "a.fs;b.fs", Some("$(MSBuildProjectDirectory)/A.fs")),
        corner(TABLE, "sub/a.fs", Some("SUB/a.fs")),
        corner(TABLE, "sub/a.fs", Some("SUB/A.FS")),
        corner(TABLE, "a.fs;b.fs", Some("A*.fs")),
        corner(TABLE, "sub/a.fs", Some("SUB/*.fs")),
        corner(TABLE, "sub/a.fs", Some("S*/a.fs")),
        corner(TABLE, "a.fs;b.fs", Some(&format!("{ROOT_UPPER}/A.fs"))),
        // Glob includes: names fold; a fixed directory exists as written.
        corner(TABLE, "*.fs", Some("A.fs")),
        corner(TABLE, "*.fs", Some("B*.fs")),
        corner(TABLE, "*.fs", Some("A?fs")),
        corner(TABLE, "A*.fs", None),
        corner(TABLE, "*.FS", None),
        corner(TABLE, "sub/*.fs", Some("sub/A.fs")),
        corner(TABLE, "sub/*.fs", Some("SUB/a.fs")),
        corner(TABLE, "*.fs", Some("$(MSBuildProjectDirectory)/A.fs")),
        corner(TABLE, "*.fs", Some(&format!("{ROOT_UPPER}/A.fs"))),
        corner(TABLE, "**/*.fs", Some("SUB/a.fs")),
        corner(TABLE, "**/*.fs", Some("sub/A.fs")),
        corner(TABLE, "**/*.fs", Some("**/A.fs")),
        corner(TABLE, "**/*.fs", Some("S*/a.fs")),
        corner(TABLE, "**/*.fs", Some("SUB/*.fs")),
        corner(TABLE, "**/*.fs", Some("sub/A*.fs")),
        corner(TABLE, "**/*.fs", Some("Sub/**")),
        corner(TABLE, "*.fs", Some("A*")),
        corner(TABLE, "SUB/*.fs", None),
        corner(TABLE, "S*/*.fs", None),
        corner(TABLE, "sub/A*.fs", None),
        corner(TABLE, "s*/A.FS", None),
        corner(TABLE, "**/A.fs", None),
        corner(TABLE, "SUB/**/*.fs", None),
        corner(TABLE, "sub/**/A.fs", None),
        // An empty `SUB` makes an exclude spelt under it take part, and it
        // then takes `sub/a.fs` too.
        corner(&["sub/a.fs", "SUB/"], "sub/*.fs", Some("SUB/*.fs")),
        corner(&["sub/a.fs", "SUB/"], "sub/*.fs", Some("SUB/a.fs")),
        corner(&["sub/a.fs", "SUB/"], "**/*.fs", Some("SUB/a.fs")),
        corner(&["sub/a.fs"], "sub/*.fs", Some("SUB/*.fs")),
        // A directory a recursive exclude names, in another case.
        corner(&["sub/Deep/d.fs"], "**/*.fs", Some("**/DEEP/**")),
        corner(&["sub/Deep/d.fs"], "sub/**/*.fs", Some("**/deep/*.fs")),
        // `**/**/**` is the directory-name shape with a name of `**`: one
        // directory, any name, never none.
        corner(&["sub/a.fs", "SUB/"], "sub/*.fs", Some("SUB/**/**/**")),
        corner(&["sub/a.fs", "sub/x/b.fs"], "sub/**/**/**", None),
        corner(&["sub/a.fs", "sub/x/b.fs"], "**/*.fs", Some("sub/**/**/**")),
        // A regular expression reads `*.*` as `*`.
        corner(&["sub/ab", "sub/ab.fs"], "s*/A*.*", None),
        corner(&["sub/ab", "sub/ab.fs"], "sub/*.*", Some("S*/a*.*")),
        corner(&["ab", "z.fs"], "AB;z.fs", Some("a*.*")),
        // A regular expression reads `?` as any character, a separator
        // included: against a literal include, and past a `**` in the file
        // matcher. Matched name by name, or before a `**`, it stays in a name.
        corner(&["q/x/a/b.fs"], "**/X/a?b.fs", None),
        corner(
            &["sub/a/b.fs", "z.fs"],
            "sub/a/b.fs;z.fs",
            Some("SUB/a?b.fs"),
        ),
        corner(
            &["sub/a/b.fs", "z.fs"],
            "sub/a/b.fs;z.fs",
            Some("**/a?b.fs"),
        ),
        corner(&["sub/a/b.fs"], "s*/a?b.fs", None),
        // An exclude based above the include's walk root is matched by its
        // regular expression alone, so its `?` crosses a separator there.
        corner(&["sub/a/b.fs"], "sub/**/B.fs", Some("s*/a?b.fs")),
        corner(&["sub/a/b.fs"], "sub/**/B.fs", Some("S*/A?B/*.fs")),
        // `*.*.*` reads as `*.*` there, which still needs a dot.
        corner(&["sub/noext"], "s*/*.*.*", None),
        corner(&["sub/noext", "sub/x.fs"], "sub/*", Some("s*/*.*.*")),
        // `i` and `I` where no regular expression compares them.
        corner(&["sub/x/bi.fs"], "**/*.fs", Some("**/BI.fs")),
        corner(&["sub/x/bi.fs"], "sub/x/*.fs", Some("sub/x/BI.fs")),
        // The directory a `**/**/**` exclude needs is above the include's
        // walk root, which MSBuild never matches against it (#615).
        corner(&["sub/x/b.fs"], "sub/x/*.fs", Some("**/**/**")),
        corner(&["sub/Deep/d.fs"], "sub/Deep/*.fs", Some("**/DEEP/**")),
        // The walk looks for a directory named `.` before a `**`, and the
        // regular expression drops one after it.
        corner(&["sub/a.fs"], "*/./**/*.fs", Some("missing/*.fs")),
        corner(&["sub/a.fs"], "**/./*.fs", None),
        // A `.` in the fixed directory stays in what the walk lists, which the
        // regular expression, having collapsed it, refuses.
        corner(&["sub/a/b.fs"], "sub/./*/*", None),
        // A `.` segment relates an include to an exclude by spelling.
        corner(TABLE, "*.fs", Some("./a.fs")),
        corner(TABLE, "./*.fs", Some("a.fs")),
        // An exclude anchored unlike its include, and one under a `..`.
        corner(TABLE, "**/*.fs", Some("$(MSBuildProjectDirectory)/s*/*.fs")),
        corner(TABLE, "../proj/**/*.fs", Some("**/.*/**")),
        corner(TABLE, "../proj/*/*.fs", Some("s*/*.fs")),
    ];
    for fixture in &committing {
        let outcome = check(&mut oracles, fixture);
        assert_eq!(
            outcome,
            Outcome::Committed,
            "a case corner did not commit:\ndisk: {:?}\n{}",
            fixture.files,
            fixture.xml(ROOT_UPPER)
        );
    }
    let declining = [
        // An exclude read by regular expression under one culture takes what
        // it leaves under the other, while the include is matched name by
        // name (#976).
        (
            corner(
                &["sub/Deep/in.fs", "SUB/", "sub/deep/"],
                "Sub/**/IN.FS",
                Some("Sub/D*/I*.fs"),
            ),
            "CultureDependentCase",
        ),
        // A regular expression compares `i` with `I`, which Turkish keeps
        // apart.
        (
            corner(&["sub/x/bi.fs"], "s*/x/*.fs", Some("s*/x/BI.fs")),
            "CultureDependentCase",
        ),
        (
            corner(&["sub/x/bi.fs"], "s*/x/BI.fs", None),
            "CultureDependentCase",
        ),
        (
            corner(&["sub/x/bi.fs"], "**/*.fs", Some("S*/x/BI.fs")),
            "CultureDependentCase",
        ),
        // A regular expression folds the Kelvin sign onto `k`.
        (
            corner(&["sub/x/\u{212a}.fs"], "s*/x/k.fs", None),
            "NonAscii",
        ),
        // A `~` in a fixed directory is looked up from the working directory.
        (
            corner(&["sub/a~b/x.fs", "z.fs"], "sub/A~B/*.fs", None),
            "TildeInFixedDirectory",
        ),
        (
            corner(&["sub/a~b/x.fs", "z.fs"], "**/*.fs", Some("sub/A~B/*.fs")),
            "TildeInFixedDirectory",
        ),
    ];
    for (fixture, reason) in &declining {
        let outcome = check(&mut oracles, fixture);
        assert_eq!(
            outcome,
            Outcome::ResolverDeclined(reason.to_string()),
            "disk: {:?}\n{}",
            fixture.files,
            fixture.xml(ROOT_UPPER)
        );
    }
}

/// Links to directories, on every host: a glob that selects through one
/// declines, as whether MSBuild skips it turns on what the walk does not see
/// (the link to the upper-case spelling is walked by an oracle whose temp
/// directory is case-sensitive and skipped by one whose is not); one that
/// never enters it commits.
#[cfg(unix)]
#[test]
fn link_corners() {
    let mut oracles = oracles();
    const TABLE: &[&str] = &["a.fs", "b.fs", "sub/a.fs"];
    let linked = |links: &[(&'static str, LinkTarget)], include: &str| Fixture {
        files: TABLE.to_vec(),
        links: links.to_vec(),
        include: include.to_string(),
        exclude: None,
    };
    let cases = [
        (
            linked(&[("sub/up", LinkTarget::Root)], "sub/*/*.fs"),
            "SymlinkedDirectory",
        ),
        (
            linked(&[("sub/upper", LinkTarget::RootUpper)], "sub/*/*.fs"),
            "SymlinkedDirectory",
        ),
        (
            linked(&[("lk", LinkTarget::Sub)], "lk/*.fs"),
            "SymlinkedDirectory",
        ),
        (
            linked(&[("sub/out", LinkTarget::Outside)], "**/*.fs"),
            "SymlinkedDirectory",
        ),
        (
            linked(&[("sub/up", LinkTarget::Root)], "**/*.fs"),
            "SymlinkCycle",
        ),
    ];
    for (fixture, reason) in &cases {
        assert_eq!(
            check(&mut oracles, fixture),
            Outcome::ResolverDeclined(reason.to_string()),
            "links: {:?}\n{}",
            fixture.links,
            fixture.xml(ROOT_UPPER)
        );
    }
    for fixture in [
        linked(&[("sub/up", LinkTarget::Root)], "*.fs;sub/*.fs"),
        linked(&[("sub/out", LinkTarget::Outside)], "sub/**/*.fsi"),
    ] {
        assert_eq!(
            check(&mut oracles, &fixture),
            Outcome::Committed,
            "links: {:?}\n{}",
            fixture.links,
            fixture.xml(ROOT_UPPER)
        );
    }
}

/// Files on every disk of the walk sweep: names `*.*` reads differently from
/// a regular expression (`ab`, `x`), a directory named like a file (`x.y`),
/// directories a `?` can stand for, and a directory name met at two depths.
const WALK_FILES: &[&str] = &[
    "a.fs",
    "ab",
    "b.fs",
    "sub/a.fs",
    "sub/ab",
    "sub/Deep/a.fs",
    "sub/Deep/d.fs",
    "sub/Deep/deep/x",
    "sub/a/b.fs",
    "sub/x.y/a.fs",
    "sub/s/a.fs",
    "q/x/a/b.fs",
];

/// Entries each walk disk holds a random selection of.
const WALK_EXTRAS: &[&str] = &[
    "sub/Deep/a/b.fs",
    "sub/Deep/ab",
    "sub/a/x",
    "x",
    "../out/a.fs",
    "../out/sub/b.fs",
];

/// A walk spec's fixed directory: none, the base directories, `..` and `.`
/// segments (which the file matcher keeps by spelling), and rooted ones.
const WALK_FIXED: &[&str] = &[
    "",
    "",
    "",
    "sub",
    "sub",
    "sub/Deep",
    "sub/a",
    "q",
    "..",
    "../proj",
    "../proj/sub",
    "../out",
    ".",
    "./sub",
    "sub/.",
    "$(MSBuildProjectDirectory)",
    "$(MSBuildProjectDirectory)/sub",
];

/// One segment of a walk spec's wildcard directory part.
const WALK_WILD_SEGMENT: &[&str] = &[
    "*", "*", "?", "**", "**", "**", ".", "sub", "Deep", "deep", "a", "s*", "?eep", "x.y", "*.*",
    "x",
];

/// A walk spec's file name.
const WALK_NAME: &[&str] = &[
    "*.*", "*.*", "a*.*", "?", "*.fs", "*.fs", "a?b.fs", "?.fs", "a.fs", "b.fs", "*", "**", "ab",
    "d.fs", "x", "*.*.*",
];

/// Where a walk exclude's fixed directory sits against its include's.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ExcludeBase {
    /// A strict ancestor of the include's fixed directory.
    Above,
    /// The include's fixed directory.
    At,
    /// A directory below the include's fixed directory.
    Below,
    /// Anywhere else.
    Elsewhere,
}

/// Wildcard directory parts of the `**/{name}/**` shape the file matcher
/// matches by directory name, drawn whole now and then.
const WALK_DIRECTORY_NAME_WILD: &[&str] = &[
    "**/Deep/**",
    "**/deep/**",
    "**/a/**",
    "**/**/**",
    "**/*.*/**",
    "**/s*/**",
    "**/?eep/**",
];

/// A wildcard directory part of up to three segments.
fn gen_walk_wild(rng: &mut SplitMix64) -> String {
    if rng.below(6) == 0 {
        return rng.pick(WALK_DIRECTORY_NAME_WILD).to_string();
    }
    let n = *rng.pick(&[0, 0, 1, 1, 1, 2, 2, 3]);
    (0..n)
        .map(|_| *rng.pick(WALK_WILD_SEGMENT))
        .collect::<Vec<_>>()
        .join("/")
}

/// A spec from its parts, empty parts dropped.
fn join_spec(parts: &[&str]) -> String {
    parts
        .iter()
        .copied()
        .filter(|p| !p.is_empty())
        .collect::<Vec<_>>()
        .join("/")
}

/// One walk fixture: an include from the walk grammar, and up to two excludes
/// whose fixed directories sit above, at, below or beside the include's, each
/// spelt as the include is anchored or the other way.
fn gen_walk_fixture(rng: &mut SplitMix64) -> (Fixture, Vec<ExcludeBase>) {
    let mut files = WALK_FILES.to_vec();
    files.extend(WALK_EXTRAS.iter().filter(|_| rng.below(3) == 0));
    let fixed = *rng.pick(WALK_FIXED);
    let include = join_spec(&[fixed, &gen_walk_wild(rng), rng.pick(WALK_NAME)]);
    // The include's fixed directory as segments below the project directory,
    // where it has a spelling there.
    let rooted = "$(MSBuildProjectDirectory)";
    let below_root: Option<Vec<&str>> = match fixed.strip_prefix(rooted) {
        Some(rest) => Some(rest.split('/').filter(|s| !s.is_empty()).collect()),
        None if fixed.starts_with("..") => None,
        None => Some(fixed.split('/').filter(|s| !s.is_empty()).collect()),
    };
    let mut relations = Vec::new();
    let mut excludes = Vec::new();
    for _ in 0..rng.below(3) {
        let (relation, base): (ExcludeBase, String) = match (rng.below(4), &below_root) {
            (0, Some(segs)) if !segs.is_empty() => {
                let keep = rng.below(segs.len());
                (ExcludeBase::Above, segs[..keep].join("/"))
            }
            (1, Some(segs)) => (ExcludeBase::At, segs.join("/")),
            (2, Some(segs)) => {
                let child = *rng.pick(&["Deep", "a", "x.y", "deep", "s"]);
                let mut segs = segs.clone();
                segs.push(child);
                (ExcludeBase::Below, segs.join("/"))
            }
            _ => (
                ExcludeBase::Elsewhere,
                rng.pick(&["q", "sub/Deep/deep", "../out", ""]).to_string(),
            ),
        };
        let anchored = if rng.below(4) == 0 && !base.starts_with("..") {
            join_spec(&[rooted, &base])
        } else {
            base
        };
        excludes.push(join_spec(&[
            &anchored,
            &gen_walk_wild(rng),
            rng.pick(WALK_NAME),
        ]));
        relations.push(relation);
    }
    let fixture = Fixture {
        files,
        links: Vec::new(),
        include,
        exclude: (!excludes.is_empty()).then(|| excludes.join(";")),
    };
    (fixture, relations)
}

/// The walk sweep: specs built from the file matcher's own grammar (fixed
/// directories, wildcard directory segments, file names, and excludes based
/// above, at and below the include's walk root), each held to both oracles
/// where the resolver commits. The census counts commits by exclude placement
/// and wildcard segment, so a decline that swallows one of them shows.
#[test]
fn generated_walk_shapes_are_certain_implies_exact() {
    walk_sweep(0x0960_0a1c_5eed, 1500);
}

/// The walk sweep's fresh-seed soak twin (see `common::soak_parameters`).
#[test]
#[ignore = "soak: a fresh seed each run"]
fn generated_walk_shapes_soak() {
    let (seed, cases) = common::soak_parameters("glob walk shapes", 5000);
    walk_sweep(seed, cases);
}

fn walk_sweep(seed: u64, cases: usize) {
    let mut oracles = oracles();
    let mut rng = SplitMix64(seed);
    let mut committed = 0usize;
    let mut committed_by_relation: BTreeMap<ExcludeBase, usize> = BTreeMap::new();
    let mut committed_by_segment: BTreeMap<&str, usize> = BTreeMap::new();
    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    let mut declined_outside_resolver = Vec::new();
    for _ in 0..cases {
        let (fixture, relations) = gen_walk_fixture(&mut rng);
        match check(&mut oracles, &fixture) {
            Outcome::Committed => {
                committed += 1;
                for relation in relations {
                    *committed_by_relation.entry(relation).or_default() += 1;
                }
                let specs = std::iter::once(fixture.include.as_str()).chain(
                    fixture
                        .exclude
                        .as_deref()
                        .into_iter()
                        .flat_map(|e| e.split(';')),
                );
                for spec in specs {
                    let mut segs: Vec<&str> = spec.split('/').collect();
                    segs.pop();
                    for seg in WALK_WILD_SEGMENT {
                        if segs.contains(seg) {
                            *committed_by_segment.entry(seg).or_default() += 1;
                        }
                    }
                }
            }
            Outcome::ResolverDeclined(reason) => *census.entry(reason).or_default() += 1,
            Outcome::Declined => declined_outside_resolver.push(fixture.xml(ROOT_UPPER)),
        }
    }
    eprintln!(
        "glob walk shapes: {committed}/{cases} committed; by exclude base: \
         {committed_by_relation:?}; by wildcard segment: {committed_by_segment:?}; \
         declines by reason: {census:?}"
    );
    assert!(
        declined_outside_resolver.is_empty(),
        "{} generated cases declined outside the resolver; the first:\n{}",
        declined_outside_resolver.len(),
        declined_outside_resolver[0]
    );
    assert!(
        committed * 100 >= cases * 90,
        "only {committed}/{cases} committed"
    );
    for relation in [
        ExcludeBase::Above,
        ExcludeBase::At,
        ExcludeBase::Below,
        ExcludeBase::Elsewhere,
    ] {
        let n = committed_by_relation.get(&relation).copied().unwrap_or(0);
        assert!(n >= 50, "{relation:?} committed {n} times");
    }
    for seg in WALK_WILD_SEGMENT {
        let n = committed_by_segment.get(seg).copied().unwrap_or(0);
        assert!(n >= 50, "`{seg}` committed {n} times");
    }
}

/// The sweep. Every case that commits is checked against both oracles; the
/// floors keep a decline-everything model from passing vacuously, and the
/// census says where the declines come from.
#[test]
fn generated_case_variants_are_certain_implies_exact() {
    sweep(0x0607_ca5e_d15c, 1500);
}

/// The sweep's fresh-seed soak twin (see `common::soak_parameters`).
#[test]
#[ignore = "soak: a fresh seed each run"]
fn generated_case_variants_soak() {
    let (seed, cases) = common::soak_parameters("glob case variants", 5000);
    sweep(seed, cases);
}

fn sweep(seed: u64, cases: usize) {
    let mut oracles = oracles();
    let mut rng = SplitMix64(seed);
    let mut links = SplitMix64(seed ^ 0x0959_11a5);
    // The floors measure the case dimension, over the disks without links;
    // the link dimension has its own.
    let (mut unlinked, mut committed, mut committed_upper) = (0usize, 0usize, 0usize);
    let (mut committed_linked, mut declined_through_link) = (0usize, 0usize);
    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    let mut declined_outside_resolver = Vec::new();
    for _ in 0..cases {
        let fixture = Fixture::generate(&mut rng, &mut links);
        let linked = !fixture.links.is_empty();
        unlinked += usize::from(!linked);
        match check(&mut oracles, &fixture) {
            Outcome::Committed if linked => committed_linked += 1,
            Outcome::Committed => {
                committed += 1;
                committed_upper += usize::from(fixture.spells_upper_case());
            }
            Outcome::ResolverDeclined(reason) => {
                declined_through_link += usize::from(reason == "SymlinkedDirectory");
                *census.entry(reason).or_default() += 1;
            }
            Outcome::Declined => declined_outside_resolver.push(fixture.xml(ROOT_UPPER)),
        }
    }
    eprintln!(
        "glob case variants: {committed}/{unlinked} committed without links ({committed_upper} \
         spelling upper case), {committed_linked}/{} with; declines by reason: {census:?}",
        cases - unlinked
    );
    assert!(
        declined_outside_resolver.is_empty(),
        "{} generated cases declined outside the resolver; the first:\n{}",
        declined_outside_resolver.len(),
        declined_outside_resolver[0]
    );
    // A link the glob selects nothing through costs nothing, and one it
    // selects through declines.
    assert!(
        committed_linked > 0 && declined_through_link > 0,
        "the link dimension committed {committed_linked} and declined through a link \
         {declined_through_link} times"
    );
    assert!(
        committed * 100 >= unlinked * 50,
        "only {committed}/{unlinked} committed"
    );
    assert!(
        committed_upper * 100 >= unlinked * 25,
        "only {committed_upper}/{unlinked} committed with an upper-case spelling"
    );
}
