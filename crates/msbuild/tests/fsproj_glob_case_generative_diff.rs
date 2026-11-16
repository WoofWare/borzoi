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
//! The rule is modelled on Linux alone (`glob_resolver`); elsewhere a glob
//! include declines wherever case would decide it, which this harness then
//! checks the same way.
//!
//! Inputs are a fixed-seed sweep, so a failure reproduces exactly.

mod common;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::{DiagnosticKind, GlobDecline, glob_resolver};
use common::{Oracle, SplitMix64};
use std::collections::{BTreeMap, HashMap};

/// Whether the resolver models the file matcher's case rule on this host.
const MODELLED: bool = cfg!(target_os = "linux");

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
    "A*.*", "a?b.fs",
];

/// Non-ASCII file names, outside the allow-list, drawn now and then.
const RARE_NAME: &[&str] = &["\u{e9}.fs", "\u{c9}.fs"];

fn gen_fragment(rng: &mut SplitMix64) -> String {
    let fixed = if rng.below(8) == 0 {
        rng.pick(RARE_FIXED)
    } else {
        rng.pick(FIXED)
    };
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

fn gen_spec(rng: &mut SplitMix64) -> String {
    (0..1 + rng.below(2))
        .map(|_| gen_fragment(rng))
        .collect::<Vec<_>>()
        .join(";")
}

struct Fixture {
    files: Vec<&'static str>,
    include: String,
    exclude: Option<String>,
}

impl Fixture {
    fn generate(rng: &mut SplitMix64) -> Fixture {
        let mut files = BASE_FILES.to_vec();
        files.extend(EXTRAS.iter().filter(|_| rng.below(4) == 0));
        if rng.below(6) == 0 {
            files.push(rng.pick(NON_ASCII));
        }
        Fixture {
            files,
            include: gen_spec(rng),
            exclude: (rng.below(3) != 0).then(|| gen_spec(rng)),
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
            "certain-implies-exact violated under the {culture} culture.\ndisk: {:?}\nproject:\n{xml}",
            fixture.files
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
/// culture-dependent ones. On Linux every modelled corner must commit, and
/// each culture or working-directory corner must decline by name.
#[test]
fn case_corners() {
    let mut oracles = oracles();
    const TABLE: &[&str] = &["a.fs", "b.fs", "sub/a.fs"];
    let corner = |files: &[&'static str], include: &str, exclude: Option<&str>| Fixture {
        files: files.to_vec(),
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
        // `i` and `I` where no regular expression compares them.
        corner(&["sub/x/bi.fs"], "**/*.fs", Some("**/BI.fs")),
        corner(&["sub/x/bi.fs"], "sub/x/*.fs", Some("sub/x/BI.fs")),
    ];
    for fixture in &committing {
        let outcome = check(&mut oracles, fixture);
        if MODELLED {
            assert_eq!(
                outcome,
                Outcome::Committed,
                "a case corner did not commit:\ndisk: {:?}\n{}",
                fixture.files,
                fixture.xml(ROOT_UPPER)
            );
        } else {
            assert_ne!(outcome, Outcome::Declined, "{}", fixture.xml(ROOT_UPPER));
        }
    }
    let declining = [
        // The directory a `**/**/**` exclude needs is above the include's
        // walk root, which MSBuild never matches against it.
        (
            corner(&["sub/x/b.fs"], "sub/x/*.fs", Some("**/**/**")),
            "GlobstarExcludeAboveIncludeRoot",
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
        assert_ne!(outcome, Outcome::Declined, "{}", fixture.xml(ROOT_UPPER));
        if MODELLED {
            assert_eq!(
                outcome,
                Outcome::ResolverDeclined(reason.to_string()),
                "disk: {:?}\n{}",
                fixture.files,
                fixture.xml(ROOT_UPPER)
            );
        }
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
    let mut committed = 0usize;
    let mut committed_upper = 0usize;
    let mut census: BTreeMap<String, usize> = BTreeMap::new();
    let mut declined_outside_resolver = Vec::new();
    for _ in 0..cases {
        let fixture = Fixture::generate(&mut rng);
        match check(&mut oracles, &fixture) {
            Outcome::Committed => {
                committed += 1;
                committed_upper += usize::from(fixture.spells_upper_case());
            }
            Outcome::ResolverDeclined(reason) => *census.entry(reason).or_default() += 1,
            Outcome::Declined => declined_outside_resolver.push(fixture.xml(ROOT_UPPER)),
        }
    }
    eprintln!(
        "glob case variants: {committed}/{cases} committed ({committed_upper} spelling upper \
         case); declines by reason: {census:?}"
    );
    assert!(
        declined_outside_resolver.is_empty(),
        "{} generated cases declined outside the resolver; the first:\n{}",
        declined_outside_resolver.len(),
        declined_outside_resolver[0]
    );
    if MODELLED {
        assert!(
            committed * 100 >= cases * 50,
            "only {committed}/{cases} committed"
        );
        assert!(
            committed_upper * 100 >= cases * 25,
            "only {committed_upper}/{cases} committed with an upper-case spelling"
        );
    }
}
