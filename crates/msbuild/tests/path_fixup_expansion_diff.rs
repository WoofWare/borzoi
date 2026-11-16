//! Differential: MSBuild's Unix path fixup on expansion, generated over where a
//! backslash comes from, where it sits, and where the expansion is read.
//!
//! On a non-Windows host MSBuild passes each piece of an expansion (a literal
//! run, or what a `$(…)` reference returns) and then the whole expanded value
//! through `FileUtilities.MaybeAdjustFilePath`, which rewrites a piece's `\` as
//! `/` (collapsing runs of slashes) when the first segment of the rewrite is a
//! directory. Every property expansion does this, wherever the value came
//! from, so a value MSBuild stored without expanding it (a global, the
//! environment, a toolset or reserved name) keeps its `\` until it is read.
//! `MSBuildUserExtensionsPath` is one: `$(LocalAppData)` joined with
//! `Microsoft\MSBuild`.
//!
//! A segment named by an absolute path is probed under the root, so the
//! answer is a fact of the file system; one named relatively is probed under
//! MSBuild's working directory, which no evaluation the LSP serves knows. So
//! MSBuild is run from two working directories: `cwd-empty`, which holds none
//! of the generated relative segments, and `cwd-full`, which holds all of
//! them. The contract, for each name we commit in a served evaluation (no
//! startup directory), with imports or without:
//!
//! - **Exact where the working directory has no say**: it equals MSBuild's
//!   value from `cwd-empty`. The walk takes every relative probe of project
//!   text to miss (`docs/msbuild-unix-path-fixup-plan.md`'s deferred
//!   provenance dimension), which is the answer from a directory holding none
//!   of them.
//! - **No seed is guessed**: where MSBuild's value moves between the two
//!   directories, the document's own text holds a `\`. A movement that only a
//!   seed's backslash can cause must have been declined.
//!
//! The census counts, per source and read site, how many points we commit
//! and how many move with the working directory, and floors the commits a
//! source whose probes are absolute must reach.

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::{PropertyRead, parse_fsproj};
use common::{Oracle, SplitMix64};
use tempfile::TempDir;

/// Relative segments the generator writes, each a directory under
/// `cwd-full` and absent under `cwd-empty`.
const RELATIVE_SEGMENTS: &[&str] = &["seg", "obj"];

/// How many environment variables [`World`] sets, each to a generated value.
const ENVIRONMENT_VALUES: usize = 24;

/// The fixture: a canonical root, the two working directories (each with
/// its oracle child), the project's directory, and the environment variables
/// both sides read.
struct World {
    root: PathBuf,
    /// `cwd-empty`, then `cwd-full`.
    oracles: [Oracle; 2],
    /// `BorzoiEnv{i}` and its value, which MSBuild reads as a property.
    environment: Vec<(String, String)>,
    _tmp: TempDir,
}

impl World {
    fn new(seed: u64) -> World {
        let tmp = TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        let empty = root.join("cwd-empty");
        let full = root.join("cwd-full");
        std::fs::create_dir_all(&empty).unwrap();
        for segment in RELATIVE_SEGMENTS {
            std::fs::create_dir_all(full.join(segment)).unwrap();
        }
        std::fs::create_dir_all(root.join("proj")).unwrap();
        let mut rng = SplitMix64(seed ^ 0x5eed_e1f1_0000_0001);
        let root_text = root.to_str().unwrap().to_owned();
        let environment: Vec<(String, String)> = (0..ENVIRONMENT_VALUES)
            .map(|i| (format!("BorzoiEnv{i}"), gen_value(&mut rng, &root_text)))
            .collect();
        World {
            oracles: [
                Oracle::spawn_in_dir_with_env(&empty, &environment),
                Oracle::spawn_in_dir_with_env(&full, &environment),
            ],
            root,
            environment,
            _tmp: tmp,
        }
    }

    fn root_text(&self) -> &str {
        self.root.to_str().unwrap()
    }

    /// What our evaluator is handed as its environment: the oracle children's.
    fn our_environment(&self) -> HashMap<String, String> {
        let mut env = common::oracle_environment();
        env.extend(self.environment.iter().cloned());
        env
    }
}

/// Where the backslash-bearing value enters the expansion.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Source {
    /// Written inline in the read site: project text.
    Literal,
    /// Written to `V` by the document, then read as `$(V)`: project text that
    /// passed MSBuild's expander when it was stored.
    Written,
    /// A global `V`, read as `$(V)`: stored without expansion.
    Global,
    /// An environment variable, read as `$(BorzoiEnv{i})`: stored without
    /// expansion.
    Environment,
    /// The host's `MSBuildUserExtensionsPath`, a toolset name the environment
    /// supplies, whose value holds `Microsoft\MSBuild`.
    UserExtensions,
}

impl Source {
    const ALL: [Source; 5] = [
        Source::Literal,
        Source::Written,
        Source::Global,
        Source::Environment,
        Source::UserExtensions,
    ];

    /// Whether the source's value is generated, so that some of its probes
    /// are relative and decline, rather than the host's absolute path.
    fn generated(self) -> bool {
        !matches!(self, Source::UserExtensions)
    }
}

/// Where the expansion is read.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Site {
    /// A property body, read back as `P`.
    Body,
    /// A condition comparing the expansion with a candidate, read back as
    /// whether `C` was written.
    Condition,
    /// `Exists(…)` of the expansion, read back as whether `E` was written.
    Exists,
    /// A property function's argument, read back as `F`.
    Function,
}

impl Site {
    const ALL: [Site; 4] = [Site::Body, Site::Condition, Site::Exists, Site::Function];
}

/// One generated value: a first segment, then parts joined by separators.
fn gen_value(rng: &mut SplitMix64, root: &str) -> String {
    let prefixes: Vec<String> = vec![
        root.to_owned(),
        "/borzoi-missing".into(),
        "seg".into(),
        "obj".into(),
        ".".into(),
        "..".into(),
        String::new(),
        r"\\srv".into(),
        r"\tmp".into(),
        r"\borzoi-missing".into(),
        "a".into(),
    ];
    const SEPARATORS: &[&str] = &["\\", "/", "\\\\", "\\/", "%5c"];
    const PARTS: &[&str] = &["a", "seg", "..", "b c"];
    let mut value = rng.pick(&prefixes).clone();
    for _ in 0..rng.below(4) {
        value.push_str(rng.pick(SEPARATORS));
        value.push_str(rng.pick(PARTS));
    }
    if rng.below(3) == 0 {
        value.push_str(rng.pick(SEPARATORS));
    }
    value
}

/// Templates a read site composes the value into: `{v}` stands for the
/// value's reference (or, for [`Source::Literal`], the value itself).
const TEMPLATES: &[&str] = &[
    "{v}",
    "x{v}",
    "{v}\\y",
    "{v}/y",
    "[{v}]",
    "{v}{v}",
    "$(Empty){v}",
    "\\{v}",
    "'{v}'",
];

/// XML text for a property body.
fn xml_body(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;")
}

/// XML text for an attribute value.
fn xml_attribute(text: &str) -> String {
    xml_body(text).replace('"', "&quot;")
}

/// One point: its document, globals, project path, the names read back, and
/// whether the document's own text holds a `\`.
struct Point {
    source: Source,
    site: Site,
    xml: String,
    globals: Vec<(String, String)>,
    project: PathBuf,
    name: &'static str,
    /// The value the source supplies, for failure messages.
    value: String,
}

fn gen_point(rng: &mut SplitMix64, world: &World, source: Source, site: Site) -> Point {
    let (value, reference) = match source {
        Source::Literal => {
            let value = gen_value(rng, world.root_text());
            (value.clone(), value)
        }
        Source::Written | Source::Global => (gen_value(rng, world.root_text()), "$(V)".to_owned()),
        Source::Environment => {
            let (name, value) = rng.pick(&world.environment);
            (value.clone(), format!("$({name})"))
        }
        Source::UserExtensions => (
            common::oracle_environment()["MSBuildUserExtensionsPath"].clone(),
            "$(MSBuildUserExtensionsPath)".to_owned(),
        ),
    };
    let template = *rng.pick(TEMPLATES);
    let expansion = template.replace("{v}", &reference);
    let mut writes = String::new();
    if source == Source::Written {
        writes.push_str(&format!("    <V>{}</V>\n", xml_body(&value)));
    }
    let name = match site {
        Site::Body => {
            writes.push_str(&format!("    <P>{}</P>\n", xml_body(&expansion)));
            "P"
        }
        Site::Condition => {
            // Compare with one spelling MSBuild may produce: the template
            // around the value as written, or the same with every `\` a `/`.
            let literal = template.replace("{v}", &value);
            let candidate = if rng.below(2) == 0 {
                literal
            } else {
                literal.replace('\\', "/")
            };
            let condition = format!("'{expansion}' == '{candidate}'");
            writes.push_str(&format!(
                "    <C Condition=\"{}\">hit</C>\n",
                xml_attribute(&condition)
            ));
            "C"
        }
        Site::Exists => {
            let condition = format!("Exists('{expansion}')");
            writes.push_str(&format!(
                "    <E Condition=\"{}\">hit</E>\n",
                xml_attribute(&condition)
            ));
            "E"
        }
        Site::Function => {
            let function = if rng.below(2) == 0 {
                format!("$([System.IO.Path]::Combine('{expansion}', 'z'))")
            } else {
                format!("$([System.String]::Concat('{expansion}', 'q'))")
            };
            writes.push_str(&format!("    <F>{}</F>\n", xml_body(&function)));
            "F"
        }
    };
    let xml = format!("<Project>\n  <PropertyGroup>\n{writes}  </PropertyGroup>\n</Project>\n");
    let globals = if source == Source::Global {
        vec![("V".to_owned(), value.clone())]
    } else {
        Vec::new()
    };
    let project = world.root.join("proj").join("Demo.fsproj");
    Point {
        source,
        site,
        xml,
        globals,
        project,
        name,
        value,
    }
}

/// What one of our evaluations claims about `name`: `Some(value)` when it
/// commits (the empty string for a name it holds unset in the real build too).
fn claim(read: &PropertyRead) -> Option<String> {
    match read {
        PropertyRead::Value(value) => Some(value.clone()),
        PropertyRead::Unset => Some(String::new()),
        PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
    }
}

#[derive(Default)]
struct Census {
    points: usize,
    committed: usize,
    moved: usize,
    moved_committed: usize,
}

/// Evaluate `point` on both sides and hold every claim to the contract,
/// returning (whether the served with-imports evaluation committed, whether
/// MSBuild's value moved with the working directory).
fn check(world: &mut World, point: &Point) -> (bool, bool) {
    let names = vec![point.name.to_owned()];
    let theirs: Vec<Option<String>> = world
        .oracles
        .iter_mut()
        .map(|oracle| {
            oracle
                .project(&point.xml, &names, Some(&point.project), &point.globals)
                .map(|values| values.get(point.name).cloned().unwrap_or_default())
        })
        .collect();
    let extra: HashMap<String, String> = point.globals.iter().cloned().collect();
    let env = world.our_environment();
    let with_imports =
        parse_fsproj_with_imports(&point.xml, &point.project, &extra, &env, None, None).ok();
    let pure = parse_fsproj(&point.xml, &point.project, &extra, &env).ok();
    let moved = theirs[0] != theirs[1];
    let own_backslash = point.xml.contains('\\');
    let mut served_committed = false;
    for (mode, parsed) in [("with imports", &with_imports), ("pure", &pure)] {
        let Some(parsed) = parsed else { continue };
        let Some(ours) = claim(&parsed.property(point.name)) else {
            continue;
        };
        if mode == "with imports" {
            served_committed = true;
        }
        let context = || {
            format!(
                "{mode}, {:?} at {:?}, ${}\nsource value: {:?}\nglobals: {:?}\nproject: {}\n--- xml ---\n{}",
                point.source,
                point.site,
                point.name,
                point.value,
                point.globals,
                point.project.display(),
                point.xml
            )
        };
        let Some(empty) = &theirs[0] else {
            panic!(
                "MSBuild rejects the document from cwd-empty, but we commit {ours:?}\n{}",
                context()
            );
        };
        assert_eq!(
            &ours,
            empty,
            "certain-implies-exact violated against MSBuild from cwd-empty (ours left)\n{}",
            context()
        );
        assert!(
            !moved || own_backslash,
            "MSBuild's value moves with its working directory ({:?} from cwd-full), and only a \
             seed holds a backslash, but we commit {ours:?}\n{}",
            theirs[1],
            context()
        );
    }
    (served_committed, moved)
}

/// The issue's shape, pinned on its own: the host's
/// `MSBuildUserExtensionsPath`, read into a body, commits MSBuild's value.
#[test]
fn the_user_extensions_path_read_into_a_body_commits_msbuilds_value() {
    let mut world = World::new(0);
    for template in ["{v}", "x{v}", "[{v}]", "{v}\\y", "{v}/y"] {
        let body = template.replace("{v}", "$(MSBuildUserExtensionsPath)");
        let point = Point {
            source: Source::UserExtensions,
            site: Site::Body,
            xml: format!(
                "<Project>\n  <PropertyGroup>\n    <P>{}</P>\n  </PropertyGroup>\n</Project>\n",
                xml_body(&body)
            ),
            globals: Vec::new(),
            project: world.root.join("proj").join("Demo.fsproj"),
            name: "P",
            value: common::oracle_environment()["MSBuildUserExtensionsPath"].clone(),
        };
        let (committed, moved) = check(&mut world, &point);
        assert!(committed, "{body}: the walk must commit\n{}", point.xml);
        assert!(!moved, "{body}: MSBuild's value is a fact of the root");
    }
}

/// The generated sweep over sources, read sites and values.
#[test]
fn expansions_hold_msbuilds_path_fixup() {
    let (seed, cases) = common::soak_parameters("BORZOI_PATH_FIXUP_EXPANSION", 600);
    let mut rng = SplitMix64(seed);
    let mut world = World::new(seed);
    let mut census: BTreeMap<(Source, Site), Census> = BTreeMap::new();
    for case in 0..cases {
        let source = Source::ALL[case % Source::ALL.len()];
        let site = *rng.pick(&Site::ALL);
        let point = gen_point(&mut rng, &world, source, site);
        let (committed, moved) = check(&mut world, &point);
        let entry = census.entry((source, site)).or_default();
        entry.points += 1;
        entry.committed += usize::from(committed);
        entry.moved += usize::from(moved);
        entry.moved_committed += usize::from(moved && committed);
    }
    eprintln!("source / site: points, committed, moved, moved and committed");
    for ((source, site), entry) in &census {
        eprintln!(
            "  {source:?} / {site:?}: {}, {}, {}, {}",
            entry.points, entry.committed, entry.moved, entry.moved_committed
        );
    }
    // Anti-vacuity: each source commits somewhere, and the seeds whose probes
    // are absolute commit at most sites. A walk that declined every backslash
    // would pass the contract.
    for source in Source::ALL {
        let (points, committed): (usize, usize) = census
            .iter()
            .filter(|((s, _), _)| *s == source)
            .fold((0, 0), |(p, c), (_, e)| (p + e.points, c + e.committed));
        let floor = if source.generated() {
            points / 4
        } else {
            points / 2
        };
        assert!(
            committed >= floor,
            "{source:?}: {committed} of {points} points committed, below {floor}"
        );
    }
    let moved: usize = census.values().map(|e| e.moved).sum();
    assert!(moved > 0, "no point moved with the working directory");
}
