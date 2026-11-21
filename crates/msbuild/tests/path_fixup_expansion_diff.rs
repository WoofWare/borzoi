//! Differential: MSBuild's Unix path fixup on expansion, generated over where a
//! backslash comes from, where it sits, and where the expansion is read, with
//! MSBuild started from several working directories.
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
//! answer is a fact of the file system. One named relatively is probed under
//! MSBuild's startup directory (its working directory), for the entry project
//! and every project it builds alike. No evaluation the LSP serves knows that
//! directory; the restore cone's does. So each project is evaluated by MSBuild
//! started from three directories: its own directory, an unrelated directory
//! holding none of the generated relative segments (`cwd-empty`), one
//! holding all of them (`cwd-full`), and one holding each alone (`cwd-seg`,
//! `cwd-obj`), since each segment is its own question. There are two projects:
//! `proj-full`,
//! whose directory holds the segments (a restored project's `obj/`), and
//! `proj-empty`, whose directory holds none. The contract, for each value we
//! commit:
//!
//! - **Served** (no startup directory), with imports or without: it equals
//!   MSBuild's value from **every** working directory. A value that moves with
//!   the working directory must be declined, whatever text holds the
//!   backslash.
//! - **Supplied** (the startup directory given, as the restore cone gives it):
//!   it equals MSBuild's value from that directory.
//!
//! The walk does not meet that contract yet (#993): it takes a relative probe
//! of project text to miss, which is MSBuild's answer from a directory holding
//! none of the segments, so it commits a value that moves with the working
//! directory, the SDK's own `obj\` among them. Two gates therefore stand on
//! it:
//!
//! - **The fixed-seed sweep**
//!   ([`fixed_seed_sweep_regresses_nothing_main_answers`]) draws every site
//!   and holds each claim to the whole contract. A wrong claim the baseline
//!   walk (`main`'s, recorded by `tools/path-fixup-baseline.sh`) shares is
//!   pinned, point by point, in `tests/manifests/path_fixup_pins.txt`; any
//!   other wrong claim fails it.
//! - **The fresh-seed soak** ([`expansions_hold_msbuilds_path_fixup`]) holds
//!   each claim to the part of the contract the walk meets: MSBuild's value
//!   from the starts that hold no segment ([`Start::all_absent`]), and no
//!   commit where MSBuild's value moves while only a seed holds a backslash
//!   ([`check_all_absent`]).
//!
//! The values are read in property bodies, conditions (on a value read
//! inline, or through properties that copy it), `Exists`, property functions
//! and `Compile` item includes. The census counts, per source and read site,
//! how many points each side commits and how many move with the working
//! directory, and floors the commits, so a walk that declined every backslash
//! cannot pass. `sdk_output_paths_moved_by_the_startup_directory_are_pinned`
//! holds the SDK's own `obj\` and `bin\` to the whole contract and pins what
//! the walk gets wrong there.

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::{EvaluationReads, ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{
    GlobResolver, ItemKind, ParsedProject, PropertyRead, glob_resolver, parse_fsproj, resolve_sdk,
    workloads,
};
use borzoi_oracle_harness::manifest::{self, Manifest};
use common::{Oracle, SplitMix64};
use tempfile::TempDir;

/// The fixture's working directories, in [`World::starts`] order, and the
/// relative segments the generator writes (`seg`, `obj`) each holds as a
/// directory. `path_fixup_baseline.rs` lays out the same table, and both
/// hash it into every point's key ([`layout_text`]).
const STARTS: [(&str, &[&str]); 6] = [
    ("cwd-empty", &[]),
    ("cwd-full", &["seg", "obj"]),
    ("cwd-seg", &["seg"]),
    ("cwd-obj", &["obj"]),
    ("proj-full", &["seg", "obj"]),
    ("proj-empty", &[]),
];

/// Files under `proj-full`'s segments, for the `Compile` globs to find.
const ITEM_FILES: &[&str] = &["seg/a.fs", "seg/b c.fs", "obj/a.fs"];

/// How many environment variables [`World`] sets, each to a generated value.
const ENVIRONMENT_VALUES: usize = 24;

/// One directory MSBuild is started from, with the oracle child running there.
struct Start {
    label: &'static str,
    dir: PathBuf,
    /// Whether the directory holds none of the generated segments: the start
    /// whose answer the walk assumes for every relative probe.
    all_absent: bool,
    oracle: Oracle,
}

/// The fixture on disk: a canonical root holding [`STARTS`]' directories and
/// the projects' files, and the environment variables both sides read.
struct Fixture {
    root: PathBuf,
    /// `BorzoiEnv{i}` and its value, which MSBuild reads as a property.
    environment: Vec<(String, String)>,
    _tmp: TempDir,
}

/// The [`Fixture`], with an oracle child started in each of its working
/// directories.
struct World {
    fixture: Fixture,
    /// `cwd-empty`, `cwd-full`, `cwd-seg`, `cwd-obj`, `proj-full`,
    /// `proj-empty`.
    starts: Vec<Start>,
}

/// The two projects, each with the indices into [`World::starts`] of the
/// directories MSBuild evaluates it from: the four unrelated ones and its own.
const PROJECTS: [(&str, [usize; 5]); 2] = [
    ("proj-full", [0, 1, 2, 3, 4]),
    ("proj-empty", [0, 1, 2, 3, 5]),
];

/// The fixture's layout as text: each start's directory and the segments it
/// holds, the files under `proj-full` and beside each project, and each
/// project's starts. Hashed into every point's key ([`point_fingerprint`]),
/// as `path_fixup_baseline.rs` hashes its own table, so that a layout the
/// two files lay out apart keys no point alike.
fn layout_text() -> String {
    let mut text = String::new();
    for (dir, segments) in STARTS {
        text.push_str(&format!("dir\t{dir}\t{}\n", segments.join(",")));
    }
    for file in ITEM_FILES {
        text.push_str(&format!("file\tproj-full/{file}\n"));
    }
    for (project, starts) in PROJECTS {
        let labels: Vec<&str> = starts.iter().map(|&start| STARTS[start].0).collect();
        text.push_str(&format!("file\t{project}/a.fs\n"));
        text.push_str(&format!("project\t{project}\t{}\n", labels.join(",")));
    }
    text
}

impl Fixture {
    /// The fixture for `seed`, in a new temporary directory under `parent`.
    fn new(seed: u64, parent: &std::path::Path) -> Fixture {
        let tmp = tempfile::Builder::new().tempdir_in(parent).unwrap();
        // The root sits one level inside the temporary directory, so that a
        // value climbing out of it names a directory unique to this run, not
        // the host's temporary directory, whose spelling a generated literal
        // may share ([`placeholder`]).
        let root = host_fs::canonicalize(tmp.path()).unwrap().join("fixture");
        std::fs::create_dir(&root).unwrap();
        for (dir, segments) in STARTS {
            std::fs::create_dir_all(root.join(dir)).unwrap();
            for segment in segments {
                std::fs::create_dir_all(root.join(dir).join(segment)).unwrap();
            }
        }
        // What the `Compile` globs find: files under the segments of
        // `proj-full`, and beside both projects.
        for file in ITEM_FILES {
            std::fs::write(root.join("proj-full").join(file), "").unwrap();
        }
        for (dir, _) in PROJECTS {
            std::fs::write(root.join(dir).join("a.fs"), "").unwrap();
        }
        let mut rng = SplitMix64(seed ^ 0x5eed_e1f1_0000_0001);
        let root_text = root.to_str().unwrap().to_owned();
        let environment: Vec<(String, String)> = (0..ENVIRONMENT_VALUES)
            .map(|i| (format!("BorzoiEnv{i}"), gen_value(&mut rng, &root_text)))
            .collect();
        Fixture {
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

impl World {
    fn new(seed: u64) -> World {
        let fixture = Fixture::new(seed, &fixture_parent());
        let starts = STARTS
            .into_iter()
            .map(|(label, segments)| {
                let dir = fixture.root.join(label);
                Start {
                    label,
                    oracle: Oracle::spawn_in_dir_with_env(&dir, &fixture.environment),
                    all_absent: segments.is_empty(),
                    dir,
                }
            })
            .collect();
        World { fixture, starts }
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
    /// Written to `V`, copied into `W` through a template, and read as `$(W)`:
    /// a value that met the expander twice before the read.
    Copied,
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
    const ALL: [Source; 6] = [
        Source::Literal,
        Source::Written,
        Source::Copied,
        Source::Global,
        Source::Environment,
        Source::UserExtensions,
    ];

    /// Whether the source's value is generated, so that some of its probes
    /// are relative and turn on the working directory, rather than the host's
    /// absolute path.
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
    /// A `Compile` item's `Include`, read back as the items' full paths.
    Item,
    /// A generic item's `Include`, beside another item and perhaps a `Remove`,
    /// read back as the list's identities, as spelled: what an item table, an
    /// `@(Foo)`, hands on.
    Identity,
    /// An indexer into the expansion's split on `/`: past the end in some
    /// worlds, MSBuild throws there. Read back as `After`, written last and
    /// unconditionally, which a project MSBuild rejects publishes nothing of.
    Index,
    /// The expansion coerced to a boolean by a later group's condition:
    /// MSBuild throws on a value that is no boolean. Read back as `After`.
    Coerce,
    /// A write of a non-boolean under a condition comparing the expansion, as
    /// [`Site::Condition`] does, then that name coerced by a later group's
    /// condition: MSBuild throws where the write ran. Read back as `After`.
    Gate,
}

impl Site {
    const ALL: [Site; 9] = [
        Site::Body,
        Site::Condition,
        Site::Exists,
        Site::Function,
        Site::Item,
        Site::Identity,
        Site::Index,
        Site::Coerce,
        Site::Gate,
    ];

    /// The sites the fresh-seed soak draws: those where the walk answers no
    /// point wrongly. The rejection-shaped ones ([`Site::Index`],
    /// [`Site::Coerce`], [`Site::Gate`]) meet wrong answers `main` shares
    /// (#1097), which only the fixed-seed sweep, holding the walk to a
    /// baseline, can tell from new ones.
    const SOAKED: [Site; 6] = [
        Site::Body,
        Site::Condition,
        Site::Exists,
        Site::Function,
        Site::Item,
        Site::Identity,
    ];
}

/// Relative paths spliced before an indexer so that the computation asks
/// about more of the startup directory than the walk enumerates
/// (`properties::worlds::MAX_SEGMENTS`, six, plus one).
const UNENUMERATED_SPLICES: usize = 7;

/// The last write of a rejection-shaped point: unconditional, so the walk
/// publishes it exactly where it claims MSBuild accepts the project.
const AFTER: &str = "  </PropertyGroup>\n  <PropertyGroup>\n    <After>ok</After>\n";

/// A generated value for `site`: for an indexer, half the time a relative
/// segment joined to a part by a `\`, whose respelling moves the value's
/// fields; otherwise [`gen_value`]'s.
fn gen_site_value(rng: &mut SplitMix64, root: &str, site: Site) -> String {
    if site == Site::Index && rng.below(2) == 0 {
        let segment = *rng.pick(&["seg", "obj"]);
        let separator = *rng.pick(&["\\", "%5c"]);
        let part = *rng.pick(&["a", "seg", "..", "b c"]);
        format!("{segment}{separator}{part}")
    } else {
        gen_value(rng, root)
    }
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
    "{v};seg\\z",
    // A whole value whose first segment always exists, so its own pass
    // respells it, collapsing the run, only where a piece kept a `\`.
    "./{v}//q",
];

/// XML text for a property body.
fn xml_body(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;")
}

/// XML text for an attribute value.
fn xml_attribute(text: &str) -> String {
    xml_body(text).replace('"', "&quot;")
}

/// What one point reads back.
#[derive(Clone, Copy, Debug)]
enum Read {
    /// The property of this name.
    Property(&'static str),
    /// The `Compile` items' full paths.
    Items,
    /// The `Foo` items' identities.
    Identities,
}

/// One point: its document, globals, project, what it reads back, and the
/// value its source supplies.
struct Point {
    source: Source,
    site: Site,
    xml: String,
    globals: Vec<(String, String)>,
    project: PathBuf,
    /// Indices into [`World::starts`] MSBuild evaluates the project from.
    starts: [usize; 5],
    read: Read,
    /// The value the source supplies, for failure messages.
    value: String,
}

fn gen_point(
    rng: &mut SplitMix64,
    fixture: &Fixture,
    source: Source,
    site: Site,
    project: usize,
) -> Point {
    let (value, reference) = match source {
        Source::Literal => {
            let value = gen_site_value(rng, fixture.root_text(), site);
            (value.clone(), value)
        }
        Source::Written | Source::Global => (
            gen_site_value(rng, fixture.root_text(), site),
            "$(V)".to_owned(),
        ),
        Source::Copied => (
            gen_site_value(rng, fixture.root_text(), site),
            "$(W)".to_owned(),
        ),
        Source::Environment => {
            let (name, value) = rng.pick(&fixture.environment);
            (value.clone(), format!("$({name})"))
        }
        Source::UserExtensions => (
            common::oracle_environment()["MSBuildUserExtensionsPath"].clone(),
            "$(MSBuildUserExtensionsPath)".to_owned(),
        ),
    };
    // An indexer reads past the end in one world most often under a whole
    // value whose pass respells a kept `\` (`./{v}//q`).
    let template = if site == Site::Index && rng.below(2) == 0 {
        "./{v}//q"
    } else {
        *rng.pick(TEMPLATES)
    };
    let expansion = template.replace("{v}", &reference);
    let mut writes = String::new();
    let mut items = String::new();
    if matches!(source, Source::Written | Source::Copied) {
        writes.push_str(&format!("    <V>{}</V>\n", xml_body(&value)));
    }
    let copy_template = (source == Source::Copied).then(|| *rng.pick(TEMPLATES));
    if let Some(copy_template) = copy_template {
        let copy = copy_template.replace("{v}", "$(V)");
        writes.push_str(&format!("    <W>{}</W>\n", xml_body(&copy)));
    }
    let read = match site {
        Site::Body => {
            writes.push_str(&format!("    <P>{}</P>\n", xml_body(&expansion)));
            Read::Property("P")
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
            Read::Property("C")
        }
        Site::Exists => {
            let condition = format!("Exists('{expansion}')");
            writes.push_str(&format!(
                "    <E Condition=\"{}\">hit</E>\n",
                xml_attribute(&condition)
            ));
            Read::Property("E")
        }
        Site::Index => {
            writes.push_str(&format!("    <X>{}</X>\n", xml_body(&expansion)));
            // Half the time, at the edge of the value's fields as written: the
            // world that keeps every `\` has that many, and one that respells
            // a `\` has more, so the indexer is past the end in some worlds.
            // Counted with the fixture's root one segment, so that the index,
            // which the document spells, is the same on every host.
            let index = if rng.below(2) == 0 {
                rng.below(6)
            } else {
                let fields = template
                    .replace("{v}", &value)
                    .replace(fixture.root_text(), "{ROOT}")
                    .split('/')
                    .count();
                fields - 1 + rng.below(3)
            };
            // Beside a name the walk holds no value of (`U`, through a
            // function it does not model), read after the indexer, before
            // it, or beside more relative paths than the walk enumerates:
            // MSBuild may throw at the indexer in one world without reading
            // `U`, which the walk must not let `U` hide.
            let body = match rng.below(4) {
                0 => format!("$(X.Split('/')[{index}])"),
                unheld => {
                    writes.push_str("    <U>$([System.IO.Path]::GetFileName('x'))</U>\n");
                    match unheld {
                        1 => format!("$(X.Split('/')[{index}].Split('z$(U)')[1])"),
                        2 => format!("$(X.TrimStart('z$(U)').Split('/')[{index}])"),
                        _ => {
                            let splices: String = (0..UNENUMERATED_SPLICES)
                                .map(|i| format!("s{i}\\x$(Empty)"))
                                .collect();
                            format!("{splices}$(U.Substring(5))$(X.Split('/')[{index}])")
                        }
                    }
                }
            };
            writes.push_str(&format!("    <F>{}</F>\n", xml_body(&body)));
            writes.push_str(AFTER);
            Read::Property("After")
        }
        Site::Coerce => {
            writes.push_str(&format!("    <X>{}</X>\n", xml_body(&expansion)));
            writes.push_str(
                "  </PropertyGroup>\n  <PropertyGroup Condition=\"'$(X)' == '' Or $(X)\">\n    <C>hit</C>\n",
            );
            writes.push_str(AFTER);
            Read::Property("After")
        }
        Site::Gate => {
            let literal = template.replace("{v}", &value);
            let candidate = if rng.below(2) == 0 {
                literal
            } else {
                literal.replace('\\', "/")
            };
            let condition = format!("'{expansion}' == '{candidate}'");
            writes.push_str("    <X>true</X>\n");
            writes.push_str(&format!(
                "    <X Condition=\"{}\">bad</X>\n",
                xml_attribute(&condition)
            ));
            writes.push_str(
                "  </PropertyGroup>\n  <PropertyGroup Condition=\"$(X)\">\n    <C>hit</C>\n",
            );
            writes.push_str(AFTER);
            Read::Property("After")
        }
        Site::Function => {
            let function = if rng.below(2) == 0 {
                format!("$([System.IO.Path]::Combine('{expansion}', 'z'))")
            } else {
                format!("$([System.String]::Concat('{expansion}', 'q'))")
            };
            writes.push_str(&format!("    <F>{}</F>\n", xml_body(&function)));
            Read::Property("F")
        }
        Site::Item => {
            // A file, a glob under the value, or the glob less one file. A
            // glob only under a value that stays inside the fixture: one that
            // is rooted, climbs, or is empty would list host directories
            // other tests write to.
            // Judged on the decoded value: `%5c` is a rooting `\`.
            let decoded = value
                .replace("%5c", "\\")
                .replace("%5C", "\\")
                .replace("%2f", "/")
                .replace("%2F", "/");
            let inside = source != Source::UserExtensions
                && !value.is_empty()
                && !decoded.contains("..")
                && !decoded.contains('%')
                && !decoded.starts_with(['/', '\\'])
                && !template.starts_with('\\')
                && copy_template.is_none_or(|copy| !copy.starts_with('\\'));
            let shape = if inside { rng.below(3) } else { 0 };
            let (include, exclude) = match shape {
                0 => (format!("{expansion}.fs"), None),
                1 => (format!("{expansion}\\*.fs"), None),
                _ => (
                    format!("{expansion}\\*.fs"),
                    Some(format!("{expansion}\\a.fs")),
                ),
            };
            let exclude = exclude
                .map(|exclude| format!(" Exclude=\"{}\"", xml_attribute(&exclude)))
                .unwrap_or_default();
            items.push_str(&format!(
                "  <ItemGroup>\n    <Compile Include=\"{}\"{exclude} />\n  </ItemGroup>\n",
                xml_attribute(&include)
            ));
            Read::Items
        }
        Site::Identity => {
            // The `Remove`: none, the same spelling, or one with every `\` the
            // expansion writes a `/`.
            let remove = match rng.below(3) {
                0 => String::new(),
                1 => format!("    <Foo Remove=\"{}\" />\n", xml_attribute(&expansion)),
                _ => format!(
                    "    <Foo Remove=\"{}\" />\n",
                    xml_attribute(&expansion.replace('\\', "/"))
                ),
            };
            items.push_str(&format!(
                "  <ItemGroup>\n    <Foo Include=\"{}\" />\n    <Foo Include=\"seg/q\" />\n{remove}  </ItemGroup>\n",
                xml_attribute(&expansion)
            ));
            Read::Identities
        }
    };
    let xml =
        format!("<Project>\n  <PropertyGroup>\n{writes}  </PropertyGroup>\n{items}</Project>\n");
    let globals = if source == Source::Global {
        vec![("V".to_owned(), value.clone())]
    } else {
        Vec::new()
    };
    let (dir, starts) = PROJECTS[project];
    Point {
        source,
        site,
        xml,
        globals,
        project: fixture.root.join(dir).join("Demo.fsproj"),
        starts,
        read,
        value,
    }
}

/// What one evaluation claims about the point, `None` where it declines.
/// A property claim is its value (the empty string for a name it holds unset
/// in the real build too); an item claim is the `Compile` items' full paths;
/// an identity claim is the `Foo` list where the walk reads it as exact.
fn claim(
    parsed: &ParsedProject,
    reads: Option<&EvaluationReads>,
    read: Read,
) -> Option<Vec<String>> {
    match read {
        Read::Identities => {
            let list = reads?.items.get("Foo")?;
            (list.exact && !list.tainted && !list.untracked && parsed.rejection.is_none())
                .then_some(list.items.as_ref())
                .flatten()
                .map(|rows| rows.iter().map(|row| row.identity.clone()).collect())
        }
        Read::Property(name) => match parsed.property(name) {
            PropertyRead::Value(value) => Some(vec![value]),
            PropertyRead::Unset => Some(vec![String::new()]),
            PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
        },
        Read::Items => (!parsed.items_uncertain && parsed.rejection.is_none()).then(|| {
            parsed
                .items
                .iter()
                .filter(|item| item.kind == ItemKind::Compile)
                .map(|item| item.include.to_string_lossy().into_owned())
                .collect()
        }),
    }
}

/// MSBuild's answer for the point from one start, `None` where it rejects the
/// document.
fn msbuild(start: &mut Start, point: &Point) -> Option<Vec<String>> {
    match point.read {
        Read::Property(name) => start
            .oracle
            .project(
                &point.xml,
                &[name.to_owned()],
                Some(&point.project),
                &point.globals,
            )
            .map(|values| vec![values.get(name).cloned().unwrap_or_default()]),
        Read::Items => start
            .oracle
            .items(&point.xml, &point.project, "Compile", &point.globals),
        // The `itemsMeta` op takes no globals; the sweep reads identities only
        // from sources that need none.
        Read::Identities => start
            .oracle
            .items_meta(&point.xml, &point.project, "Foo", &[])
            .map(|items| items.into_iter().map(|(identity, _)| identity).collect()),
    }
}

#[derive(Default)]
struct Census {
    points: usize,
    served: usize,
    moved: usize,
    supplied: usize,
    supplied_moved: usize,
}

/// One claim MSBuild contradicts.
struct Violation {
    /// The mode ([`MODES`], or `s:<start>` for a supplied startup directory).
    mode: String,
    /// The labels of the starts whose answer contradicts it.
    starts: Vec<&'static str>,
    /// The failure message, against the first of them.
    message: String,
}

/// What [`grade`] saw at one point.
struct Seen {
    /// Whether the served with-imports evaluation committed.
    served: bool,
    /// Whether MSBuild's answer moved with the working directory.
    moved: bool,
    /// How many of the five startup-supplied evaluations committed.
    supplied: usize,
    /// MSBuild's answer from each of the point's starts, `None` where it
    /// rejects the document.
    theirs: Vec<Option<Vec<String>>>,
    /// Each mode whose claim MSBuild contradicts from some start.
    violations: Vec<Violation>,
    /// The served modes that commit where MSBuild's answer moves while the
    /// document's own text holds no `\`, so that only a seed's can move it.
    seed_guesses: Vec<&'static str>,
}

/// The served modes, as the baseline names them.
const MODES: [&str; 3] = ["wi", "rd", "pu"];

/// [`grade`], holding every claim to the whole contract.
fn check(world: &mut World, point: &Point) -> Seen {
    let seen = grade(world, point);
    if let Some(violation) = seen.violations.first() {
        panic!("{}", violation.message);
    }
    seen
}

/// [`grade`], holding every claim to the part of the contract the walk meets
/// while it takes a relative probe of project text to miss (#993): MSBuild's
/// answer from each start that holds no segment ([`Start::all_absent`]), and
/// no served commit where MSBuild's answer moves while only a seed holds a
/// backslash. A claim only some other start contradicts is the fixed-seed
/// sweep's to pin.
fn check_all_absent(world: &mut World, point: &Point) -> Seen {
    let seen = grade(world, point);
    for violation in &seen.violations {
        let all_absent = violation.starts.iter().any(|label| {
            world
                .starts
                .iter()
                .any(|start| start.label == *label && start.all_absent)
        });
        if all_absent {
            panic!("{}", violation.message);
        }
    }
    if let Some(mode) = seen.seed_guesses.first() {
        panic!(
            "{mode}: MSBuild's value moves with its working directory ({:?}), and only a seed \
             holds a backslash, but we commit it\n{:?} at {:?}, source value {:?}\n--- xml ---\n{}",
            seen.theirs, point.source, point.site, point.value, point.xml
        );
    }
    seen
}

/// `claim` as one tab-free field: `-` where it declines (or MSBuild rejects),
/// else `=` and each value as `|` and its Rust escape, a space and a `|`
/// escaped too. `path_fixup_baseline.rs` writes the baseline's claims alike.
fn encode_claim(claim: &Option<Vec<String>>) -> String {
    match claim {
        None => "-".to_owned(),
        Some(values) => {
            let mut out = String::from("=");
            for value in values {
                out.push('|');
                out.push_str(
                    &value
                        .escape_default()
                        .to_string()
                        .replace(' ', "\\x20")
                        .replace('|', "\\x7c"),
                );
            }
            out
        }
    }
}

/// Whether the claim `encoded` ([`encode_claim`]) is one MSBuild contradicts
/// from a start whose answer is in `answers`: it commits where MSBuild
/// rejects, or a value MSBuild does not hold.
fn contradicted(encoded: &str, answers: &[&Option<Vec<String>>]) -> bool {
    encoded != "-" && answers.iter().any(|answer| encode_claim(answer) != encoded)
}

/// Evaluate `point` on both sides, and say which claims MSBuild contradicts.
fn grade(world: &mut World, point: &Point) -> Seen {
    let theirs: Vec<Option<Vec<String>>> = point
        .starts
        .iter()
        .map(|&start| msbuild(&mut world.starts[start], point))
        .collect();
    let extra: HashMap<String, String> = point.globals.iter().cloned().collect();
    let env = world.fixture.our_environment();
    let file = borzoi_msbuild::ProjectFile::buffer(&point.project, &point.xml)
        .expect("a project path spelt as its full path");
    let context = |mode: &str| {
        format!(
            "{mode}, {:?} at {:?}, reading {:?}\nsource value: {:?}\nglobals: {:?}\nproject: {}\n--- xml ---\n{}",
            point.source,
            point.site,
            point.read,
            point.value,
            point.globals,
            point.project.display(),
            point.xml
        )
    };
    let globs = Some(&glob_resolver::resolve as &GlobResolver<'_>);
    let probe = ReadProbe {
        item_types: vec!["Foo".to_owned()],
        ..ReadProbe::default()
    };
    let with_imports = parse_fsproj_with_imports(&file, &extra, &env, None, globs).ok();
    let served_reads = parse_fsproj_reads(&file, &extra, &env, None, globs, None, &probe).ok();
    let pure = parse_fsproj(&file, &extra, &env).ok();
    let moved = theirs.iter().any(|answer| answer != &theirs[0]);
    let own_backslash = point.xml.contains('\\');
    // The message against the first start whose answer contradicts `ours`,
    // and every such start's label.
    let contradicting = |ours: &Vec<String>, starts: &[usize], mode: &str| {
        let mut labels = Vec::new();
        let mut message = None;
        for (answer, &start) in theirs.iter().zip(&point.starts) {
            if !starts.contains(&start) {
                continue;
            }
            let label = world.starts[start].label;
            let text = match answer {
                None => format!(
                    "MSBuild rejects the document from {label}, but we commit {ours:?}\n{}",
                    context(mode)
                ),
                Some(answer) if answer != ours => format!(
                    "certain-implies-exact violated against MSBuild started in {label}: ours \
                     {ours:?}, MSBuild's {answer:?}; MSBuild's answers from {:?}: {theirs:?}\n{}",
                    point.starts.map(|s| world.starts[s].label),
                    context(mode)
                ),
                Some(_) => continue,
            };
            labels.push(label);
            message.get_or_insert(text);
        }
        message.map(|message| (labels, message))
    };
    let mut served = false;
    let mut violations = Vec::new();
    let mut seed_guesses = Vec::new();
    for ((mode, ours), key) in [
        (
            "served with imports",
            with_imports
                .as_ref()
                .and_then(|parsed| claim(parsed, None, point.read)),
        ),
        (
            "served reads",
            served_reads
                .as_ref()
                .and_then(|(parsed, reads)| claim(parsed, Some(reads), point.read)),
        ),
        (
            "served pure",
            pure.as_ref()
                .and_then(|parsed| claim(parsed, None, point.read)),
        ),
    ]
    .into_iter()
    .zip(MODES)
    {
        let Some(ours) = ours else {
            continue;
        };
        if mode != "served pure" {
            served = true;
        }
        if moved && !own_backslash {
            seed_guesses.push(key);
        }
        if let Some((starts, message)) = contradicting(&ours, &point.starts, mode) {
            violations.push(Violation {
                mode: key.to_owned(),
                starts,
                message,
            });
        }
    }
    let mut supplied = 0;
    for &start in &point.starts {
        let label = world.starts[start].label;
        let parsed = parse_fsproj_reads(
            &file,
            &extra,
            &env,
            None,
            globs,
            Some(&world.starts[start].dir),
            &probe,
        )
        .ok();
        let Some(ours) = parsed
            .as_ref()
            .and_then(|(parsed, reads)| claim(parsed, Some(reads), point.read))
        else {
            continue;
        };
        supplied += 1;
        let mode = format!("supplied with {label}");
        if let Some((starts, message)) = contradicting(&ours, &[start], &mode) {
            violations.push(Violation {
                mode: format!("s:{label}"),
                starts,
                message,
            });
        }
    }
    Seen {
        served,
        moved,
        supplied,
        theirs,
        violations,
        seed_guesses,
    }
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
            project: world.fixture.root.join("proj-full").join("Demo.fsproj"),
            starts: PROJECTS[0].1,
            read: Read::Property("P"),
            value: common::oracle_environment()["MSBuildUserExtensionsPath"].clone(),
        };
        let seen = check(&mut world, &point);
        assert!(seen.served, "{body}: the walk must commit\n{}", point.xml);
        assert!(!seen.moved, "{body}: MSBuild's value is a fact of the root");
    }
}

/// The modes MSBuild contradicts at `seen`, each with the starts it is
/// contradicted from, in a form two runs compare.
fn wrong_claims(seen: &Seen) -> Vec<(String, Vec<&'static str>)> {
    seen.violations
        .iter()
        .map(|violation| (violation.mode.clone(), violation.starts.clone()))
        .collect()
}

/// What the walk claims wrongly where it takes a probe of `segment` to miss
/// (#993): every served mode, from each of `starts` whose directory holds
/// `segment`, and the supplied mode of each such start.
fn wrong_where_present(starts: [usize; 5], segment: &str) -> Vec<(String, Vec<&'static str>)> {
    let present: Vec<&'static str> = starts
        .iter()
        .map(|&start| STARTS[start])
        .filter(|(_, segments)| segments.contains(&segment))
        .map(|(label, _)| label)
        .collect();
    MODES
        .iter()
        .map(|mode| ((*mode).to_owned(), present.clone()))
        .chain(
            present
                .iter()
                .map(|label| (format!("s:{label}"), vec![*label])),
        )
        .collect()
}

/// #993's shape: a relative `obj\` in project text, compared in a condition
/// and copied into a property. MSBuild started in a directory holding `obj/`
/// stores `obj/`; started anywhere else, `obj\`. The walk takes the probe to
/// miss, so it commits `obj\` and the condition's `FALSE` in every mode, and
/// MSBuild contradicts both from each start holding `obj/`. What does not
/// move, a path combined from the value and a condition that agrees either
/// way, it commits rightly. Pinned, so that a fix of #993 shows here.
#[test]
fn a_relative_backslash_in_project_text_is_committed_as_if_its_probe_missed() {
    let mut world = World::new(1);
    let xml = "<Project>\n  <PropertyGroup>\n    <P>obj\\</P>\n    <R>FALSE</R>\n    \
               <R Condition=\"'$(P)'=='obj/'\">TRUE</R>\n    <N>$([System.IO.Path]::Combine('$(P)', 'x.dll'))</N>\n    \
               <S Condition=\"HasTrailingSlash('$(P)')\">yes</S>\n  </PropertyGroup>\n</Project>\n";
    let mut moved = Vec::new();
    for name in ["P", "R", "N", "S"] {
        let point = Point {
            source: Source::Literal,
            site: Site::Body,
            xml: xml.to_owned(),
            globals: Vec::new(),
            project: world.fixture.root.join("proj-full").join("Demo.fsproj"),
            starts: PROJECTS[0].1,
            read: Read::Property(name),
            value: "obj\\".to_owned(),
        };
        let seen = check_all_absent(&mut world, &point);
        assert!(seen.served, "{name}: the served walk commits");
        assert_eq!(seen.supplied, 5, "{name}: every supplied start commits");
        let expected = if seen.moved {
            moved.push(name);
            wrong_where_present(point.starts, "obj")
        } else {
            Vec::new()
        };
        assert_eq!(
            wrong_claims(&seen),
            expected,
            "{name}: the claims MSBuild contradicts, and from where"
        );
    }
    assert_eq!(moved, ["P", "R"], "what moves with the working directory");
}

/// Each segment is its own question: a condition reading two of them is true
/// from the start holding one and not the other, which a start holding all or
/// none never shows. The walk takes both probes to miss and commits `FALSE`,
/// which MSBuild contradicts from that start alone, served or supplied.
#[test]
fn a_condition_reading_two_segments_is_wrong_only_where_one_is_present() {
    let mut world = World::new(2);
    let xml = "<Project>\n  <PropertyGroup>\n    <P>obj\\x</P>\n    <Q>seg\\y</Q>\n    \
               <R>FALSE</R>\n    <R Condition=\"'$(P)'=='obj/x' And '$(Q)'!='seg/y'\">TRUE</R>\n  \
               </PropertyGroup>\n</Project>\n";
    let point = Point {
        source: Source::Literal,
        site: Site::Condition,
        xml: xml.to_owned(),
        globals: Vec::new(),
        project: world.fixture.root.join("proj-empty").join("Demo.fsproj"),
        starts: PROJECTS[1].1,
        read: Read::Property("R"),
        value: "obj\\x".to_owned(),
    };
    let answers: Vec<(&str, Option<Vec<String>>)> = point
        .starts
        .iter()
        .map(|&start| {
            let answer = msbuild(&mut world.starts[start], &point);
            (world.starts[start].label, answer)
        })
        .collect();
    let truthy: Vec<&str> = answers
        .iter()
        .filter(|(_, answer)| answer.as_deref() == Some(&["TRUE".to_owned()][..]))
        .map(|(label, _)| *label)
        .collect();
    assert_eq!(truthy, ["cwd-obj"], "MSBuild's answers: {answers:?}");
    let seen = check_all_absent(&mut world, &point);
    assert!(seen.moved);
    assert!(seen.served, "the served walk commits");
    assert_eq!(seen.supplied, 5, "every supplied start commits");
    let expected: Vec<(String, Vec<&str>)> = MODES
        .iter()
        .map(|mode| ((*mode).to_owned(), vec!["cwd-obj"]))
        .chain([("s:cwd-obj".to_owned(), vec!["cwd-obj"])])
        .collect();
    assert_eq!(
        wrong_claims(&seen),
        expected,
        "the claims MSBuild contradicts"
    );
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
        let site = match *rng.pick(&Site::SOAKED) {
            // MSBuild's identities are read without globals.
            Site::Identity if source == Source::Global => Site::Item,
            site => site,
        };
        let point = gen_point(&mut rng, &world.fixture, source, site, (case / 7) % 2);
        let seen = check_all_absent(&mut world, &point);
        let entry = census.entry((source, site)).or_default();
        entry.points += 1;
        entry.served += usize::from(seen.served);
        entry.moved += usize::from(seen.moved);
        entry.supplied += seen.supplied;
        entry.supplied_moved += if seen.moved { seen.supplied } else { 0 };
    }
    eprintln!(
        "source / site: points, served committed, moved, supplied committed (of 5 per point), \
         supplied committed where moved"
    );
    for ((source, site), entry) in &census {
        eprintln!(
            "  {source:?} / {site:?}: {}, {}, {}, {}, {}",
            entry.points, entry.served, entry.moved, entry.supplied, entry.supplied_moved
        );
    }
    // Anti-vacuity: each source commits somewhere, and the seeds whose probes
    // are absolute commit at most sites. A walk that declined every backslash
    // would pass the contract.
    for source in Source::ALL {
        let (points, served): (usize, usize) = census
            .iter()
            .filter(|((s, _), _)| *s == source)
            .fold((0, 0), |(p, c), (_, e)| (p + e.points, c + e.served));
        let floor = if source.generated() {
            points / 4
        } else {
            points / 2
        };
        assert!(
            served >= floor,
            "{source:?}: {served} of {points} points committed, below {floor}"
        );
    }
    let moved: usize = census.values().map(|e| e.moved).sum();
    assert!(moved > 0, "no point moved with the working directory");
    for site in Site::SOAKED {
        let (points, served, site_moved, supplied_moved) = census
            .iter()
            .filter(|((_, s), _)| *s == site)
            .fold((0, 0, 0, 0), |(p, c, m, sm), (_, e)| {
                (
                    p + e.points,
                    c + e.served,
                    m + e.moved,
                    sm + e.supplied_moved,
                )
            });
        match site {
            // MSBuild reads the `\` of an `Exists` argument and of an item
            // spec as a separator, so what they answer is the same from every
            // working directory. The served walk commits most item specs, and a
            // little over half of the `Exists` arguments (52% to 66% over
            // twelve seeds), so their floors differ.
            Site::Exists | Site::Item => {
                assert_eq!(site_moved, 0, "{site:?}: MSBuild's answer moved");
                let share = if site == Site::Exists { 3 } else { 2 };
                assert!(
                    served * share >= points,
                    "{site:?}: {served} of {points} points committed"
                );
            }
            // What the walk claims where a body or a condition moves is pinned
            // by `a_relative_backslash_in_project_text_is_committed_as_if_its_probe_missed`:
            // the sweep's moving points depend on its seed. What moves at a
            // property function is a result holding a `\`, which the expression
            // evaluator declines whatever the startup directory
            // (`expr::has_unix_backslash`).
            Site::Body
            | Site::Condition
            | Site::Function
            | Site::Index
            | Site::Coerce
            | Site::Gate => {
                let _ = supplied_moved;
            }
            // An identity's spelling moves with the working directory; a
            // quarter of the points commit at least.
            Site::Identity => assert!(
                served * 4 >= points,
                "{site:?}: {served} of {points} points committed"
            ),
        }
    }
}

/// Where the fixture's temporary directory goes: the host's, where its
/// spelling is plain, else `/tmp`. Its path is written into generated
/// documents (a `'` would end a condition's operand, a `&` begin an entity),
/// so a spelling that changed their grammar would change the points, and the
/// manifests would measure the host rather than the walk.
fn fixture_parent() -> PathBuf {
    // Checked as the documents spell it: canonical, past any symbolic link.
    let host = host_fs::canonicalize(std::env::temp_dir()).unwrap_or_else(|_| std::env::temp_dir());
    let plain = host.to_str().is_some_and(|text| {
        text.chars()
            .all(|c| c.is_ascii_alphanumeric() || "/._-".contains(c))
    });
    if plain { host } else { PathBuf::from("/tmp") }
}

/// The seed and size of the sweep held to `main`'s walk
/// ([`fixed_seed_sweep_regresses_nothing_main_answers`]).
const FIXED_SEED: u64 = 0x0993_0000_0000_0001;
const FIXED_CASES: usize = 900;

/// The text of a generated point, or of a claim on it, with the fixture's
/// root spelt `{ROOT}`, its parent (a directory unique to the run) `{TMP}`,
/// and the host's `MSBuildUserExtensionsPath` `{UEXT}`, so that it names the
/// same document on any host and in any checkout. A document spells each in
/// XML (`xml_attribute`), which is replaced first.
fn placeholder(text: &str, root: &str) -> String {
    static UEXT: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    let uext = UEXT.get_or_init(|| {
        common::oracle_environment()
            .get("MSBuildUserExtensionsPath")
            .cloned()
            .unwrap_or_default()
    });
    // A value that climbs out of the root names its parent.
    let parent = std::path::Path::new(root)
        .parent()
        .and_then(std::path::Path::to_str)
        .unwrap_or(root);
    let mut text = text.to_owned();
    for (path, token) in [
        (root, "{ROOT}"),
        (parent, "{TMP}"),
        (uext.as_str(), "{UEXT}"),
    ] {
        if !path.is_empty() {
            text = text
                .replace(&xml_attribute(path), token)
                .replace(path, token);
        }
    }
    text
}

/// `answer` with each value [`placeholder`]ed, as the baseline records its
/// claims.
fn placeheld(answer: &Option<Vec<String>>, root: &str) -> Option<Vec<String>> {
    answer.as_ref().map(|values| {
        values
            .iter()
            .map(|value| placeholder(value, root))
            .collect()
    })
}

/// FNV-1a over `text`'s bytes, as hex: a point's key against the baseline.
fn fnv1a(text: &str) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{hash:016x}")
}

/// One baseline row: the hash of the point it was recorded on, and each
/// mode's claim, encoded ([`encode_claim`]).
struct BaselineRow {
    hash: String,
    claims: HashMap<String, String>,
}

/// `tests/manifests/path_fixup_baseline.txt`, by case.
fn read_baseline() -> HashMap<String, BaselineRow> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/manifests/path_fixup_baseline.txt");
    let text = host_fs::read_to_string(&path).unwrap_or_default();
    text.lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(|line| {
            let mut fields = line.split('\t');
            let key = fields.next().expect("a key").to_owned();
            let hash = fields.next().expect("a hash").to_owned();
            let claims = fields
                .map(|field| {
                    let (mode, claim) = field.split_once(' ').expect("a mode and its claim");
                    (mode.to_owned(), claim.to_owned())
                })
                .collect();
            (key, BaselineRow { hash, claims })
        })
        .collect()
}

/// What the baseline walk needs beside `point`'s document, as
/// `path_fixup_baseline.rs` reads it: the project, the read graded, and the
/// globals, [`placeholder`]ed.
fn point_meta(point: &Point, root: &str) -> String {
    let project = point
        .project
        .parent()
        .and_then(|dir| dir.file_name())
        .expect("a project directory")
        .to_string_lossy()
        .into_owned();
    let read = match point.read {
        Read::Property(name) => format!("property\t{name}"),
        Read::Items => "items".to_owned(),
        Read::Identities => "identities".to_owned(),
    };
    let mut meta = format!("project\t{project}\nread\t{read}\n");
    for (name, value) in &point.globals {
        meta.push_str(&format!(
            "global\t{name}\t{}\n",
            placeholder(value, root).escape_default()
        ));
    }
    meta
}

/// A point's key against the baseline: every input its evaluation reads
/// that the sweep generates (the document, [`point_meta`], the environment as
/// `env.txt` spells it, and the fixture's [`layout_text`]), hashed as
/// `path_fixup_baseline.rs` hashes them.
fn point_fingerprint(point: &Point, root: &str, environment: &str) -> String {
    fnv1a(&format!(
        "{}\n--\n{}\n--\n{environment}\n--\n{}",
        placeholder(&point.xml, root),
        point_meta(point, root),
        layout_text()
    ))
}

/// Write `point` into `dump` for `path_fixup_baseline.rs`: its document and
/// [`point_meta`], the root spelt `{ROOT}`.
fn dump_point(dump: &std::path::Path, key: &str, point: &Point, root: &str) {
    std::fs::write(
        dump.join(format!("{key}.xml")),
        placeholder(&point.xml, root),
    )
    .unwrap();
    std::fs::write(dump.join(format!("{key}.meta")), point_meta(point, root)).unwrap();
}

/// The fixed seed's points, keyed `case{n}`, over `fixture`.
fn fixed_seed_points(fixture: &Fixture) -> Vec<(String, Point)> {
    let mut rng = SplitMix64(FIXED_SEED);
    (0..FIXED_CASES)
        .map(|case| {
            // The host's `MSBuildUserExtensionsPath` is no fact of the
            // fixture: a point reading it would answer differently on another
            // host, so this sweep draws the environment's generated values in
            // its place.
            let source = match Source::ALL[case % Source::ALL.len()] {
                Source::UserExtensions => Source::Environment,
                source => source,
            };
            let site = match *rng.pick(&Site::ALL) {
                Site::Identity if source == Source::Global => Site::Item,
                site => site,
            };
            let point = gen_point(&mut rng, fixture, source, site, (case / 7) % 2);
            (format!("case{case:04}"), point)
        })
        .collect()
}

/// `fixture`'s environment as `env.txt` spells it: a line per variable, its
/// value [`placeholder`]ed and escaped.
fn environment_text(fixture: &Fixture) -> String {
    let root = fixture.root_text();
    fixture
        .environment
        .iter()
        .map(|(name, value)| format!("{name}\t{}\n", placeholder(value, root).escape_default()))
        .collect()
}

/// The fixed seed's points are a function of the seed alone: laid out under
/// two temporary directories of different depths, each point's key against
/// the baseline ([`point_fingerprint`]) is the same. A key that moved with
/// the host's temporary directory would make the baseline and the pins
/// measure the host rather than the walk.
#[test]
fn fixed_seed_points_do_not_depend_on_where_the_fixture_is() {
    let outer = tempfile::Builder::new()
        .tempdir_in(fixture_parent())
        .unwrap();
    let deeper = outer.path().join("a-deeper-host-temporary-directory");
    std::fs::create_dir(&deeper).unwrap();
    let keys = |parent: &std::path::Path| -> Vec<(String, String)> {
        let fixture = Fixture::new(FIXED_SEED, parent);
        let env = environment_text(&fixture);
        fixed_seed_points(&fixture)
            .into_iter()
            .map(|(key, point)| {
                let hash = point_fingerprint(&point, fixture.root_text(), &env);
                (key, hash)
            })
            .collect()
    };
    assert_eq!(keys(outer.path()), keys(&deeper));
}

/// The landing rule for this change, held mechanically: over a fixed seed's
/// points, every site included, no claim may be wrong where `main`'s walk was
/// right or declined. `main`'s claims are recorded in
/// `tests/manifests/path_fixup_baseline.txt` (`tools/path-fixup-baseline.sh
/// <merge-base>`, which runs `path_fixup_baseline.rs` there over the points
/// this sweep dumps). A wrong claim `main` shares is pinned, point by point,
/// in `tests/manifests/path_fixup_pins.txt`, so that any movement shows.
#[test]
fn fixed_seed_sweep_regresses_nothing_main_answers() {
    let mut world = World::new(FIXED_SEED);
    let root = world.fixture.root_text().to_owned();
    let dump = std::env::var_os("BORZOI_PATH_FIXUP_DUMP").map(PathBuf::from);
    let env = environment_text(&world.fixture);
    if let Some(dump) = &dump {
        std::fs::create_dir_all(dump).unwrap();
        std::fs::write(dump.join("env.txt"), &env).unwrap();
    }
    let baseline = read_baseline();
    let (mut pins, mut regressed, mut stale) = (Vec::new(), Vec::new(), Vec::new());
    let mut violations = 0usize;
    // The claims `main` made wrongly that the walk under test does not.
    let mut righted = 0usize;
    for (key, point) in fixed_seed_points(&world.fixture) {
        let (source, site) = (point.source, point.site);
        if let Some(dump) = &dump {
            dump_point(dump, &key, &point, &root);
        }
        let seen = grade(&mut world, &point);
        violations += seen.violations.len();
        let hash = point_fingerprint(&point, &root, &env);
        let Some(row) = baseline.get(&key).filter(|row| row.hash == hash) else {
            stale.push(key);
            continue;
        };
        let answers_of = |mode: &str| -> Vec<&Option<Vec<String>>> {
            match mode.strip_prefix("s:") {
                None => seen.theirs.iter().collect(),
                Some(label) => point
                    .starts
                    .iter()
                    .zip(&seen.theirs)
                    .filter(|(start, _)| world.starts[**start].label == label)
                    .map(|(_, answer)| answer)
                    .collect(),
            }
        };
        // The baseline's claims are in `{ROOT}`/`{UEXT}` spelling, and so are
        // the answers it is held to.
        let placeheld_answers = |mode: &str| -> Vec<Option<Vec<String>>> {
            answers_of(mode)
                .into_iter()
                .map(|answer| placeheld(answer, &root))
                .collect()
        };
        righted += row
            .claims
            .iter()
            .filter(|(mode, claim)| {
                let answers = placeheld_answers(mode);
                contradicted(claim, &answers.iter().collect::<Vec<_>>())
                    && !seen.violations.iter().any(|ours| ours.mode == **mode)
            })
            .count();
        for Violation {
            mode,
            starts,
            message,
        } in &seen.violations
        {
            let answers = placeheld_answers(mode);
            let answers: Vec<&Option<Vec<String>>> = answers.iter().collect();
            let main_claim = row.claims.get(mode).map_or("-", String::as_str);
            if contradicted(main_claim, &answers) {
                // With the starts that contradict it: a claim no start holding
                // no segment contradicts is one only the startup directory
                // moves (#993).
                pins.push((
                    format!("{key} {mode}"),
                    format!("{source:?}/{site:?} from {}", starts.join(",")),
                ));
            } else {
                regressed.push(format!(
                    "{key} {mode} (main claims {main_claim}): {message}"
                ));
            }
        }
    }
    eprintln!(
        "path fixup fixed seed: {violations} wrong claims, {} shared with main; \
         {righted} of main's wrong claims the walk does not make",
        pins.len()
    );
    assert!(
        stale.is_empty(),
        "the baseline does not hold {} of the points this sweep generates (first {}): \\
         regenerate it with `bash tools/path-fixup-baseline.sh $(git merge-base HEAD \\
         origin/main)`",
        stale.len(),
        stale[0]
    );
    assert!(
        regressed.is_empty(),
        "{} claims wrong where main's walk was right or declined:\n{}",
        regressed.len(),
        regressed.join("\n")
    );
    let manifest = Manifest::from_keyed(pins).expect("well-formed entries");
    manifest::check(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/manifests/path_fixup_pins.txt"),
        &manifest,
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \\
         path_fixup_expansion_diff fixed_seed_sweep_regresses_nothing_main_answers",
    );
}

/// What the walk claims wrongly about an SDK project's output paths
/// ([`sdk_output_paths_moved_by_the_startup_directory_are_pinned`]), as
/// (mode, name, the start MSBuild contradicts it from). It takes a relative
/// probe to miss (#993), so it commits `obj\` and `bin\` as MSBuild spells
/// them from a directory holding neither, served and supplied alike, and the
/// conditions on them in the project as decided there.
const SDK_WRONG_CLAIMS: &[(&str, &str, &str)] = &[
    ("served", "BaseIntermediateOutputPath", "project"),
    ("supplied", "BaseIntermediateOutputPath", "project"),
    ("served", "_InitialBaseIntermediateOutputPath", "project"),
    ("supplied", "_InitialBaseIntermediateOutputPath", "project"),
    ("served", "BaseOutputPath", "project"),
    ("supplied", "BaseOutputPath", "project"),
    ("served", "Moved", "project"),
    ("supplied", "Moved", "project"),
    ("served", "BaseIntermediateOutputPath", "full"),
    ("supplied", "BaseIntermediateOutputPath", "full"),
    ("served", "_InitialBaseIntermediateOutputPath", "full"),
    ("supplied", "_InitialBaseIntermediateOutputPath", "full"),
    ("served", "BaseOutputPath", "full"),
    ("supplied", "BaseOutputPath", "full"),
    ("served", "Moved", "full"),
    ("supplied", "Moved", "full"),
];

/// The SDK's own `obj\` and `bin\`, held to the whole contract: an SDK project
/// whose directory holds `obj/` and `bin/` (a restored, built one), evaluated
/// by MSBuild started in that directory, in one holding neither, and in one
/// holding both. `BaseIntermediateOutputPath` and the paths composed from it
/// move; a condition on one in the project moves with it, and so does the
/// assembly name it gates. Every claim MSBuild contradicts is pinned in
/// [`SDK_WRONG_CLAIMS`], the trusted `obj\` among them.
#[test]
fn sdk_output_paths_moved_by_the_startup_directory_are_pinned() {
    const NAMES: &[&str] = &[
        "BaseIntermediateOutputPath",
        "_InitialBaseIntermediateOutputPath",
        "BaseOutputPath",
        "IntermediateOutputPath",
        "OutputPath",
        "OutDir",
        "MSBuildProjectExtensionsPath",
        "ProjectAssetsFile",
        "AssemblyName",
        "TargetName",
        "TargetFileName",
        "Moved",
    ];
    let tmp = TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    let project_dir = root.join("app");
    let elsewhere = root.join("elsewhere");
    let full = root.join("full");
    std::fs::create_dir_all(&elsewhere).unwrap();
    for dir in [&project_dir, &full] {
        for segment in ["obj", "bin"] {
            std::fs::create_dir_all(dir.join(segment)).unwrap();
        }
    }
    let project = project_dir.join("App.fsproj");
    let xml = "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    \
               <TargetFramework>net10.0</TargetFramework>\n    \
               <Moved Condition=\"'$(BaseIntermediateOutputPath)' == 'obj/'\">yes</Moved>\n    \
               <AssemblyName Condition=\"'$(BaseOutputPath)' == 'bin/'\">Moved</AssemblyName>\n  \
               </PropertyGroup>\n</Project>\n";
    let dotnet_root = common::dotnet_root_from_env();
    let (user_dotnet_root, overrides_present) = common::workload_env_from_process();
    let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        resolve_sdk(
            &dotnet_root,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present,
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    let sdk_resolver = &resolver as &borzoi_msbuild::SdkResolver<'_>;
    let env = common::oracle_environment();
    let file = borzoi_msbuild::ProjectFile::buffer(&project, xml).expect("a full path");
    let served = parse_fsproj_with_imports(&file, &HashMap::new(), &env, Some(sdk_resolver), None)
        .expect("well-formed XML parses");
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_owned()).collect();
    let mut answers: Vec<(&str, HashMap<String, String>)> = Vec::new();
    let mut wrong: Vec<(&str, &str, &str)> = Vec::new();
    for (label, dir) in [
        ("project", &project_dir),
        ("elsewhere", &elsewhere),
        ("full", &full),
    ] {
        let answer = Oracle::spawn_in_dir(dir)
            .project(xml, &names, Some(&project), &[])
            .expect("MSBuild evaluates the SDK project");
        let (supplied, _) = parse_fsproj_reads(
            &file,
            &HashMap::new(),
            &env,
            Some(sdk_resolver),
            None,
            Some(dir),
            &ReadProbe::default(),
        )
        .expect("well-formed XML parses");
        for name in NAMES {
            let theirs = answer.get(*name).cloned().unwrap_or_default();
            for (mode, parsed) in [("served", &served), ("supplied", &supplied)] {
                if let Some(ours) = claim(parsed, None, Read::Property(name))
                    && ours != std::slice::from_ref(&theirs)
                {
                    eprintln!(
                        "{mode}: ${name} is {ours:?}, MSBuild started in {label} has {theirs:?}"
                    );
                    wrong.push((mode, name, label));
                }
            }
        }
        answers.push((label, answer));
    }
    assert_eq!(
        wrong, SDK_WRONG_CLAIMS,
        "the claims MSBuild contradicts, by mode, name and start"
    );
    // The fixture moves what it means to: MSBuild's `obj\` depends on where it
    // starts.
    let spellings: Vec<&str> = answers
        .iter()
        .map(|(_, answer)| answer["BaseIntermediateOutputPath"].as_str())
        .collect();
    assert_eq!(
        spellings,
        ["obj/", "obj\\", "obj/"],
        "MSBuild's spellings by start"
    );
}
