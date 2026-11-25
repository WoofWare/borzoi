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

/// Which of the relative names the points probe ([`probed_names`]) a working
/// directory holds as directories.
#[derive(Clone, Copy)]
enum Holds {
    Nothing,
    Every,
    Only(&'static str),
}

/// The fixture's working directories, in [`World::starts`] order, and what
/// each holds.
const STARTS: [(&str, Holds); 6] = [
    ("cwd-empty", Holds::Nothing),
    ("cwd-full", Holds::Every),
    ("cwd-seg", Holds::Only("seg")),
    ("cwd-obj", Holds::Only("obj")),
    ("proj-full", Holds::Every),
    ("proj-empty", Holds::Nothing),
];

/// The literal runs of `text`: what lies between its `$(…)` references, each
/// of which MSBuild's fixup adjusts as a piece of its own.
fn literal_runs(text: &str) -> Vec<&str> {
    let mut runs = Vec::new();
    let mut rest = text;
    while let Some(start) = rest.find("$(") {
        runs.push(&rest[..start]);
        let mut depth = 0usize;
        let mut end = rest.len();
        for (i, c) in rest[start + 1..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = start + 1 + i + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        rest = &rest[end..];
    }
    runs.push(rest);
    runs
}

/// The relative first segments MSBuild's fixup may ask about for `texts`,
/// the texts points record it adjusts ([`Point::probes`]): the first segment
/// of each, and of each literal run of one, where it holds a `\`. An escaped `%5c` is no separator, so it stays in the name.
///
/// A rooted text names the host's file system, not the fixture's, unless it
/// is under the fixture's root: each such first segment must be absent from
/// the host, or the answers the baseline records would be host facts. That
/// is asserted here, so a host it fails on says so rather than answering
/// apart from the host that recorded the baseline.
fn probed_names<'t>(
    texts: impl IntoIterator<Item = &'t str>,
    root: &str,
) -> std::collections::BTreeSet<String> {
    let under_root = root.trim_start_matches('/');
    // The host's `MSBuildUserExtensionsPath` is a host fact by design
    // ([`Source::UserExtensions`]), which the fixed seed never reads.
    let user_extensions = common::oracle_environment()
        .get("MSBuildUserExtensionsPath")
        .map(|path| path.replace('\\', "/").trim_start_matches('/').to_owned())
        .filter(|path| !path.is_empty());
    let mut relative = std::collections::BTreeSet::new();
    let mut rooted = std::collections::BTreeMap::new();
    let depth = ROOT_IN_TMP.split('/').count();
    for text in texts {
        for piece in std::iter::once(text).chain(literal_runs(text)) {
            let piece = piece.replace("$(Empty)", "");
            let bare = piece.trim_start_matches(['/', '\\']);
            // Read from the root, or from a directory in it (a start, a
            // project), no path may leave the temporary directory.
            let (from, allowed) = match bare.strip_prefix(under_root) {
                Some(rest) if bare.len() < piece.len() => (rest, depth),
                _ if bare.len() < piece.len() => ("", 0),
                _ => (piece.as_str(), depth + 1),
            };
            assert!(
                climb(from) <= allowed,
                "{text:?} climbs out of the fixture's temporary directory: deepen ROOT_IN_TMP"
            );
            if bare.len() < piece.len() {
                let host_by_design = user_extensions
                    .as_deref()
                    .is_some_and(|path| bare.replace('\\', "/").starts_with(path));
                if !bare.starts_with(under_root) && !host_by_design {
                    let first = bare.split(['/', '\\']).next().unwrap_or_default();
                    if !first.is_empty() {
                        rooted
                            .entry(first.to_owned())
                            .or_insert_with(|| text.to_owned());
                    }
                }
            } else if piece.contains('\\') {
                let first = piece.split(['/', '\\']).next().unwrap_or_default();
                if !matches!(first, "" | "." | "..") {
                    relative.insert(first.to_owned());
                }
            }
        }
    }
    for (name, text) in &rooted {
        if name != ".." && name != "." {
            assert!(
                host_fs::metadata(std::path::Path::new("/").join(name)).is_err(),
                "/{name}, which a generated point names ({text:?}), is on this host: its \
                 answers would measure the host"
            );
        }
    }
    relative
}

/// How many levels above where it starts `path` reaches, read segment by
/// segment (a `%5c` is no separator).
fn climb(path: &str) -> usize {
    let (mut depth, mut lowest) = (0i64, 0i64);
    for segment in path.split(['/', '\\']) {
        match segment {
            ".." => depth -= 1,
            "" | "." => {}
            _ => depth += 1,
        }
        lowest = lowest.min(depth);
    }
    usize::try_from(-lowest).expect("a climb is never negative")
}

/// Files under `proj-full`'s segments, for the `Compile` globs to find.
const ITEM_FILES: &[&str] = &["seg/a.fs", "seg/b c.fs", "obj/a.fs"];

/// How many environment variables [`World`] sets, each to a generated value.
const ENVIRONMENT_VALUES: usize = 24;

/// One directory MSBuild is started from, with the oracle child running there.
struct Start {
    label: &'static str,
    dir: PathBuf,
    /// Whether the directory holds none of the probed names: the start
    /// whose answer the walk assumes for every relative probe.
    all_absent: bool,
    oracle: Oracle,
}

/// The fixture on disk: a canonical root, the environment variables both
/// sides read, and, once furnished ([`Fixture::furnish`]), [`STARTS`]'
/// directories and the projects' files.
struct Fixture {
    root: PathBuf,
    /// `BorzoiEnv{i}` and its value, which MSBuild reads as a property.
    environment: Vec<(String, String)>,
    /// What [`Fixture::furnish`] laid out ([`layout_text`]).
    layout: String,
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

/// Where the fixture's root sits inside its temporary directory: deep enough
/// that no composed path climbs out, so that every path a point names is the
/// fixture's or a host-rooted name [`probed_names`] holds absent, never a
/// file of the host's temporary directory. A value climbs four levels at
/// most (a `..` first segment, three `..` parts, a last separator), a read
/// template and a copy template may each double it, and the climb starts in
/// a directory of the root's: sixteen levels below the temporary directory.
/// [`probed_names`] asserts the bound on every point.
const ROOT_IN_TMP: &str = "c/c/c/c/c/c/c/c/c/c/c/c/c/c/fixture";

/// The fixture's layout as text, holding `names` in the full starts: a
/// `root` line, [`ROOT_IN_TMP`]; a `dir` line per start, its directory and
/// each name it holds; a `file` line per file under `proj-full` and beside
/// each project; and a `project` line per project, with its starts. The
/// sweep lays the fixture out from it ([`lay_out`]), dumps it for
/// `path_fixup_baseline.rs`, which lays its fixture out from that dump, and
/// hashes it into every point's key ([`point_fingerprint`]).
fn layout_text(names: &std::collections::BTreeSet<String>) -> String {
    let mut text = format!("root\t{ROOT_IN_TMP}\n");
    for (dir, holds) in STARTS {
        text.push_str(&format!("dir\t{dir}"));
        let held: Vec<&str> = match holds {
            Holds::Nothing => Vec::new(),
            Holds::Only(name) => vec![name],
            Holds::Every => names.iter().map(String::as_str).collect(),
        };
        for name in held {
            text.push_str(&format!("\t{name}"));
        }
        text.push('\n');
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

/// Lay `layout` ([`layout_text`]) out under `root`, as
/// `path_fixup_baseline.rs` does.
fn lay_out(root: &std::path::Path, layout: &str) {
    for line in layout.lines() {
        let mut fields = line.split('\t');
        match fields.next() {
            Some("dir") => {
                let dir = root.join(fields.next().expect("a directory"));
                std::fs::create_dir_all(&dir).unwrap();
                for name in fields {
                    std::fs::create_dir_all(dir.join(name)).unwrap();
                }
            }
            Some("file") => {
                let file = root.join(fields.next().expect("a file"));
                std::fs::create_dir_all(file.parent().expect("a directory")).unwrap();
                std::fs::write(file, "").unwrap();
            }
            Some("root" | "project") => {}
            other => panic!("no layout line {other:?}"),
        }
    }
}

impl Fixture {
    /// The fixture for `seed`, in a new temporary directory under `parent`,
    /// not yet furnished.
    fn new(seed: u64, parent: &std::path::Path) -> Fixture {
        let tmp = tempfile::Builder::new().tempdir_in(parent).unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap().join(ROOT_IN_TMP);
        std::fs::create_dir_all(&root).unwrap();
        let mut rng = SplitMix64(seed ^ 0x5eed_e1f1_0000_0001);
        let root_text = root.to_str().unwrap().to_owned();
        let environment: Vec<(String, String)> = (0..ENVIRONMENT_VALUES)
            .map(|i| (format!("BorzoiEnv{i}"), gen_value(&mut rng, &root_text)))
            .collect();
        Fixture {
            root,
            environment,
            layout: String::new(),
            _tmp: tmp,
        }
    }

    /// Lay the fixture out with the full starts holding every name `texts`
    /// probe ([`probed_names`]).
    fn furnish<'t>(&mut self, texts: impl IntoIterator<Item = &'t str>) {
        let names = probed_names(texts, self.root_text());
        self.layout = layout_text(&names);
        lay_out(&self.root, &self.layout);
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
    /// `fixture`, furnished, with an oracle child in each start.
    fn new(fixture: Fixture) -> World {
        assert!(!fixture.layout.is_empty(), "the fixture is furnished");
        let starts = STARTS
            .into_iter()
            .map(|(label, holds)| {
                let dir = fixture.root.join(label);
                Start {
                    label,
                    oracle: Oracle::spawn_in_dir_with_env(&dir, &fixture.environment),
                    all_absent: matches!(holds, Holds::Nothing),
                    dir,
                }
            })
            .collect();
        World { fixture, starts }
    }

    /// A world for hand-written points, which probe `seg` and `obj`.
    fn for_hand_written(seed: u64) -> World {
        let mut fixture = Fixture::new(seed, &fixture_parent());
        fixture.furnish(["seg\\x", "obj\\x"]);
        World::new(fixture)
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

/// The body of the indexer site's `U`: a name the walk holds no value of
/// (through a function it does not model), whose value is long enough that
/// every read of it the site writes succeeds in MSBuild.
const UNHELD: &str = "$([System.IO.Path]::GetFileName('borzoi-unheld'))";

/// The indexer site's `F`, reading `X.Split('/')[index]`: alone (`variant`
/// 0), or beside `U` ([`UNHELD`]), read after the indexer (1), before it
/// (2), or beside more relative paths than the walk enumerates (3). Every
/// read of `U` succeeds in MSBuild, so that the indexer alone decides
/// whether it throws: [`each_index_variant_throws_only_at_its_indexer`].
fn index_body(variant: usize, index: usize) -> String {
    match variant {
        0 => format!("$(X.Split('/')[{index}])"),
        1 => format!("$(X.Split('/')[{index}].Split('z$(U)')[0])"),
        2 => format!("$(X.TrimStart('z$(U)').Split('/')[{index}])"),
        _ => {
            let splices: String = (0..UNENUMERATED_SPLICES)
                .map(|i| format!("s{i}\\x$(Empty)"))
                .collect();
            format!("{splices}$(U.Substring(5))$(X.Split('/')[{index}])")
        }
    }
}

/// Each variant of the indexer site ([`index_body`]) is accepted by MSBuild
/// where the index is inside the value's fields, and rejected where it is
/// past their end: no read beside the indexer throws on its own.
#[test]
fn each_index_variant_throws_only_at_its_indexer() {
    let mut world = World::for_hand_written(3);
    let project = world.fixture.root.join("proj-empty").join("Demo.fsproj");
    for variant in 0..4 {
        for (index, accepted) in [(0, true), (1, true), (2, false)] {
            let mut writes = String::from("    <X>a/b</X>\n");
            if variant != 0 {
                writes.push_str(&format!("    <U>{UNHELD}</U>\n"));
            }
            writes.push_str(&format!(
                "    <F>{}</F>\n",
                xml_body(&index_body(variant, index))
            ));
            writes.push_str(AFTER);
            let xml =
                format!("<Project>\n  <PropertyGroup>\n{writes}  </PropertyGroup>\n</Project>\n");
            let answer =
                world.starts[0]
                    .oracle
                    .project(&xml, &["After".to_owned()], Some(&project), &[]);
            assert_eq!(
                answer.is_some(),
                accepted,
                "variant {variant}, index {index}: MSBuild accepts?\n{xml}"
            );
        }
    }
}

/// The last write of a rejection-shaped point: unconditional, so the walk
/// publishes it exactly where it claims MSBuild accepts the project.
const AFTER: &str = "  </PropertyGroup>\n  <PropertyGroup>\n    <After>ok</After>\n";

/// A generated value for `site`: for an indexer, half the time a relative
/// segment joined to a part by a `\`, whose respelling moves the value's
/// fields; otherwise [`gen_value`]'s.
fn gen_site_value(rng: &mut SplitMix64, root: &str, site: Site) -> String {
    if site == Site::Item && rng.below(2) == 0 {
        // A bare segment, whose glob finds `proj-full`'s files.
        return (*rng.pick(&["seg", "obj"])).to_owned();
    }
    if site == Site::Index && rng.below(2) == 0 {
        let segment = *rng.pick(&["seg", "obj"]);
        let separator = *rng.pick(&["\\", "%5c"]);
        let part = *rng.pick(&["a", "seg", "..", "b c"]);
        format!("{segment}{separator}{part}")
    } else {
        gen_value(rng, root)
    }
}

/// The first segments [`gen_value`] writes beside the fixture's root, which
/// stands for an absolute path that exists. Those rooted at the host's `/`
/// are probed on the host, which [`probed_names`] holds them absent from.
const PREFIXES: &[&str] = &[
    "/borzoi-missing",
    "seg",
    "obj",
    ".",
    "..",
    "",
    r"\\borzoi-missing",
    r"\borzoi-missing",
    "a",
];

/// The parts [`gen_value`] joins after the first segment.
const PARTS: &[&str] = &["a", "seg", "..", "b c"];

/// One generated value: a first segment, then parts joined by separators.
fn gen_value(rng: &mut SplitMix64, root: &str) -> String {
    let prefixes: Vec<String> = std::iter::once(root.to_owned())
        .chain(PREFIXES.iter().map(|prefix| (*prefix).to_owned()))
        .collect();
    const SEPARATORS: &[&str] = &["\\", "/", "\\\\", "\\/", "%5c"];
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
    /// The texts the point makes MSBuild adjust, with each reference
    /// replaced by the text it reads as written: what [`probed_names`] reads
    /// the probed names off.
    probes: Vec<String>,
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
    } else if site == Site::Item && matches!(value.as_str(), "seg" | "obj") {
        // So that the glob under a bare segment finds its files.
        "{v}"
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
    // What the read expands to as written: the value, through the copy
    // template for a copied one, inside the read's template.
    let spliced = copy_template.map_or_else(|| value.clone(), |copy| copy.replace("{v}", &value));
    let composed = template.replace("{v}", &spliced);
    let mut probes = vec![value.clone(), spliced.clone(), composed.clone()];
    probes.extend(
        [template, copy_template.unwrap_or("{v}")]
            .iter()
            .map(|t| t.replace("{v}", "$(V)")),
    );
    let read = match site {
        Site::Body => {
            writes.push_str(&format!("    <P>{}</P>\n", xml_body(&expansion)));
            Read::Property("P")
        }
        Site::Condition => {
            // Compare with one spelling MSBuild may produce: the expansion as
            // written, or the same with every `\` a `/`.
            let candidate = if rng.below(2) == 0 {
                composed.clone()
            } else {
                composed.replace('\\', "/")
            };
            probes.push(candidate.clone());
            let condition = format!("'{expansion}' == '{candidate}'");
            writes.push_str(&format!(
                "    <C Condition=\"{}\">hit</C>\n",
                xml_attribute(&condition)
            ));
            Read::Property("C")
        }
        Site::Exists => {
            // `Exists` asks the file system about the path itself.
            probes.push(composed.clone());
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
                let fields = composed
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
            let variant = rng.below(4);
            if variant != 0 {
                writes.push_str(&format!("    <U>{UNHELD}</U>\n"));
            }
            let body = index_body(variant, index);
            // Each field the indexer may return is adjusted whole, whether or
            // not a `\` before it was respelled.
            for spelling in [composed.clone(), composed.replace('\\', "/")] {
                probes.extend(spelling.split('/').map(str::to_owned));
            }
            probes.push(body.clone());
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
            let candidate = if rng.below(2) == 0 {
                composed.clone()
            } else {
                composed.replace('\\', "/")
            };
            probes.push(candidate.clone());
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
            probes.push(include.replace(&expansion, &composed));
            probes.extend(
                exclude
                    .as_ref()
                    .map(|exclude| exclude.replace(&expansion, &composed)),
            );
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
        probes,
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
    /// The labels of the starts the mode is held to whose answer contradicts
    /// it: every one for a served mode, its own for a supplied one.
    starts: Vec<&'static str>,
    /// The labels of every start of the point whose answer contradicts it.
    contradicted_from: Vec<&'static str>,
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

/// What a glob at an item point found, by MSBuild's answer from any start,
/// where the served walk committed too: a file under `proj-full`'s segments
/// ([`ITEM_FILES`]) through a wildcard, and that, beside an `Exclude`, with
/// the excluded file gone. Counted so that a gate whose globs found nothing,
/// or whose walk declined every one that did, cannot pass for one that
/// grades them.
#[derive(Default)]
struct GlobCoverage {
    found: usize,
    found_beside_exclude: usize,
}

impl GlobCoverage {
    fn count(&mut self, point: &Point, seen: &Seen) {
        if point.site != Site::Item || !point.xml.contains('*') || !seen.served {
            return;
        }
        let listed = |file: &str| {
            let suffix = format!("/proj-full/{file}");
            seen.theirs
                .iter()
                .flatten()
                .flatten()
                .any(|path| path.ends_with(&suffix))
        };
        if ITEM_FILES.iter().any(|file| listed(file)) {
            self.found += 1;
            if point.xml.contains("Exclude=") && listed("seg/b c.fs") && !listed("seg/a.fs") {
                self.found_beside_exclude += 1;
            }
        }
    }
}

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

/// The starts of `graded` from which a claim `encoded` ([`encode_claim`])
/// would be newly wrong where the baseline claimed `baseline`: those whose
/// answer (in `answers`, by label) the baseline's claim agrees with, or where
/// the baseline declined. A wrong claim is the baseline's to share only at
/// a start where the baseline was wrong too.
fn newly_wrong<'a>(
    baseline: &str,
    graded: &[&'a str],
    answers: &[(&str, Option<Vec<String>>)],
) -> Vec<&'a str> {
    graded
        .iter()
        .copied()
        .filter(|label| {
            let answer = answers
                .iter()
                .find(|(start, _)| start == label)
                .map(|(_, answer)| answer)
                .expect("every graded start was asked");
            !contradicted(baseline, &[answer])
        })
        .collect()
}

/// A claim wrong at a start where the baseline was right is new there, even
/// where the baseline was wrong at another start.
#[test]
fn a_claim_is_shared_with_the_baseline_only_where_the_baseline_was_wrong() {
    let answers = [
        ("cwd-empty", Some(vec!["seg\\".to_owned()])),
        ("cwd-full", Some(vec!["seg/".to_owned()])),
        ("cwd-obj", None),
    ];
    let both = ["cwd-empty", "cwd-full"];
    // The baseline's `seg\` is right from `cwd-empty`, wrong from `cwd-full`.
    assert_eq!(newly_wrong("=|seg\\\\", &both, &answers), ["cwd-empty"]);
    assert!(newly_wrong("=|seg\\\\", &["cwd-full"], &answers).is_empty());
    // A baseline wrong at both shares both; one that declined shares none.
    assert!(newly_wrong("=|x", &both, &answers).is_empty());
    assert_eq!(newly_wrong("-", &both, &answers), both);
    // A commit where MSBuild rejects is wrong.
    assert!(newly_wrong("=|x", &["cwd-obj"], &answers).is_empty());
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
    if !matches!(point.read, Read::Identities) {
        assert_eq!(
            with_imports
                .as_ref()
                .and_then(|parsed| claim(parsed, None, point.read)),
            served_reads
                .as_ref()
                .and_then(|(parsed, _)| claim(parsed, None, point.read)),
            "probing the walk moved its claim (with imports left, probed right)\n{}",
            context("served")
        );
    }
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
        // An identity is read through the probe; every other read through
        // the walk the LSP serves.
        let counted = if matches!(point.read, Read::Identities) {
            "served reads"
        } else {
            "served with imports"
        };
        if mode == counted {
            served = true;
        }
        if moved && !own_backslash {
            seed_guesses.push(key);
        }
        if let Some((starts, message)) = contradicting(&ours, &point.starts, mode) {
            violations.push(Violation {
                mode: key.to_owned(),
                contradicted_from: starts.clone(),
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
            let (contradicted_from, _) = contradicting(&ours, &point.starts, &mode)
                .expect("a claim contradicted from one start is contradicted from the point's");
            violations.push(Violation {
                mode: format!("s:{label}"),
                starts,
                contradicted_from,
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
    let mut world = World::for_hand_written(0);
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
            probes: Vec::new(),
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
fn wrong_where_present(
    world: &World,
    starts: [usize; 5],
    segment: &str,
) -> Vec<(String, Vec<&'static str>)> {
    let present: Vec<&'static str> = starts
        .iter()
        .map(|&start| &world.starts[start])
        .filter(|start| host_fs::metadata(start.dir.join(segment)).is_ok_and(|m| m.is_dir()))
        .map(|start| start.label)
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
    let mut world = World::for_hand_written(1);
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
            probes: Vec::new(),
        };
        let seen = check_all_absent(&mut world, &point);
        assert!(seen.served, "{name}: the served walk commits");
        assert_eq!(seen.supplied, 5, "{name}: every supplied start commits");
        let expected = if seen.moved {
            moved.push(name);
            wrong_where_present(&world, point.starts, "obj")
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
    let mut world = World::for_hand_written(2);
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
        probes: Vec::new(),
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

/// The deepest climb the generator can compose, a value climbing four levels
/// doubled by both a read and a copy template, then a part, stays inside the
/// fixture's temporary directory from a directory of the root's.
#[test]
fn the_deepest_composed_climb_stays_in_the_temporary_directory() {
    assert_eq!(climb("../../../../../../y"), 6);
    assert_eq!(climb("../a/../..%5c../b"), 1);
    let value = "..\\..\\..\\..\\";
    let doubled = "{v}{v}".replace("{v}", &"{v}{v}".replace("{v}", value));
    let text = format!("{doubled}y");
    let depth = ROOT_IN_TMP.split('/').count();
    assert!(climb(&text) <= depth + 1, "{text:?} climbs out");
    // `probed_names` holds every point to the same bound.
    probed_names([text.as_str()], "/nowhere");
}

/// The indexer's splices are each a piece MSBuild adjusts, so each is a name
/// the full starts hold.
#[test]
fn every_indexer_splice_is_a_probed_name() {
    assert_eq!(
        literal_runs("s0\\x$(Empty)s1\\x$(U.Substring(5))$(X.Split('/')[0])q"),
        ["s0\\x", "s1\\x", "", "q"]
    );
    let names = probed_names([index_body(3, 0).as_str()], "/nowhere");
    let splices: Vec<String> = (0..UNENUMERATED_SPLICES).map(|i| format!("s{i}")).collect();
    assert_eq!(names.into_iter().collect::<Vec<_>>(), splices);
}

/// A copied value's condition compares the copy as the copy template writes
/// it, so its outcome turns on whether MSBuild respelled the value it copied.
#[test]
fn a_copied_value_is_compared_through_its_copy_template() {
    let mut world = World::for_hand_written(5);
    let xml = "<Project>\n  <PropertyGroup>\n    <V>seg\\a</V>\n    <W>[$(V)]</W>\n    \
               <C Condition=\"'$(W)' == '[seg/a]'\">hit</C>\n  </PropertyGroup>\n</Project>\n";
    let point = Point {
        source: Source::Copied,
        site: Site::Condition,
        xml: xml.to_owned(),
        globals: Vec::new(),
        project: world.fixture.root.join("proj-empty").join("Demo.fsproj"),
        starts: PROJECTS[1].1,
        read: Read::Property("C"),
        value: "seg\\a".to_owned(),
        probes: Vec::new(),
    };
    let seen = check_all_absent(&mut world, &point);
    let hit: Vec<&str> = point
        .starts
        .iter()
        .zip(&seen.theirs)
        .filter(|(_, answer)| answer.as_deref() == Some(&["hit".to_owned()][..]))
        .map(|(&start, _)| world.starts[start].label)
        .collect();
    assert_eq!(
        hit,
        ["cwd-full", "cwd-seg"],
        "MSBuild's answers: {:?}",
        seen.theirs
    );
}

/// A glob that finds files, alone and beside an `Exclude` that removes one,
/// is graded whatever the soak's seed draws: MSBuild lists the files, and
/// the served walk commits them.
#[test]
fn a_glob_that_finds_files_is_graded() {
    let mut world = World::for_hand_written(4);
    for (include, exclude) in [
        ("seg\\*.fs", None),
        ("seg\\*.fs", Some("seg\\a.fs")),
        ("obj/*.fs", None),
    ] {
        let exclude = exclude
            .map(|exclude| format!(" Exclude=\"{exclude}\""))
            .unwrap_or_default();
        let point = Point {
            source: Source::Literal,
            site: Site::Item,
            xml: format!(
                "<Project>\n  <ItemGroup>\n    <Compile Include=\"{include}\"{exclude} />\n  \
                 </ItemGroup>\n</Project>\n"
            ),
            globals: Vec::new(),
            project: world.fixture.root.join("proj-full").join("Demo.fsproj"),
            starts: PROJECTS[0].1,
            read: Read::Items,
            value: include.to_owned(),
            probes: Vec::new(),
        };
        let seen = check_all_absent(&mut world, &point);
        let mut globs = GlobCoverage::default();
        globs.count(&point, &seen);
        assert_eq!(globs.found, 1, "{include}{exclude}: graded and found");
        assert_eq!(
            globs.found_beside_exclude,
            usize::from(!exclude.is_empty()),
            "{include}{exclude}: the Exclude removed its file"
        );
    }
}

/// The generated sweep over sources, read sites and values.
#[test]
fn expansions_hold_msbuilds_path_fixup() {
    let (seed, cases) = common::soak_parameters("BORZOI_PATH_FIXUP_EXPANSION", 600);
    let mut rng = SplitMix64(seed);
    let mut fixture = Fixture::new(seed, &fixture_parent());
    let points: Vec<Point> = (0..cases)
        .map(|case| {
            let source = Source::ALL[case % Source::ALL.len()];
            let site = match *rng.pick(&Site::SOAKED) {
                // MSBuild's identities are read without globals.
                Site::Identity if source == Source::Global => Site::Item,
                site => site,
            };
            gen_point(&mut rng, &fixture, source, site, (case / 7) % 2)
        })
        .collect();
    fixture.furnish(
        points
            .iter()
            .flat_map(|point| point.probes.iter().map(String::as_str)),
    );
    let mut world = World::new(fixture);
    let mut census: BTreeMap<(Source, Site), Census> = BTreeMap::new();
    for point in &points {
        let (source, site) = (point.source, point.site);
        let seen = check_all_absent(&mut world, point);
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
            // little over half of the `Exists` arguments (57% to 74% over
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
    // A value that climbs out of the root names a directory of the
    // temporary directory's.
    let parent = root
        .strip_suffix(ROOT_IN_TMP)
        .and_then(|tmp| tmp.strip_suffix('/'))
        .expect("the root sits at ROOT_IN_TMP");
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
fn point_fingerprint(point: &Point, root: &str, environment: &str, layout: &str) -> String {
    fnv1a(&format!(
        "{}\n--\n{}\n--\n{environment}\n--\n{layout}",
        placeholder(&point.xml, root),
        point_meta(point, root)
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
    // The points and their layout, never laid out: the keys are of inputs.
    let keys = |parent: &std::path::Path| -> Vec<(String, String)> {
        let fixture = Fixture::new(FIXED_SEED, parent);
        let env = environment_text(&fixture);
        let points = fixed_seed_points(&fixture);
        let layout = layout_text(&probed_names(
            points
                .iter()
                .flat_map(|(_, point)| point.probes.iter().map(String::as_str)),
            fixture.root_text(),
        ));
        points
            .into_iter()
            .map(|(key, point)| {
                let hash = point_fingerprint(&point, fixture.root_text(), &env, &layout);
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
    let mut fixture = Fixture::new(FIXED_SEED, &fixture_parent());
    let points = fixed_seed_points(&fixture);
    fixture.furnish(
        points
            .iter()
            .flat_map(|(_, point)| point.probes.iter().map(String::as_str)),
    );
    let mut world = World::new(fixture);
    let root = world.fixture.root_text().to_owned();
    let env = environment_text(&world.fixture);
    if let Some(dump) = std::env::var_os("BORZOI_PATH_FIXUP_DUMP").map(PathBuf::from) {
        std::fs::create_dir_all(&dump).unwrap();
        std::fs::write(dump.join("env.txt"), &env).unwrap();
        std::fs::write(dump.join("layout.txt"), &world.fixture.layout).unwrap();
        for (key, point) in &points {
            dump_point(&dump, key, point, &root);
        }
        // `tools/path-fixup-baseline.sh` asks for the points alone: grading
        // them against the baseline it is about to replace says nothing.
        if std::env::var_os("BORZOI_PATH_FIXUP_DUMP_ONLY").is_some() {
            return;
        }
    }
    let baseline = read_baseline();
    let (mut pins, mut regressed, mut stale) = (Vec::new(), Vec::new(), Vec::new());
    let mut violations = 0usize;
    // The claims `main` made wrongly that the walk under test does not.
    let mut righted = 0usize;
    let mut globs = GlobCoverage::default();
    for (key, point) in &points {
        let (source, site) = (point.source, point.site);
        let seen = grade(&mut world, point);
        globs.count(point, &seen);
        violations += seen.violations.len();
        let hash = point_fingerprint(point, &root, &env, &world.fixture.layout);
        let Some(row) = baseline.get(key).filter(|row| row.hash == hash) else {
            stale.push(key.clone());
            continue;
        };
        // Each start's answer, in the `{ROOT}`/`{UEXT}` spelling the
        // baseline's claims are in.
        let answers: Vec<(&str, Option<Vec<String>>)> = point
            .starts
            .iter()
            .zip(&seen.theirs)
            .map(|(&start, answer)| (world.starts[start].label, placeheld(answer, &root)))
            .collect();
        righted += row
            .claims
            .iter()
            .filter(|(mode, claim)| {
                let graded: Vec<&str> = match mode.strip_prefix("s:") {
                    None => answers.iter().map(|(label, _)| *label).collect(),
                    Some(label) => vec![label],
                };
                newly_wrong(claim, &graded, &answers).len() < graded.len()
                    && !seen.violations.iter().any(|ours| ours.mode == **mode)
            })
            .count();
        for violation in &seen.violations {
            let main_claim = row.claims.get(&violation.mode).map_or("-", String::as_str);
            let newly = newly_wrong(main_claim, &violation.starts, &answers);
            if newly.is_empty() {
                // With every start whose answer contradicts the claim: one no
                // start holding no segment contradicts is wrong only where
                // the startup directory moves it (#993).
                pins.push((
                    format!("{key} {}", violation.mode),
                    format!(
                        "{source:?}/{site:?} from {}",
                        violation.contradicted_from.join(",")
                    ),
                ));
            } else {
                regressed.push(format!(
                    "{key} {} (main claims {main_claim}), newly wrong from {}: {}",
                    violation.mode,
                    newly.join(","),
                    violation.message
                ));
            }
        }
    }
    eprintln!(
        "path fixup fixed seed: {violations} wrong claims, {} shared with main; \
         {righted} of main's wrong claims the walk does not make",
        pins.len()
    );
    eprintln!(
        "item globs that found a file: {}, of them beside an Exclude that removed one: {}; \
         relative names the full starts hold: {}",
        globs.found,
        globs.found_beside_exclude,
        world
            .fixture
            .layout
            .lines()
            .find_map(|line| line.strip_prefix("dir\tcwd-full"))
            .map_or(0, |names| names.matches('\t').count())
    );
    assert!(
        globs.found > 0 && globs.found_beside_exclude > 0,
        "the fixed seed grades no glob that finds a file, or none beside an Exclude"
    );
    // A row no point visits is coverage the sweep lost without saying so.
    let generated: std::collections::HashSet<&str> =
        points.iter().map(|(key, _)| key.as_str()).collect();
    let mut unvisited: Vec<&str> = baseline
        .keys()
        .map(String::as_str)
        .filter(|key| !generated.contains(key))
        .collect();
    unvisited.sort_unstable();
    assert!(
        stale.is_empty() && unvisited.is_empty(),
        "the baseline does not hold {} of the points this sweep generates (first {:?}), and \
         holds {} it does not generate (first {:?}): regenerate it with \\
         `bash tools/path-fixup-baseline.sh $(git merge-base HEAD origin/main)`",
        stale.len(),
        stale.first(),
        unvisited.len(),
        unvisited.first()
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
/// conditions on them in the project as decided there, so the assembly name
/// one of them gates, and the target names composed from it, too.
const SDK_WRONG_CLAIMS: &[(&str, &str, &str)] = &[
    ("served", "BaseIntermediateOutputPath", "project"),
    ("supplied", "BaseIntermediateOutputPath", "project"),
    ("served", "_InitialBaseIntermediateOutputPath", "project"),
    ("supplied", "_InitialBaseIntermediateOutputPath", "project"),
    ("served", "BaseOutputPath", "project"),
    ("supplied", "BaseOutputPath", "project"),
    ("served", "AssemblyName", "project"),
    ("supplied", "AssemblyName", "project"),
    ("served", "TargetName", "project"),
    ("supplied", "TargetName", "project"),
    ("served", "TargetFileName", "project"),
    ("supplied", "TargetFileName", "project"),
    ("served", "Moved", "project"),
    ("supplied", "Moved", "project"),
    ("served", "BaseIntermediateOutputPath", "full"),
    ("supplied", "BaseIntermediateOutputPath", "full"),
    ("served", "_InitialBaseIntermediateOutputPath", "full"),
    ("supplied", "_InitialBaseIntermediateOutputPath", "full"),
    ("served", "BaseOutputPath", "full"),
    ("supplied", "BaseOutputPath", "full"),
    ("served", "AssemblyName", "full"),
    ("supplied", "AssemblyName", "full"),
    ("served", "TargetName", "full"),
    ("supplied", "TargetName", "full"),
    ("served", "TargetFileName", "full"),
    ("supplied", "TargetFileName", "full"),
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
    // Empty directory imports, so that neither side reads the host's from
    // above the temporary directory.
    for name in [
        "Directory.Build.props",
        "Directory.Build.targets",
        "Directory.Packages.props",
    ] {
        std::fs::write(root.join(name), "<Project />").unwrap();
    }
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
               <AssemblyName Condition=\"'$(Moved)' == 'yes'\">Moved</AssemblyName>\n  \
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
    let names: Vec<&str> = answers
        .iter()
        .map(|(_, answer)| answer["AssemblyName"].as_str())
        .collect();
    assert_eq!(
        names,
        ["Moved", "App", "Moved"],
        "MSBuild's assembly names by start"
    );
}
