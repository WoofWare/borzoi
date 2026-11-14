//! Metamorphic gate: **an uncertain document claims no more than its worlds
//! agree on.**
//!
//! The five MSBuild differentials check that a committed value is MSBuild's.
//! None of them can check that the walker *declines* where it is unsure: a
//! wrong decline and a right one both agree with the oracle, and a value whose
//! uncertainty was laundered agrees with it too whenever the laundered input
//! happens to be right. This harness checks the other half of
//! certain-implies-exact against the walker itself, with no oracle
//! (`docs/msbuild-value-carried-provenance-plan.md`, "The systematic gate").
//!
//! For a generated document `D` and one construct `c` in it, put `c` behind
//! something the walker cannot decide, giving `D′`. The real build then sees
//! one of a small set of *worlds* — `D` with `c` taken, `D` with `c` not taken,
//! or `D` with `c`'s value replaced — and the walker cannot tell which. So for
//! every fact `D′` publishes as certain (a property not in
//! `untrusted_properties`, the Compile items while `items_uncertain` is clear,
//! `define_constants` while `define_constants_uncertain` is clear, the
//! `ProjectReference` list while `project_references_uncertain` is clear, a
//! known `target_name`), **every world must publish the same fact, certain,
//! with the same value**. A world that differs means `D′` committed a value it
//! could not know; a world that declines means `D′` claimed more than a
//! document strictly easier to evaluate.
//!
//! Each world is evaluated by the walker too, so the property is
//! monotonicity, not exactness: it holds the trust lattice to the dependence
//! the expansion actually has, whatever route (a member access, a nested
//! argument, a condition, a skipped write, a copy of a copy) carried it.
//!
//! The derived complement is floored, not the swept input: what keeps the gate
//! from passing vacuously is the number of cases in which the worlds disagree
//! about a fact both commit — a decline `D′` *owes* — per kind of fact.

mod common;

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::{ItemMetadataValue, ParsedProject, parse_fsproj, parse_fsproj_with_imports};
use common::{
    CONTROLLED_PROPERTY_NAMES, SplitMix64, gen_bool_expr, gen_expand_value, gen_grammar_value,
    soak_parameters,
};

/// A condition MSBuild evaluates to `true` and the walker cannot evaluate.
const UNDECIDABLE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";
/// A property body MSBuild evaluates and the walker refuses (`Substring` is
/// outside the modelled members), so it stores no value.
const REFUSED_BODY: &str = "$(Configuration.Substring(0,1))";
/// The values a refused body's world may hold instead. The refused write's
/// real value is unknown, so a fact certain under the refusal must be the same
/// under each of these.
const REPLACEMENTS: &[&str] = &["", "a", "true", "false", "net8.0", "1.2.3", "Debug"];

/// Properties a `Directory.Build.targets` splice writes rather than the
/// generated document: the fixture's own write, and the path the splice
/// records.
const SPLICE_WRITTEN: &[&str] = &["FromDirBuild", "DirectoryBuildTargetsPath"];

/// The two inputs the `Directory.Build.targets` splice decides on.
const SPLICE_GATES: [&str; 2] = ["ImportDirectoryBuildTargets", "DirectoryBuildTargetsPath"];

/// The names the generated documents write: the shared expression grammar's
/// names, so its bodies read what the documents write, plus the names three
/// published facets are computed from.
fn written_names(with_gates: bool) -> Vec<&'static str> {
    let mut names: Vec<&'static str> = CONTROLLED_PROPERTY_NAMES.to_vec();
    names.extend(["DefineConstants", "TargetName", "AssemblyName"]);
    if with_gates {
        names.extend(SPLICE_GATES);
    }
    names
}

#[derive(Clone, Debug)]
struct Write {
    name: &'static str,
    group_condition: Option<String>,
    condition: Option<String>,
    body: String,
}

#[derive(Clone, Debug)]
struct Item {
    kind: &'static str,
    group_condition: Option<String>,
    condition: Option<String>,
    include: String,
}

#[derive(Clone, Debug)]
struct Doc {
    writes: Vec<Write>,
    items: Vec<Item>,
}

/// How the target write is made undecidable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Wrap {
    /// An undecidable conjunct on the write's own `Condition`.
    ElementCondition,
    /// An undecidable conjunct on the enclosing `<PropertyGroup>`.
    GroupCondition,
    /// The write's group moved into an undecidable `<Choose>` arm.
    ChooseWhen,
    /// The write's body replaced by one the walker refuses to evaluate.
    RefusedBody,
}

const WRAPS: [Wrap; 4] = [
    Wrap::ElementCondition,
    Wrap::GroupCondition,
    Wrap::ChooseWhen,
    Wrap::RefusedBody,
];

/// What happens to the target write when a document is rendered.
#[derive(Clone, Debug)]
enum Variant {
    /// As generated: the world where the gate ran.
    Taken,
    /// Left out: the world where the gate did not run.
    Omitted,
    /// With this body: a world for a refused body.
    Replaced(&'static str),
    /// Undecidable to the walker: the document under test.
    Undecided(Wrap),
}

fn gen_condition(rng: &mut SplitMix64, names: &[&'static str]) -> String {
    const LITERALS: &[&str] = &["", "a", "true", "false", "net8.0", "Debug", "1.2.3"];
    let name = *rng.pick(names);
    match rng.below(8) {
        0 => format!("'$({name})' == ''"),
        1 => format!("'$({name})' != ''"),
        2 => format!("'$({name})' == '{}'", rng.pick(LITERALS)),
        3 => format!("'$({name}.Length)' == '{}'", rng.below(8)),
        4 => format!(
            "$({name}.StartsWith('{}'))",
            rng.pick(&["n", "a", "D", "t"])
        ),
        5 => format!("'$({name}.ToString())' == '{}'", rng.pick(LITERALS)),
        _ => gen_bool_expr(rng, 1),
    }
}

fn gen_body(rng: &mut SplitMix64, names: &[&'static str]) -> String {
    const LITERALS: &[&str] = &["", "a", "true", "false", "net8.0", "Debug", "1.2.3", "x;y"];
    let name = *rng.pick(names);
    match rng.below(10) {
        0..=1 => (*rng.pick(LITERALS)).to_string(),
        2..=3 => format!("$({name})"),
        4 => format!("{}$({name})", rng.pick(LITERALS)),
        5 => format!("$({name}.Length)"),
        6 => gen_grammar_value(rng),
        _ => gen_expand_value(rng),
    }
}

fn maybe(
    rng: &mut SplitMix64,
    percent: usize,
    f: impl FnOnce(&mut SplitMix64) -> String,
) -> Option<String> {
    (rng.below(100) < percent).then(|| f(rng))
}

fn writes_names(writes: &[Write]) -> Vec<&'static str> {
    writes.iter().map(|w| w.name).collect()
}

fn gen_doc(rng: &mut SplitMix64, names: &[&'static str]) -> Doc {
    // Each document writes a few names, often more than once, so the
    // undecided write is often one that overwrites a value already held — the
    // case where trust, not the absence of a binding, is all that records the
    // doubt.
    let (gates, others): (Vec<&'static str>, Vec<&'static str>) =
        names.iter().partition(|n| SPLICE_GATES.contains(n));
    let mut pool = others;
    while pool.len() > 3 + rng.below(3) {
        pool.swap_remove(rng.below(pool.len()));
    }
    // The splice's inputs stay in every pool that has them: they are what
    // the `Directory.Build.targets` tier exists to exercise.
    pool.extend(gates);
    let writes: Vec<Write> = (0..2 + rng.below(6))
        .map(|_| {
            let readers = if rng.below(4) == 0 { names } else { &pool[..] };
            Write {
                name: *rng.pick(&pool),
                group_condition: maybe(rng, 15, |rng| gen_condition(rng, readers)),
                condition: maybe(rng, 30, |rng| gen_condition(rng, readers)),
                body: gen_body(rng, readers),
            }
        })
        .collect();
    // Items lean on the names the document actually writes, so that the
    // undecided write reaches an item facet often enough to floor.
    let written: Vec<&'static str> = writes_names(&writes);
    let items = (0..1 + rng.below(4))
        .map(|_| {
            let kind = if rng.below(4) == 0 {
                "ProjectReference"
            } else {
                "Compile"
            };
            let suffix = if kind == "Compile" { ".fs" } else { ".fsproj" };
            let readers = if rng.below(2) == 0 {
                &written[..]
            } else {
                names
            };
            Item {
                kind,
                group_condition: maybe(rng, 20, |rng| gen_condition(rng, readers)),
                condition: maybe(rng, 30, |rng| gen_condition(rng, readers)),
                include: format!("{}{suffix}", gen_body(rng, readers)),
            }
        })
        .collect();
    Doc { writes, items }
}

fn attr(condition: Option<&str>) -> String {
    condition
        .map(|c| format!(" Condition=\"{}\"", xml_escape(c)))
        .unwrap_or_default()
}

fn xml_escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

fn with_undecidable(condition: Option<&str>) -> String {
    match condition {
        Some(c) => format!("({c}) And {UNDECIDABLE}"),
        None => UNDECIDABLE.to_string(),
    }
}

fn render(doc: &Doc, target: usize, variant: &Variant) -> String {
    let mut out = String::from("<Project>\n");
    for (i, write) in doc.writes.iter().enumerate() {
        let mut group = write.group_condition.clone();
        let mut condition = write.condition.clone();
        let mut body = write.body.clone();
        let mut choose = false;
        if i == target {
            match variant {
                Variant::Taken => {}
                Variant::Omitted => continue,
                Variant::Replaced(value) => body = (*value).to_string(),
                Variant::Undecided(Wrap::ElementCondition) => {
                    condition = Some(with_undecidable(condition.as_deref()));
                }
                Variant::Undecided(Wrap::GroupCondition) => {
                    group = Some(with_undecidable(group.as_deref()));
                }
                Variant::Undecided(Wrap::ChooseWhen) => choose = true,
                Variant::Undecided(Wrap::RefusedBody) => body = REFUSED_BODY.to_string(),
            }
        }
        let element = format!(
            "    <{name}{cond}>{body}</{name}>\n",
            name = write.name,
            cond = attr(condition.as_deref()),
            body = xml_escape(&body),
        );
        let group = format!(
            "  <PropertyGroup{}>\n{element}  </PropertyGroup>\n",
            attr(group.as_deref())
        );
        if choose {
            out.push_str(&format!(
                "  <Choose>\n    <When Condition=\"{}\">\n{group}    </When>\n  </Choose>\n",
                xml_escape(UNDECIDABLE)
            ));
        } else {
            out.push_str(&group);
        }
    }
    for item in &doc.items {
        out.push_str(&format!(
            "  <ItemGroup{}>\n    <{kind} Include=\"{include}\"{cond} />\n  </ItemGroup>\n",
            attr(item.group_condition.as_deref()),
            kind = item.kind,
            include = xml_escape(&item.include),
            cond = attr(item.condition.as_deref()),
        ));
    }
    out.push_str("</Project>\n");
    out
}

/// What a project publishes as certain, fact by fact: `None` where it
/// declines.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Fact {
    Property(String),
    CompileItems,
    ProjectReferences,
    DefineConstants,
    TargetName,
}

fn facts(project: &ParsedProject, names: &[&'static str]) -> BTreeMap<Fact, Option<Vec<String>>> {
    let mut out = BTreeMap::new();
    // `FromDirBuild` is written by the `Directory.Build.targets` fixture only.
    for name in names.iter().chain(&["FromDirBuild"]) {
        let certain = !project.property_provenance_untrusted(name);
        let value = project
            .properties
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.clone());
        out.insert(
            Fact::Property(name.to_string()),
            certain.then(|| vec![format!("{value:?}")]),
        );
    }
    let paths = |items: &[borzoi_msbuild::ResolvedItem]| {
        vec![format!(
            "{:?}",
            items
                .iter()
                .map(|i| i.include.clone())
                .collect::<Vec<PathBuf>>()
        )]
    };
    out.insert(
        Fact::CompileItems,
        (!project.items_uncertain).then(|| paths(&project.items)),
    );
    out.insert(
        Fact::ProjectReferences,
        (!project.project_references_uncertain).then(|| {
            project
                .project_references
                .iter()
                .map(|i| i.include.display().to_string())
                .collect()
        }),
    );
    out.insert(
        Fact::DefineConstants,
        (!project.define_constants_uncertain)
            .then(|| vec![format!("{:?}", project.define_constants)]),
    );
    out.insert(
        Fact::TargetName,
        match &project.target_name {
            ItemMetadataValue::Known(name) => Some(vec![format!("{name:?}")]),
            ItemMetadataValue::Unknown => None,
        },
    );
    out
}

impl Fact {
    /// Whether a world publishing `world` agrees with a certain `claim`. Every
    /// facet is claimed exactly but one: the `ProjectReference` list promises
    /// no phantom edge and tolerates a missing one (an `Include` behind an
    /// untrusted gate is left out without declining), so its claim holds when
    /// every edge it names is one the world has.
    fn claim_holds_in(&self, claim: &[String], world: &[String]) -> bool {
        match self {
            Fact::ProjectReferences => claim.iter().all(|edge| world.contains(edge)),
            _ => world == claim,
        }
    }
}

fn fact_kind(fact: &Fact) -> &'static str {
    match fact {
        Fact::Property(_) => "property",
        Fact::CompileItems => "Compile items",
        Fact::ProjectReferences => "ProjectReference items",
        Fact::DefineConstants => "DefineConstants",
        Fact::TargetName => "target name",
    }
}

/// Tallies across a sweep: how often each kind of fact owed a decline, and
/// the violations found.
#[derive(Default)]
struct Census {
    cases: usize,
    /// Per fact kind: cases whose worlds commit the fact differently, so the
    /// undecided document must decline it.
    owed: BTreeMap<&'static str, usize>,
    /// Per fact kind: of those, how many the undecided document declined.
    paid: BTreeMap<&'static str, usize>,
    violations: Vec<String>,
    violation_count: usize,
    /// Cases set aside as the known refused-write defect (see [`check`]).
    refused_absent: usize,
    /// Cases set aside as the known splice-value defect (see [`check`]).
    spliced_values: usize,
    /// Certain facts some world declined while the rest agreed.
    world_declined: usize,
}

impl Census {
    fn print(&self, label: &str) {
        println!(
            "{label}: {} cases, {} refused-write absences and {} splice values set aside, \
             {} commits a world declined",
            self.cases, self.refused_absent, self.spliced_values, self.world_declined
        );
        for (kind, owed) in &self.owed {
            println!(
                "  {kind}: {owed} owed declines, {} paid",
                self.paid.get(kind).copied().unwrap_or(0)
            );
        }
    }
}

/// Check one undecided document against its worlds, recording into `census`.
///
/// A certain fact must be published, with the same value, by every world that
/// publishes it certain, and at least one world must. A world that declines
/// what the undecided document commits is not itself a violation: the worlds
/// are evaluated by the walker too, and a world can decline for a reason that
/// cannot move this fact (an untrusted gate over a write whose own condition
/// is exactly false, say). Those cases are counted, not failed.
fn check(
    census: &mut Census,
    doc_text: &str,
    undecided: &BTreeMap<Fact, Option<Vec<String>>>,
    worlds: &[(String, BTreeMap<Fact, Option<Vec<String>>>)],
    absent_but_written: &[&str],
    label: &str,
) {
    census.cases += 1;
    for (fact, claim) in undecided {
        let values: Vec<&Option<Vec<String>>> = worlds.iter().map(|(_, w)| &w[fact]).collect();
        let world_committed: Vec<&Vec<String>> = values.iter().filter_map(|v| v.as_ref()).collect();
        let owed = world_committed.len() == values.len()
            && world_committed.windows(2).any(|w| w[0] != w[1]);
        if owed {
            *census.owed.entry(fact_kind(fact)).or_default() += 1;
            if claim.is_none() {
                *census.paid.entry(fact_kind(fact)).or_default() += 1;
            }
        }
        let Some(claim) = claim else { continue };
        // A refused write leaves its name out of both `properties` and
        // `untrusted_properties`, so the walker publishes "never written" for
        // a name the real build holds a value for, and `target_name` falls
        // through a refused `TargetName` or `AssemblyName` as though it were
        // unset. That is a defect, tracked as #780; it is counted
        // rather than reported here so the gate stays a gate for everything
        // else, and so the count says when the fix lands.
        let absent = |name: &str| {
            absent_but_written
                .iter()
                .any(|n| n.eq_ignore_ascii_case(name))
        };
        let rests_on_a_refused_absence = match fact {
            Fact::Property(name) => absent(name),
            Fact::TargetName => absent("TargetName") || absent("AssemblyName"),
            // An item gate reads a refused name as never written too.
            Fact::ProjectReferences => !absent_but_written.is_empty(),
            _ => false,
        };
        let disagreeing = worlds
            .iter()
            .find(|(_, facts)| {
                facts[fact]
                    .as_ref()
                    .is_some_and(|world| !fact.claim_holds_in(claim, world))
            })
            .map(|(world, facts)| (world.clone(), facts[fact].clone()));
        let nobody_commits = world_committed.is_empty();
        if disagreeing.is_none() && !nobody_commits {
            if world_committed.len() < values.len() {
                census.world_declined += 1;
            }
            continue;
        }
        if rests_on_a_refused_absence {
            census.refused_absent += 1;
            continue;
        }
        // A `Directory.Build.*` splice decided on an untrusted gate withdraws
        // the item facets, but the values the spliced file writes — and the
        // path property the splice itself writes — stay certain, though the
        // real build may not import the file at all. A defect, tracked as
        // #781, and set aside the same way.
        let written_by_an_undecided_splice = matches!(
            fact,
            Fact::Property(name) if SPLICE_WRITTEN.iter().any(|n| n.eq_ignore_ascii_case(name))
        ) && undecided[&Fact::CompileItems].is_none();
        if written_by_an_undecided_splice {
            census.spliced_values += 1;
            continue;
        }
        census.violation_count += 1;
        if census.violations.len() < 8 {
            let why = match disagreeing {
                Some((world, published)) => format!("the world `{world}` publishes {published:?}"),
                None => "no world publishes it certain".to_string(),
            };
            census.violations.push(format!(
                "{label}: {fact:?} committed as {claim:?} under the undecided construct, \
                 but {why}\n--- undecided document ---\n{doc_text}"
            ));
        }
    }
}

/// The worlds a wrap leaves the real build choosing between.
fn worlds_for(wrap: Wrap) -> Vec<Variant> {
    match wrap {
        Wrap::RefusedBody => REPLACEMENTS.iter().map(|v| Variant::Replaced(v)).collect(),
        _ => vec![Variant::Taken, Variant::Omitted],
    }
}

fn sweep(
    seed: u64,
    cases: usize,
    names: &[&'static str],
    evaluate: &dyn Fn(&str) -> ParsedProject,
    label: &str,
) -> Census {
    let mut rng = SplitMix64(seed);
    let mut census = Census::default();
    for _ in 0..cases {
        let doc = gen_doc(&mut rng, names);
        let target = rng.below(doc.writes.len());
        for wrap in WRAPS {
            let world_facts: Vec<(String, BTreeMap<Fact, Option<Vec<String>>>)> = worlds_for(wrap)
                .into_iter()
                .map(|variant| {
                    let text = render(&doc, target, &variant);
                    (format!("{variant:?}"), facts(&evaluate(&text), names))
                })
                .collect();
            let text = render(&doc, target, &Variant::Undecided(wrap));
            let project = evaluate(&text);
            let undecided = facts(&project, names);
            let absent_but_written: Vec<&str> = doc
                .writes
                .iter()
                .map(|w| w.name)
                .filter(|name| {
                    !project
                        .properties
                        .keys()
                        .any(|k| k.eq_ignore_ascii_case(name))
                })
                .collect();
            check(
                &mut census,
                &text,
                &undecided,
                &world_facts,
                &absent_but_written,
                &format!("{label} {wrap:?}"),
            );
        }
    }
    census
}

fn pure_evaluate(text: &str) -> ParsedProject {
    parse_fsproj(
        text,
        Path::new("/metamorphic/Demo.fsproj"),
        &HashMap::new(),
        &HashMap::new(),
    )
    .expect("generated documents are well-formed")
}

/// A directory holding a `Directory.Build.targets` that contributes a Compile
/// item, so the generated `ImportDirectoryBuildTargets` /
/// `DirectoryBuildTargetsPath` writes decide whether a file joins the walk.
struct DirectoryBuildFixture {
    _dir: tempfile::TempDir,
    project: PathBuf,
}

impl DirectoryBuildFixture {
    fn new() -> Self {
        let dir = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(dir.path()).unwrap();
        std::fs::write(
            root.join("Directory.Build.targets"),
            r#"<Project><PropertyGroup><FromDirBuild>set</FromDirBuild></PropertyGroup><ItemGroup><Compile Include="FromDirBuild.fs" /></ItemGroup></Project>"#,
        )
        .unwrap();
        Self {
            _dir: dir,
            project: root.join("Demo.fsproj"),
        }
    }

    fn evaluate(&self, text: &str) -> ParsedProject {
        parse_fsproj_with_imports(
            text,
            &self.project,
            &HashMap::new(),
            &HashMap::new(),
            None,
            None,
        )
        .expect("generated documents are well-formed")
    }
}

fn assert_sound(census: &Census, floors: &[(&str, usize)]) {
    assert!(
        census.violation_count == 0,
        "{} uncertainty laundered into a certain fact (first {} shown):\n\n{}",
        census.violation_count,
        census.violations.len(),
        census.violations.join("\n\n")
    );
    for (kind, floor) in floors {
        let owed = census.owed.get(kind).copied().unwrap_or(0);
        assert!(
            owed >= *floor,
            "only {owed} cases owed a decline of the {kind} facet (floor {floor}): the \
             generator no longer reaches that facet's dependence, so the gate is vacuous there",
        );
    }
}

/// The set-aside counts, pinned for the fixed seeds: a fix for #780 or #781
/// moves them, and must update them here (and drop the set-aside once it
/// reaches zero), so the gate cannot quietly keep exempting a class that no
/// longer exists — or one that grew.
fn assert_set_asides(census: &Census, refused_absent: usize, spliced_values: usize) {
    assert_eq!(
        (census.refused_absent, census.spliced_values),
        (refused_absent, spliced_values),
        "the (#780 refused-absence, #781 splice-value) set-aside counts moved"
    );
}

/// The floors are about half what the fixed seed produces, so a generator
/// change that stops reaching a facet fails here instead of passing
/// vacuously. `ProjectReference` has none: its contract tolerates a missing
/// edge, so a decline is never owed there, only the absence of a phantom.
#[test]
fn an_undecided_write_claims_no_more_than_its_worlds_agree_on() {
    let names = written_names(false);
    let census = sweep(0x5eed_7a17, 1000, &names, &pure_evaluate, "pure");
    census.print("pure walk");
    assert_sound(
        &census,
        &[
            ("property", 850),
            ("Compile items", 70),
            ("DefineConstants", 60),
            ("target name", 100),
        ],
    );
    assert_set_asides(&census, 532, 0);
}

#[test]
fn an_undecided_directory_build_gate_write_claims_no_more_than_its_worlds_agree_on() {
    let names = written_names(true);
    let fixture = DirectoryBuildFixture::new();
    let census = sweep(
        0x0d1b_7a17,
        400,
        &names,
        &|text| fixture.evaluate(text),
        "Directory.Build",
    );
    census.print("with Directory.Build.targets");
    assert_sound(
        &census,
        &[
            ("property", 450),
            ("Compile items", 75),
            ("DefineConstants", 25),
        ],
    );
    assert_set_asides(&census, 240, 163);
}

/// The fresh-seed twin of the two sweeps above. Seed 1 at 4 000 cases finds
/// #782 (a single-witness root lets the `DefineConstants` self-append
/// exemption drop an independent cause), which the fixed seeds do not reach.
#[test]
#[ignore = "soak: run with --ignored; BORZOI_MSBUILD_SOAK_SEED reproduces"]
fn soak_undecided_writes_claim_no_more_than_their_worlds() {
    let (seed, cases) = soak_parameters("taint_closure_metamorphic", 5_000);
    let census = sweep(seed, cases, &written_names(false), &pure_evaluate, "pure");
    census.print("pure walk");
    assert_sound(&census, &[]);
    let fixture = DirectoryBuildFixture::new();
    let census = sweep(
        seed,
        cases / 4,
        &written_names(true),
        &|text| fixture.evaluate(text),
        "Directory.Build",
    );
    census.print("with Directory.Build.targets");
    assert_sound(&census, &[]);
}

// The defects the gate found, each pinned as the answer it should give, and
// ignored with its issue until fixed.

/// #780: a refused write is published as never written.
#[test]
#[ignore = "#780: a refused property write reads as never written"]
fn a_refused_write_is_not_published_as_never_written() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><TargetName>$(Configuration.Substring(0,1))</TargetName></PropertyGroup>
</Project>"#,
    );
    assert!(
        project.property_provenance_untrusted("TargetName"),
        "MSBuild computes `TargetName`; an absent, trusted name says the project never wrote it"
    );
    assert_eq!(project.target_name, ItemMetadataValue::Unknown);
}

/// #780: an item gate reads a refused name as never written, capturing a
/// phantom `ProjectReference`.
#[test]
#[ignore = "#780: a refused property write reads as never written"]
fn a_project_reference_gated_on_a_refused_name_is_not_certain() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><Bar>$(Configuration.Substring(0,1))</Bar></PropertyGroup>
  <ItemGroup Condition="'$(Bar)' == ''"><ProjectReference Include="x.fsproj" /></ItemGroup>
</Project>"#,
    );
    assert!(
        project.project_references_uncertain || project.project_references.is_empty(),
        "MSBuild computes `Bar` and skips the group; we captured {:?} as certain",
        project.project_references
    );
}

/// #781: a `Directory.Build.targets` spliced on an undecided gate publishes
/// its writes as trusted.
#[test]
#[ignore = "#781: a Directory.Build file spliced on an undecided gate publishes its writes as trusted"]
fn a_file_spliced_on_an_undecided_gate_publishes_no_trusted_value() {
    let fixture = DirectoryBuildFixture::new();
    let project = fixture.evaluate(&format!(
        r#"<Project>
  <PropertyGroup>
    <ImportDirectoryBuildTargets Condition="{UNDECIDABLE}">false</ImportDirectoryBuildTargets>
  </PropertyGroup>
</Project>"#
    ));
    assert!(
        project.items_uncertain,
        "P2″ already withdraws the item facets"
    );
    assert!(
        project.property_provenance_untrusted("FromDirBuild"),
        "MSBuild writes the gate `false` and never imports the file"
    );
}

/// #782: a single-witness root lets the `DefineConstants` self-append
/// exemption drop an independent cause.
#[test]
#[ignore = "#782: a single-witness root drops a cause the self-append exemption cannot see"]
fn a_copied_define_constants_root_does_not_hide_a_gate() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><TargetName>$(Configuration.Substring(0,1))</TargetName></PropertyGroup>
  <PropertyGroup>
    <P1 Condition="'$(TargetName)' == ''">$(DefineConstants.Length)</P1>
  </PropertyGroup>
  <PropertyGroup><DefineConstants>x$(P1.EndsWith('0'))</DefineConstants></PropertyGroup>
</Project>"#,
    );
    assert!(
        project.define_constants_uncertain,
        "MSBuild skips `P1`'s write, so `DefineConstants` is `xFalse`; we published {:?}",
        project.define_constants
    );
}
