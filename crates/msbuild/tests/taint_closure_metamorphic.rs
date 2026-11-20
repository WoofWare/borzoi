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
//! every fact `D′` publishes as certain (a property read as a value or as
//! unset, the Compile items while `items_uncertain` is clear,
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
use borzoi_msbuild::{
    InexactUnset, ItemMetadataValue, ParsedProject, PropertyRead, SdkPaths, SdkResolution,
    SdkResolveError, parse_fsproj,
};
use common::{
    CONTROLLED_PROPERTY_NAMES, SplitMix64, gen_bool_expr, gen_expand_value,
    gen_grammar_value_spelled, parse_fsproj_with_imports, soak_parameters,
};

/// A condition MSBuild evaluates to `true` and the walker cannot evaluate.
const UNDECIDABLE: &str = "'É' == 'é'";
/// A property body MSBuild evaluates and the walker refuses (`Substring` is
/// outside the modelled members), so it stores no value.
const REFUSED_BODY: &str = "$(Configuration.Substring(0,1))";
/// The values a refused body's world may hold instead. The refused write's
/// real value is unknown, so a fact certain under the refusal must be the same
/// under each of these.
const REPLACEMENTS: &[&str] = &["", "a", "true", "false", "net8.0", "1.2.3", "Debug"];

/// The Compile item the `Directory.Build.targets` fixture contributes.
const DIR_BUILD_ITEM: &str = "FromDirBuild.fs";

/// The two inputs the `Directory.Build.targets` import decides on.
const IMPORT_POINT_INPUTS: [&str; 2] = ["ImportDirectoryBuildTargets", "DirectoryBuildTargetsPath"];

/// The names the generated documents write: the shared expression grammar's
/// names, so its bodies read what the documents write, plus the names three
/// published facets are computed from.
fn written_names(with_gates: bool) -> Vec<&'static str> {
    let mut names: Vec<&'static str> = CONTROLLED_PROPERTY_NAMES.to_vec();
    names.extend(["DefineConstants", "TargetName", "AssemblyName"]);
    if with_gates {
        names.extend(IMPORT_POINT_INPUTS);
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
        6 => gen_grammar_value_spelled(rng),
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
        names.iter().partition(|n| IMPORT_POINT_INPUTS.contains(n));
    let mut pool = others;
    while pool.len() > 3 + rng.below(3) {
        pool.swap_remove(rng.below(pool.len()));
    }
    // The import's inputs stay in every pool that has them: they are what
    // the `Directory.Build.targets` tier exists to exercise.
    pool.extend(gates);
    let writes: Vec<Write> = (0..2 + rng.below(6))
        .map(|_| {
            let readers = if rng.below(4) == 0 { names } else { &pool[..] };
            Write {
                name: rng.pick(&pool),
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
type Facts = BTreeMap<Fact, Option<Vec<String>>>;

/// One fact a project may publish as certain.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Fact {
    Property(String),
    CompileItems,
    ProjectReferences,
    DefineConstants,
    TargetName,
}

fn facts(project: &ParsedProject, names: &[&'static str]) -> Facts {
    let mut out = BTreeMap::new();
    // `FromDirBuild` is written by the `Directory.Build.targets` fixture only.
    for name in names.iter().chain(&["FromDirBuild"]) {
        let claim = match project.property(name) {
            PropertyRead::Value(value) => Some(Some(value)),
            PropertyRead::Unset => Some(None),
            PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
        };
        out.insert(
            Fact::Property(name.to_string()),
            claim.map(|value| vec![format!("{value:?}")]),
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

    /// Whether `claim` holds in every world whatever the world publishes: an
    /// empty `ProjectReference` list names no edge, so it can hold no phantom
    /// one. Such a claim needs no world to commit it.
    fn claim_is_vacuous(&self, claim: &[String]) -> bool {
        matches!(self, Fact::ProjectReferences) && claim.is_empty()
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
    /// undecided document must decline it — the wrapped write's own property
    /// excluded, so this counts dependence on it rather than the input.
    owed: BTreeMap<&'static str, usize>,
    /// Per fact kind: of those, how many the undecided document declined.
    paid: BTreeMap<&'static str, usize>,
    violations: Vec<String>,
    violation_count: usize,
    /// Per fact kind: the violations found.
    violated: BTreeMap<&'static str, usize>,
    /// Certain facts some world declined while the rest agreed.
    world_declined: usize,
}

impl Census {
    fn print(&self, label: &str) {
        println!(
            "{label}: {} cases, {} commits a world declined",
            self.cases, self.world_declined
        );
        for (kind, owed) in &self.owed {
            println!(
                "  {kind}: {owed} owed declines, {} paid, {} violations",
                self.paid.get(kind).copied().unwrap_or(0),
                self.violated.get(kind).copied().unwrap_or(0)
            );
        }
    }
}

/// The construct a case made undecidable.
#[derive(Clone, Copy)]
enum Undecided<'a> {
    /// A property write, of this name.
    Write(&'a str),
    /// An import in the SDK, of content that may redefine what was written
    /// before it.
    Import,
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
    undecided: &Facts,
    worlds: &[(String, Facts)],
    undecided_construct: Undecided<'_>,
    label: &str,
) {
    census.cases += 1;
    for (fact, claim) in undecided {
        // The floor counts only the derived complement: the wrapped write's
        // own name moves by construction, so counting it would floor the
        // swept input rather than the dependence on it.
        let derived = !matches!(
            (fact, undecided_construct),
            (Fact::Property(name), Undecided::Write(wrapped)) if name.eq_ignore_ascii_case(wrapped)
        );
        let values: Vec<&Option<Vec<String>>> = worlds.iter().map(|(_, w)| &w[fact]).collect();
        let world_committed: Vec<&Vec<String>> = values.iter().filter_map(|v| v.as_ref()).collect();
        let owed = world_committed.len() == values.len()
            && world_committed.windows(2).any(|w| w[0] != w[1]);
        if owed && derived {
            *census.owed.entry(fact_kind(fact)).or_default() += 1;
            if claim.is_none() {
                *census.paid.entry(fact_kind(fact)).or_default() += 1;
            }
        }
        let Some(claim) = claim else { continue };
        let disagreeing = worlds
            .iter()
            .find(|(_, facts)| {
                facts[fact]
                    .as_ref()
                    .is_some_and(|world| !fact.claim_holds_in(claim, world))
            })
            .map(|(world, facts)| (world.clone(), facts[fact].clone()));
        let nobody_commits = world_committed.is_empty() && !fact.claim_is_vacuous(claim);
        if disagreeing.is_none() && !nobody_commits {
            if world_committed.len() < values.len() {
                census.world_declined += 1;
            }
            continue;
        }
        census.violation_count += 1;
        *census.violated.entry(fact_kind(fact)).or_default() += 1;
        if census.violated[fact_kind(fact)] <= 2 {
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
        check_every_wrap(&mut census, &doc, target, names, evaluate, label);
    }
    census
}

/// Make `doc`'s write `target` undecidable in each way the walker cannot see
/// through, and check each undecided document against its worlds.
fn check_every_wrap(
    census: &mut Census,
    doc: &Doc,
    target: usize,
    names: &[&'static str],
    evaluate: &dyn Fn(&str) -> ParsedProject,
    label: &str,
) {
    for wrap in WRAPS {
        let world_facts: Vec<(String, Facts)> = worlds_for(wrap)
            .into_iter()
            .map(|variant| {
                let text = render(doc, target, &variant);
                (format!("{variant:?}"), facts(&evaluate(&text), names))
            })
            .collect();
        let text = render(doc, target, &Variant::Undecided(wrap));
        let project = evaluate(&text);
        let undecided = facts(&project, names);
        check(
            census,
            &text,
            &undecided,
            &world_facts,
            Undecided::Write(doc.writes[target].name),
            &format!("{label} {wrap:?}"),
        );
    }
}

fn pure_evaluate(text: &str) -> ParsedProject {
    parse_fsproj(
        &borzoi_msbuild::ProjectFile::buffer(Path::new("/metamorphic/Demo.fsproj"), text)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &HashMap::new(),
    )
    .expect("generated documents are well-formed")
}

/// The SDK the `Directory.Build.targets` tier's documents name: its
/// `Sdk.targets` is `Microsoft.Common.targets`'s import block, verbatim from
/// SDK 10.0.401, which is the only thing that imports the file.
const DIRECTORY_BUILD_SDK: &str = "DirectoryBuildSdk";

/// `Microsoft.Common.targets`'s `Directory.Build.targets` import block.
const COMMON_TARGETS_BLOCK: &str = r#"<Project>
  <PropertyGroup>
    <ImportDirectoryBuildTargets Condition="'$(ImportDirectoryBuildTargets)' == ''">true</ImportDirectoryBuildTargets>
  </PropertyGroup>
  <PropertyGroup Condition="'$(ImportDirectoryBuildTargets)' == 'true' and '$(DirectoryBuildTargetsPath)' == ''">
    <_DirectoryBuildTargetsFile Condition="'$(_DirectoryBuildTargetsFile)' == ''">Directory.Build.targets</_DirectoryBuildTargetsFile>
    <_DirectoryBuildTargetsBasePath Condition="'$(_DirectoryBuildTargetsBasePath)' == ''">$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), '$(_DirectoryBuildTargetsFile)'))</_DirectoryBuildTargetsBasePath>
    <DirectoryBuildTargetsPath Condition="'$(_DirectoryBuildTargetsBasePath)' != '' and '$(_DirectoryBuildTargetsFile)' != ''">$([System.IO.Path]::Combine('$(_DirectoryBuildTargetsBasePath)', '$(_DirectoryBuildTargetsFile)'))</DirectoryBuildTargetsPath>
  </PropertyGroup>
  <Import Project="$(DirectoryBuildTargetsPath)" Condition="'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')"/>
</Project>
"#;

/// A directory holding a `Directory.Build.targets` that contributes a Compile
/// item, and the SDK [`DIRECTORY_BUILD_SDK`] whose import of it the generated
/// `ImportDirectoryBuildTargets` / `DirectoryBuildTargetsPath` writes decide.
struct DirectoryBuildFixture {
    _dir: tempfile::TempDir,
    project: PathBuf,
    sdk: PathBuf,
}

impl DirectoryBuildFixture {
    fn new() -> Self {
        let dir = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(dir.path()).unwrap();
        std::fs::write(
            root.join("Directory.Build.targets"),
            format!(
                r#"<Project><PropertyGroup><FromDirBuild>set</FromDirBuild></PropertyGroup><ItemGroup><Compile Include="{DIR_BUILD_ITEM}" /></ItemGroup></Project>"#
            ),
        )
        .unwrap();
        let sdk = root.join("sdks").join(DIRECTORY_BUILD_SDK);
        std::fs::create_dir_all(&sdk).unwrap();
        std::fs::write(sdk.join("Sdk.props"), "<Project />").unwrap();
        std::fs::write(sdk.join("Sdk.targets"), COMMON_TARGETS_BLOCK).unwrap();
        Self {
            _dir: dir,
            project: root.join("Demo.fsproj"),
            sdk,
        }
    }

    /// Evaluate a generated document (a `<Project>`) under the SDK.
    fn evaluate(&self, text: &str) -> ParsedProject {
        let text = text.replacen(
            "<Project>",
            &format!("<Project Sdk=\"{DIRECTORY_BUILD_SDK}\">"),
            1,
        );
        let sdk = self.sdk.clone();
        let resolver = move |name: &str, _: &borzoi_msbuild::observed::Observer| {
            if name.eq_ignore_ascii_case(DIRECTORY_BUILD_SDK) {
                Ok(SdkResolution::Single(SdkPaths {
                    root: sdk.clone(),
                    props: sdk.join("Sdk.props"),
                    targets: sdk.join("Sdk.targets"),
                }))
            } else {
                Err(SdkResolveError::NotFound)
            }
        };
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&self.project, &text)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &HashMap::new(),
            Some(&resolver),
            None,
        )
        .expect("generated documents are well-formed")
    }
}

/// The SDK the opacity tier's documents name.
const OPACITY_SDK: &str = "OpacitySdk";

/// A document under an SDK whose `Sdk.props` writes some properties and then
/// imports a file behind a gate the walker cannot decide — content the walk
/// cannot see, which may redefine what was written before it. The body reads
/// those properties, including into the `Directory.Build.targets` gate and
/// path, after the opacity.
///
/// This is the shape of #614, generated rather than witnessed: a value bound
/// before hidden content and read after it may be stale.
struct OpacityDoc {
    /// Written in `Sdk.props` before the undecided import.
    before: Vec<Write>,
    /// Where an earlier undecided import of an empty file sits among
    /// `before`, if anywhere: a second opacity, behaviourally inert (the file
    /// writes nothing, so every world imports it unconditionally) but one the
    /// walk latches. A value bound between the two latches is stale only if
    /// the *second* latch marks it too.
    earlier_opacity: Option<usize>,
    /// Written by the hidden file, when it is imported.
    hidden: Vec<Write>,
    body: Doc,
}

fn gen_opacity_doc(rng: &mut SplitMix64, names: &[&'static str]) -> OpacityDoc {
    const LITERALS: &[&str] = &[
        "", "true", "false", "true", "false", "net8.0", "Debug", "1.2.3",
    ];
    let literal_write = |rng: &mut SplitMix64, name: &'static str| Write {
        name,
        group_condition: None,
        condition: None,
        body: (*rng.pick(LITERALS)).to_string(),
    };
    let mut body = gen_doc(rng, names);
    let before: Vec<Write> = (0..1 + rng.below(4))
        .map(|_| {
            let name = *rng.pick(names);
            literal_write(rng, name)
        })
        .collect();
    let hidden = (0..1 + rng.below(3))
        .map(|_| {
            // Mostly a redefinition of something written before the import:
            // that is the stale value the shape needs.
            let name = if rng.below(4) == 0 {
                *rng.pick(names)
            } else {
                rng.pick(&before).name
            };
            literal_write(rng, name)
        })
        .collect::<Vec<Write>>();
    // Sometimes the hidden file writes an import input that nothing else
    // writes, which is #811's shape, with a value that turns the import off.
    let mut hidden = hidden;
    let unbound_import_input = (rng.below(8) == 0).then(|| {
        let name = *rng.pick(&IMPORT_POINT_INPUTS);
        let off = if name == IMPORT_POINT_INPUTS[0] {
            "false"
        } else {
            "Missing.targets"
        };
        hidden.push(Write {
            name,
            group_condition: None,
            condition: None,
            body: off.to_string(),
        });
        name
    });
    // Most cases copy a value the SDK wrote before the opacity into the
    // import's gate or path, as #614's witness does; the rest leave the
    // import to whatever the generated body reads.
    if rng.below(10) < 7 {
        let gate = if rng.below(5) == 0 {
            IMPORT_POINT_INPUTS[1]
        } else {
            IMPORT_POINT_INPUTS[0]
        };
        let source = rng.pick(&before).name;
        let at = rng.below(body.writes.len() + 1);
        body.writes.insert(
            at,
            Write {
                name: gate,
                group_condition: None,
                condition: None,
                body: format!("$({source})"),
            },
        );
    }
    let mut before = before;
    if let Some(name) = unbound_import_input {
        before.retain(|w| w.name != name);
        body.writes.retain(|w| w.name != name);
    }
    // Many cases add a Compile item whose `Include` or `Condition` reads a
    // value the hidden file rewrites, so the Compile reader's dependence on a
    // stale value is reached often rather than by accident; half of those
    // drop the body's other Compile items, whose own uncertainty would
    // otherwise decline the set whatever this item reads.
    if rng.below(10) < 4 {
        if rng.below(2) == 0 {
            body.items.retain(|item| item.kind != "Compile");
        }
        // The condition compares with a value the hidden file writes, so the
        // worlds usually take different branches.
        let rewrite = rng.pick(&hidden);
        let (source, literal) = (rewrite.name, rewrite.body.clone());
        let (condition, include) = if rng.below(2) == 0 {
            (None, format!("$({source}).fs"))
        } else {
            (
                Some(format!("'$({source})' == '{literal}'")),
                "Read.fs".to_string(),
            )
        };
        body.items.push(Item {
            kind: "Compile",
            group_condition: None,
            condition,
            include,
        });
    }
    let earlier_opacity = (rng.below(2) == 0).then(|| rng.below(before.len() + 1));
    OpacityDoc {
        before,
        earlier_opacity,
        hidden,
        body,
    }
}

fn render_writes(writes: &[Write]) -> String {
    let mut out = String::from("  <PropertyGroup>\n");
    for write in writes {
        out.push_str(&format!(
            "    <{name}>{body}</{name}>\n",
            name = write.name,
            body = xml_escape(&write.body)
        ));
    }
    out.push_str("  </PropertyGroup>\n");
    out
}

/// The three files of one opacity case under `variant` (`Taken`, `Omitted`,
/// or `Undecided`, whose wrap is ignored): `Sdk.props`, the hidden file, and
/// the project body.
fn render_opacity(doc: &OpacityDoc, variant: &Variant) -> (String, String, String) {
    let import = match variant {
        Variant::Omitted => String::new(),
        Variant::Undecided(_) => format!(
            "  <Import Project=\"Hidden.props\" Condition=\"{}\" />\n",
            xml_escape(UNDECIDABLE)
        ),
        _ => "  <Import Project=\"Hidden.props\" />\n".to_string(),
    };
    let (early, late) = doc
        .before
        .split_at(doc.earlier_opacity.unwrap_or(0).min(doc.before.len()));
    let earlier = match (doc.earlier_opacity, variant) {
        (None, _) => String::new(),
        (Some(_), Variant::Undecided(_)) => format!(
            "  <Import Project=\"Empty.props\" Condition=\"{}\" />\n",
            xml_escape(UNDECIDABLE)
        ),
        (Some(_), _) => "  <Import Project=\"Empty.props\" />\n".to_string(),
    };
    let sdk_props = format!(
        "<Project>\n{}{earlier}{}{import}</Project>\n",
        render_writes(early),
        render_writes(late)
    );
    let hidden = format!("<Project>\n{}</Project>\n", render_writes(&doc.hidden));
    let body = render(&doc.body, usize::MAX, &Variant::Taken).replacen(
        "<Project>",
        &format!("<Project Sdk=\"{OPACITY_SDK}\">"),
        1,
    );
    (sdk_props, hidden, body)
}

/// [`DirectoryBuildFixture`] with an SDK beside it whose files each case
/// writes.
struct OpacityFixture {
    inner: DirectoryBuildFixture,
    sdk: PathBuf,
}

impl OpacityFixture {
    fn new() -> Self {
        let inner = DirectoryBuildFixture::new();
        let sdk = inner
            .project
            .parent()
            .unwrap()
            .join("sdks")
            .join(OPACITY_SDK);
        std::fs::create_dir_all(&sdk).unwrap();
        std::fs::write(sdk.join("Sdk.targets"), "<Project />").unwrap();
        std::fs::write(sdk.join("Empty.props"), "<Project />").unwrap();
        Self { inner, sdk }
    }

    fn evaluate(&self, (sdk_props, hidden, body): &(String, String, String)) -> ParsedProject {
        std::fs::write(self.sdk.join("Sdk.props"), sdk_props).unwrap();
        std::fs::write(self.sdk.join("Hidden.props"), hidden).unwrap();
        let sdk = self.sdk.clone();
        let resolver = move |name: &str, _: &borzoi_msbuild::observed::Observer| {
            if name.eq_ignore_ascii_case(OPACITY_SDK) {
                Ok(SdkResolution::Single(SdkPaths {
                    root: sdk.clone(),
                    props: sdk.join("Sdk.props"),
                    targets: sdk.join("Sdk.targets"),
                }))
            } else {
                Err(SdkResolveError::NotFound)
            }
        };
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&self.inner.project, body)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &HashMap::new(),
            Some(&resolver),
            None,
        )
        .expect("generated documents are well-formed")
    }
}

fn sweep_opacity(seed: u64, cases: usize, names: &[&'static str]) -> Census {
    let fixture = OpacityFixture::new();
    let mut rng = SplitMix64(seed);
    let mut census = Census::default();
    for _ in 0..cases {
        let doc = gen_opacity_doc(&mut rng, names);
        let world_facts: Vec<(String, Facts)> = [Variant::Taken, Variant::Omitted]
            .into_iter()
            .map(|variant| {
                let files = render_opacity(&doc, &variant);
                (
                    format!("{variant:?}"),
                    facts(&fixture.evaluate(&files), names),
                )
            })
            .collect();
        let files = render_opacity(&doc, &Variant::Undecided(Wrap::ElementCondition));
        let project = fixture.evaluate(&files);
        let undecided = facts(&project, names);
        let text = format!(
            "--- Sdk.props ---\n{}--- Hidden.props ---\n{}--- body ---\n{}",
            files.0, files.1, files.2
        );
        check(
            &mut census,
            &text,
            &undecided,
            &world_facts,
            Undecided::Import,
            "opacity",
        );
    }
    census
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
            ("property", 65),
            ("Compile items", 70),
            ("DefineConstants", 60),
            ("target name", 100),
        ],
    );
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
            ("property", 110),
            ("Compile items", 75),
            ("DefineConstants", 25),
        ],
    );
}

/// The opacity tier: a property written in the SDK before content the walk
/// cannot see, read by the body after it.
#[test]
fn a_value_written_before_hidden_content_claims_no_more_than_its_worlds_agree_on() {
    let census = sweep_opacity(0x0bac_17e5, 800, &written_names(true));
    census.print("with an undecided SDK import");
    assert_sound(&census, &[("Compile items", 30)]);
}

/// The fresh-seed twin of the two sweeps above.
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

/// #782's shape, exhaustively. A value with two reasons to be unpinned — its
/// body read a name while undefined, and its gate read the undecided write —
/// keeps one of them as its root, so a reader that exempts by the root's name
/// drops the gate. The copy's body reads a name an exemption is keyed on
/// (`DefineConstants`' self-append, `TargetFramework`'s carve-out), or one no
/// exemption knows, or nothing; the readers copy it again or not, and read it
/// beside a direct `$(DefineConstants)` or alone.
///
/// The random sweeps reach this shape only by chance (it took a soak to find
/// #782): their wraps refuse the target's gate outright, and a refused gate
/// evaluates no body, so the target itself never holds two doubts. Here the
/// copy is gated on the target instead, which decides a gate untrusted.
#[test]
fn a_value_with_two_doubts_keeps_both_through_every_reader() {
    const GATES: &[&str] = &["'$(Foo)' == ''", "'$(Foo)' != ''", "'$(Foo)' == 'a'"];
    const COPY_BODIES: &[&str] = &[
        "$(DefineConstants.Length)",
        "a$(DefineConstants)",
        "$(DefineConstants)",
        "a$(TargetFramework)",
        "a$(Bar)",
        "a",
    ];
    // `{C}` is the copy a reader reads: `P0` itself, or `P1`, a copy of it.
    const DEFINE_READERS: &[&str] = &[
        "$({C})",
        "x$({C}.EndsWith('0'))",
        "$(DefineConstants);$({C})",
        "$({C});$(DefineConstants)",
        "$(DefineConstants.Length)$({C})",
    ];
    let names = [
        "Foo",
        "Bar",
        "P0",
        "P1",
        "DefineConstants",
        "TargetFramework",
    ];
    let write = |name, group_condition: Option<&str>, condition: Option<&str>, body: &str| Write {
        name,
        group_condition: group_condition.map(str::to_string),
        condition: condition.map(str::to_string),
        body: body.to_string(),
    };
    let mut census = Census::default();
    for gate in GATES {
        for gate_on_group in [false, true] {
            for copy_body in COPY_BODIES {
                for copies in [false, true] {
                    for reader in DEFINE_READERS {
                        let (group, element) = if gate_on_group {
                            (Some(*gate), None)
                        } else {
                            (None, Some(*gate))
                        };
                        let read = if copies { "P1" } else { "P0" };
                        let mut writes = vec![
                            write("Foo", None, None, "a"),
                            write("P0", group, element, copy_body),
                        ];
                        if copies {
                            writes.push(write("P1", None, None, "$(P0)"));
                        }
                        writes.push(write(
                            "DefineConstants",
                            None,
                            None,
                            &reader.replace("{C}", read),
                        ));
                        let doc = Doc {
                            writes,
                            items: vec![Item {
                                kind: "Compile",
                                group_condition: None,
                                condition: None,
                                include: format!("$({read}).fs"),
                            }],
                        };
                        check_every_wrap(&mut census, &doc, 0, &names, &pure_evaluate, "grid");
                    }
                }
            }
        }
    }
    census.print("two doubts");
    // About half what the grid produces, as for the random sweeps.
    assert_sound(
        &census,
        &[
            ("property", 400),
            ("Compile items", 240),
            ("DefineConstants", 190),
        ],
    );
}

// The defects the gate found, each pinned as the answer it should give, and
// ignored with its issue until fixed.

/// #780: a refused write is not published as never written.
#[test]
fn a_refused_write_is_not_published_as_never_written() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><TargetName>$(Configuration.Substring(0,1))</TargetName></PropertyGroup>
</Project>"#,
    );
    assert_eq!(
        project.property("TargetName"),
        PropertyRead::UnsetInexact(InexactUnset::Refused),
        "MSBuild computes `TargetName`; an absent, trusted name says the project never wrote it"
    );
    assert_eq!(project.target_name, ItemMetadataValue::Unknown);
}

/// #780: an item gate reads a refused name as never written, capturing a
/// phantom `ProjectReference`.
#[test]
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

/// #1098: a `ProjectReference` reading a name refused twice (a refused write,
/// then a refused write under a gate reading it) is not dropped from a list
/// published as certain.
#[test]
fn a_project_reference_reading_a_twice_refused_name_is_not_dropped() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup>
    <TargetFramework>$(Configuration)</TargetFramework>
  </PropertyGroup>
  <PropertyGroup>
    <TargetFramework>$(Platform.Nope('x'))</TargetFramework>
  </PropertyGroup>
  <PropertyGroup>
    <TargetFramework Condition="'$(TargetFramework)' == ''">$(Configuration.Substring(0,1))</TargetFramework>
  </PropertyGroup>
  <ItemGroup>
    <ProjectReference Include="$(TargetFramework.Length).fsproj" />
  </ItemGroup>
  <ItemGroup>
    <ProjectReference Include="$(Configuration.Length).fsproj" />
  </ItemGroup>
</Project>"#,
    );
    assert!(
        project.project_references_uncertain,
        "MSBuild references `$(TargetFramework.Length).fsproj`; we captured {:?} as certain",
        project.project_references
    );
    // The same read of a name the walk holds no value of, or holds one it
    // doubts, by each route: dropped or kept, the list is not certain.
    for (label, text) in [
        (
            "single",
            r#"<Project>
  <PropertyGroup><TF>$(Platform.Nope('x'))</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
        (
            "single-cond",
            r#"<Project>
  <PropertyGroup><TF Condition="'É' == 'é'">$(Platform.Nope('x'))</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
        (
            "twice-uncond",
            r#"<Project>
  <PropertyGroup><TF>$(Platform.Nope('x'))</TF></PropertyGroup>
  <PropertyGroup><TF>$(Configuration.Substring(0,1))</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
        (
            "twice-cond-a",
            r#"<Project>
  <PropertyGroup><TF>$(Platform.Nope('x'))</TF></PropertyGroup>
  <PropertyGroup><TF Condition="'$(TF)' == ''">a</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
        (
            "twice-cond-refused",
            r#"<Project>
  <PropertyGroup><TF>$(Platform.Nope('x'))</TF></PropertyGroup>
  <PropertyGroup><TF Condition="'$(TF)' == ''">$(Configuration.Substring(0,1))</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
        (
            "undecided-a",
            r#"<Project>
  <PropertyGroup><TF Condition="'É' == 'é'">a</TF></PropertyGroup>
  <ItemGroup><ProjectReference Include="$(TF.Length).fsproj" /></ItemGroup>
</Project>"#,
        ),
    ] {
        let project = pure_evaluate(text);
        assert!(
            project.project_references_uncertain,
            "{label}: MSBuild references `$(TF.Length).fsproj`; we captured {:?} as certain",
            project.project_references
        );
    }
}

/// The other side of #780's gate fix: a refused name that a later clean write
/// binds holds a value computed exactly, so a gate reading it decides exactly.
#[test]
fn a_project_reference_gated_on_a_rewritten_refused_name_is_certain() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><Bar>$(Configuration.Substring(0,1))</Bar></PropertyGroup>
  <PropertyGroup><Bar>x</Bar></PropertyGroup>
  <ItemGroup Condition="'$(Bar)' == 'x'"><ProjectReference Include="x.fsproj" /></ItemGroup>
</Project>"#,
    );
    assert!(!project.project_references_uncertain);
    assert_eq!(project.project_references.len(), 1);
    assert_eq!(
        project.property("Bar"),
        PropertyRead::Value("x".to_string())
    );
}

/// #781: a `Directory.Build.targets` imported under an undecided gate
/// publishes none of its writes as trusted.
#[test]
fn a_file_imported_under_an_undecided_gate_publishes_no_trusted_value() {
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
        project.property("FromDirBuild").untrusted_cause().is_some(),
        "MSBuild writes the gate `false` and never imports the file"
    );
}

/// #811: a gate content the walk could not see may have written is not read
/// as never written.
#[test]
fn an_unbound_import_input_hidden_content_defined_declines() {
    let fixture = OpacityFixture::new();
    let project = fixture.evaluate(&(
        format!(
            "<Project>\n  <Import Project=\"Hidden.props\" Condition=\"{}\" />\n</Project>\n",
            xml_escape(UNDECIDABLE)
        ),
        "<Project><PropertyGroup><ImportDirectoryBuildTargets>false</ImportDirectoryBuildTargets></PropertyGroup></Project>".to_string(),
        format!("<Project Sdk=\"{OPACITY_SDK}\" />"),
    ));
    assert!(
        project.items_uncertain,
        "MSBuild imports `Hidden.props`, whose gate keeps `{DIR_BUILD_ITEM}` out; we published {:?}",
        project.items
    );
}

/// A Compile item reading a value hidden content may have rewritten leaves the
/// Compile set uncertain, by its `Include` and by its `Condition` alike.
#[test]
fn a_compile_item_reading_a_stale_value_declines() {
    let fixture = OpacityFixture::new();
    let sdk_props = format!(
        "<Project>\n  <PropertyGroup><Name>Before</Name></PropertyGroup>\n  \
         <Import Project=\"Hidden.props\" Condition=\"{}\" />\n</Project>\n",
        xml_escape(UNDECIDABLE)
    );
    let hidden = "<Project><PropertyGroup><Name>After</Name></PropertyGroup></Project>".to_string();
    for item in [
        r#"<Compile Include="$(Name).fs" />"#,
        r#"<Compile Include="Read.fs" Condition="'$(Name)' == 'After'" />"#,
    ] {
        let body = format!(
            "<Project Sdk=\"{OPACITY_SDK}\">\n  \
             <PropertyGroup><ImportDirectoryBuildTargets>false</ImportDirectoryBuildTargets></PropertyGroup>\n  \
             <ItemGroup>{item}</ItemGroup>\n</Project>"
        );
        let project = fixture.evaluate(&(sdk_props.clone(), hidden.clone(), body));
        assert!(
            project.items_uncertain,
            "`{item}` reads `Name`, which the hidden file may set to `After`; we published {:?}",
            project.items
        );
    }
}

/// #782: a single-witness root lets the `DefineConstants` self-append
/// exemption drop an independent cause.
#[test]
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

/// #782 through the self-append's own read: a `<DefineConstants>` value that
/// reads `$(DefineConstants)` directly and also reads a copy of it does not
/// let the direct read stand for the copy's root, which hides the same gate.
#[test]
fn the_self_append_read_does_not_stand_for_a_copied_root() {
    let project = pure_evaluate(
        r#"<Project>
  <PropertyGroup><TargetName>$(Configuration.Substring(0,1))</TargetName></PropertyGroup>
  <PropertyGroup>
    <P1 Condition="'$(TargetName)' == ''">$(DefineConstants.Length)</P1>
  </PropertyGroup>
  <PropertyGroup><DefineConstants>$(DefineConstants);x$(P1.EndsWith('0'))</DefineConstants></PropertyGroup>
</Project>"#,
    );
    assert!(
        project.define_constants_uncertain,
        "MSBuild skips `P1`'s write, so `DefineConstants` is `;xFalse`; we published {:?}",
        project.define_constants
    );
}
