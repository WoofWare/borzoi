//! Differential: what MSBuild's registration of a `<UsingTask>` refuses
//! without an expression throwing (#1099), against design-time evaluation
//! through `tools/msbuild-condition-oracle`.
//!
//! MSBuild registers every `<UsingTask>` whose condition holds, after every
//! property write, and refuses one (rejecting the whole project) whose
//! `TaskName` expands to empty, whose children stand under a `TaskFactory`
//! that expands to empty, `AssemblyTaskFactory` or `TaskHostFactory`, whose
//! `AssemblyFile` (else `AssemblyName`) expands to empty, whose body's
//! `Evaluate` or a parameter's `Output` or `Required` `Boolean.TryParse` does
//! not read, or a parameter's `ParameterType` names no type it takes. The
//! walk's registration judgement (`evaluator/rejection.rs`'s
//! `judge_registration`) is held to it certain-implies-exact:
//!
//! - MSBuild rejects the project: the walk claims it may;
//! - MSBuild evaluates it: the walk claims no certain rejection, and commits
//!   the value written after the `<UsingTask>`.
//!
//! [`hand_picked_registrations`] pins each rule's corners, MSBuild's verdict
//! and the walk's claim alike; [`registration_sweep_fixed_seed`] generates
//! values for every place over the hostile value alphabet and a spelling
//! table, each written as a literal, through a property the walk is certain
//! of, through one it doubts, and through a write it refuses.

mod common;

use std::collections::{BTreeSet, HashMap};

use borzoi_msbuild::RejectionCertainty;
use borzoi_oracle_harness::hostile::{self, Dimension, coverage, value};
use common::{Oracle, SplitMix64};

/// An inline task's `<UsingTask>` attributes, but for its children.
const INLINE: &str = "TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" \
                      AssemblyFile=\"$(MSBuildToolsPath)\\Microsoft.Build.Tasks.Core.dll\"";

/// A gate MSBuild evaluates to true and the walk cannot decide.
const UNDECIDED_TRUE: &str = "'É' == 'é'";

/// What one graded document came to.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Graded {
    msbuild_rejects: bool,
    walk: Option<RejectionCertainty>,
    /// Whether the walk holds no value of `V` (a write it refused to compute).
    v_unheld: bool,
}

/// Grade `body` (the `<UsingTask>` and what it needs), after `writes` (a
/// property group's content), against design-time evaluation: certain-
/// implies-exact. A rejection resting on a value the walk holds none of (`V`
/// written by a write it refused) is the judgement over the values a name may
/// hold, which the walk does not make yet (#1051): not graded here, and shown
/// by the caller to rest there.
fn grade(oracle: &mut Oracle, writes: &str, body: &str) -> Graded {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let xml = format!(
        "<Project><PropertyGroup><Empty></Empty>{writes}</PropertyGroup>{body}\
         <PropertyGroup><After>ok</After></PropertyGroup></Project>"
    );
    std::fs::write(&project_path, &xml).unwrap();
    let msbuild_rejects = oracle
        .project_design_time(&xml, &["After".to_string()], Some(&project_path), &[])
        .is_none();
    let parsed = common::parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed");
    let walk = parsed.rejection.as_ref().map(|r| r.certainty);
    let v_unheld = writes.contains("<V>") && !parsed.properties.contains_key("V");
    if msbuild_rejects {
        assert!(
            walk.is_some() || v_unheld,
            "MSBuild rejects, and the walk claims nothing: {xml}"
        );
    } else {
        assert_ne!(
            walk,
            Some(RejectionCertainty::Certain),
            "MSBuild evaluates, and the walk claims it rejects: {xml}\n{:#?}",
            parsed.rejection
        );
        // A possible rejection withdraws every value, which claims nothing;
        // with none, the value after the task is MSBuild's.
        if walk.is_none() {
            assert_eq!(
                parsed.property("After").value(),
                Some("ok"),
                "MSBuild evaluates, and the walk withdrew: {xml}"
            );
        }
    }
    Graded {
        msbuild_rejects,
        walk,
        v_unheld,
    }
}

/// Where a value goes: `{v}` stands for it.
const PLACES: &[&str] = &[
    "<UsingTask {INLINE}><Task Evaluate=\"{v}\">x</Task></UsingTask>",
    "<UsingTask {INLINE}><ParameterGroup><A Required=\"{v}\" /></ParameterGroup><Task>x</Task></UsingTask>",
    "<UsingTask {INLINE}><ParameterGroup><A Output=\"{v}\" /></ParameterGroup><Task>x</Task></UsingTask>",
    "<UsingTask {INLINE}><ParameterGroup><A ParameterType=\"{v}\" /></ParameterGroup><Task>x</Task></UsingTask>",
    "<UsingTask {INLINE}><ParameterGroup><A ParameterType=\"{v}\" Output=\"true\" /></ParameterGroup><Task>x</Task></UsingTask>",
    "<UsingTask TaskName=\"{v}\" AssemblyFile=\"y.dll\" />",
    "<UsingTask TaskName=\"X\" TaskFactory=\"{v}\" AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>",
    "<UsingTask TaskName=\"X\" AssemblyFile=\"{v}\" />",
    "<UsingTask TaskName=\"X\" AssemblyName=\"{v}\" />",
];

/// The plain values a place reads, beside the hostile ones.
const PLAIN: &[&str] = &[
    "true",
    "false",
    "FALSE",
    " true ",
    "",
    "off",
    "1",
    "maybe",
    "System.String",
    "System.Int32[]",
    "Microsoft.Build.Framework.ITaskItem[]",
    "System.Object",
    "string",
    "Nope.Type",
    "RoslynCodeTaskFactory",
    "TaskHostFactory",
    "assemblytaskfactory",
    "y.dll",
];

/// How a value reaches its place.
#[derive(Clone, Copy, Debug)]
enum Source {
    /// Written in the place itself.
    Literal,
    /// Through a property the walk is certain of.
    Certain,
    /// Through a property written under a gate the walk cannot decide (the
    /// same value either way, so MSBuild's is the one it holds).
    Doubted,
    /// Through a write the walk refuses to compute (MSBuild holds the value).
    Refused,
}

const SOURCES: &[Source] = &[
    Source::Literal,
    Source::Certain,
    Source::Doubted,
    Source::Refused,
];

/// A document putting `value` in `place` through `source`: its writes and
/// its body.
fn document(place: &str, value: &str, source: Source) -> (String, String) {
    let text = value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;");
    let attribute = text.replace('"', "&quot;");
    let (writes, spliced) = match source {
        Source::Literal => (String::new(), attribute),
        Source::Certain => (format!("<V>{text}</V>"), "$(V)".to_owned()),
        Source::Doubted => (
            format!("<V>{text}</V><V Condition=\"{UNDECIDED_TRUE}\">{text}</V>"),
            "$(V)".to_owned(),
        ),
        Source::Refused => (
            format!(
                "<V>$([System.String]::Copy('{}'))</V>",
                text.replace('\'', "&apos;")
            ),
            "$(V)".to_owned(),
        ),
    };
    let body = place.replace("{INLINE}", INLINE).replace("{v}", &spliced);
    (writes, body)
}

/// Each rule's corners, with MSBuild's verdict (rejects) and the walk's claim
/// pinned, so that a verdict moving shows.
#[test]
fn hand_picked_registrations() {
    use RejectionCertainty::{Certain, Possible};
    let inline_task = |attributes: &str, inner: &str| {
        format!("<UsingTask {INLINE}{attributes}>{inner}</UsingTask>")
    };
    let rows: Vec<(String, bool, Option<RejectionCertainty>)> = vec![
        // An `Evaluate` that is no boolean, whatever the body holds.
        (inline_task("", "<Task Evaluate=\"off\">x</Task>"), true, Some(Certain)),
        (inline_task("", "<Task Evaluate=\"no\">x</Task>"), true, Some(Certain)),
        (inline_task("", "<Task Evaluate=\"!false\">x</Task>"), true, Some(Certain)),
        (inline_task("", "<Task Evaluate=\"false;\">x</Task>"), true, Some(Certain)),
        (inline_task("", "<Task Evaluate=\"$(Missing)\">x</Task>"), true, Some(Certain)),
        (inline_task("", "<Task Evaluate=\"$(Empty)\">x</Task>"), true, Some(Certain)),
        // Written empty, it reads as absent; padded and cased, a boolean.
        (inline_task("", "<Task Evaluate=\"\">x</Task>"), false, None),
        (inline_task("", "<Task Evaluate=\" FALSE \">x</Task>"), false, None),
        (inline_task("", "<Task Evaluate=\"True\">x</Task>"), false, None),
        // Under a false condition, nothing is registered.
        (
            inline_task(" Condition=\"false\"", "<Task Evaluate=\"off\">x</Task>"),
            false,
            None,
        ),
        // Parameters.
        (
            inline_task("", "<ParameterGroup><A Required=\"maybe\" /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Certain),
        ),
        (
            inline_task("", "<ParameterGroup><A Output=\"yes\" /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Certain),
        ),
        (
            inline_task("", "<ParameterGroup><A Required=\"\" Output=\"\" /></ParameterGroup><Task>x</Task>"),
            false,
            None,
        ),
        (
            inline_task("", "<ParameterGroup><A ParameterType=\"Nope.Type\" /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Possible),
        ),
        (
            inline_task("", "<ParameterGroup><A ParameterType=\"$(Empty)\" /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Certain),
        ),
        (
            inline_task("", "<ParameterGroup><A ParameterType=\"System.String\" Required=\"true\" Output=\"false\" /></ParameterGroup><Task>x</Task>"),
            false,
            None,
        ),
        // A body under no task factory.
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"$(Empty)\" AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>".to_owned(),
            true,
            Some(Certain),
        ),
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"taskhostfactory\" AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>".to_owned(),
            true,
            Some(Certain),
        ),
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"TaskHostFactory\" AssemblyFile=\"y.dll\" />".to_owned(),
            false,
            None,
        ),
        // Names that expand to empty.
        (
            "<UsingTask TaskName=\"$(Empty)\" AssemblyFile=\"y.dll\" />".to_owned(),
            true,
            Some(Certain),
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"$(Empty)\" />".to_owned(),
            true,
            Some(Certain),
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyName=\"$(Empty)\" />".to_owned(),
            true,
            Some(Certain),
        ),
        // A function that reads the file system, which finds nothing.
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"$([MSBuild]::GetPathOfFileAbove('Missing.dll', '$(MSBuildProjectDirectory)'))\" />".to_owned(),
            true,
            Some(Certain),
        ),
        // `AssemblyFile`'s own `\` turned into `/` before it expands.
        (
            "<PropertyGroup><Slash>/foo</Slash></PropertyGroup>\
             <UsingTask TaskName=\"X\" AssemblyFile=\"$(Slash.Split('\\')[0])\" />"
                .to_owned(),
            true,
            Some(Certain),
        ),
        // A metadatum MSBuild leaves as written: a file name.
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"%(M)\" />".to_owned(),
            false,
            None,
        ),
        // Parameters MSBuild keys case-insensitively
        // ([`parameters_colliding_by_case_fail_the_registry`]).
        (
            inline_task("", "<ParameterGroup><A /><B /></ParameterGroup><Task>x</Task>"),
            false,
            None,
        ),
        (
            inline_task(
                " Condition=\"false\"",
                "<ParameterGroup><A /><a /></ParameterGroup><Task>x</Task>",
            ),
            false,
            None,
        ),
        // A factory name a fold outside ASCII may match: a decline.
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"É\" AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>".to_owned(),
            false,
            Some(Possible),
        ),
    ];
    let mut oracle = Oracle::spawn();
    for (body, rejects, claim) in rows {
        let graded = grade(&mut oracle, "", &body);
        assert_eq!(
            graded,
            Graded {
                msbuild_rejects: rejects,
                walk: claim,
                v_unheld: false,
            },
            "{body}"
        );
    }
}

/// Two parameters whose names fold to one: MSBuild's registry, keyed
/// case-insensitively, fails on the second (an internal error, MSB1025,
/// which the oracle reports as the exception), so the project does not
/// evaluate, and the walk claims it is rejected.
#[test]
fn parameters_colliding_by_case_fail_the_registry() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let xml = format!(
        "<Project><UsingTask {INLINE}><ParameterGroup><A /><a /></ParameterGroup><Task>x</Task>\
         </UsingTask><PropertyGroup><After>ok</After></PropertyGroup></Project>"
    );
    std::fs::write(&project_path, &xml).unwrap();
    let verdict = Oracle::spawn().design_time_verdict(&xml, &project_path);
    assert!(
        verdict
            .as_ref()
            .is_err_and(|error| error.contains("same key")),
        "{verdict:?}"
    );
    let parsed = common::parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed");
    assert_eq!(
        parsed.rejection.as_ref().map(|r| r.certainty),
        Some(RejectionCertainty::Certain),
        "{xml}"
    );
}

/// The values the sweep cannot carry.
const EXCLUDED: &[(Dimension, &str)] = &[
    (
        Dimension::OverwrittenLater,
        "the registration reads a value after every property write: a value a later write puts \
         back never reaches it",
    ),
    (
        Dimension::SelfSetProperty,
        "each value reads a property the build sets for itself, which the walk holds no value \
         of: whether MSBuild refuses the value it holds is the judgement over the values a name \
         may hold, which the walk does not make yet (#1051)",
    ),
    (
        Dimension::ReadsTheBuild,
        "each value calls a property function in a property body, one the walk does not model \
         there, which MSBuild may throw on and the walk does not judge yet (#1094)",
    ),
];

/// What the sweep saw.
#[derive(Debug, Default)]
struct Census {
    cases: usize,
    msbuild_rejects: usize,
    certain: usize,
    possible: usize,
    /// Rejections resting on a value the walk holds none of (#1051).
    unheld_value: usize,
}

/// `cases` documents from `rng`, each graded ([`grade`]).
fn registration_sweep(seed: u64, cases: usize) -> Census {
    let census = coverage::open(file!(), "using_task_registration", EXCLUDED);
    let excluded: BTreeSet<Dimension> = EXCLUDED.iter().map(|(d, _)| *d).collect();
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut tally = Census::default();
    while tally.cases < cases {
        let place = *rng.pick(PLACES);
        let source = *rng.pick(SOURCES);
        let plain = *rng.pick(PLAIN);
        let drawn = match value::alphabet().sample(rng.next()) {
            Some(entry) => hostile::Drawn::of(entry).map(|v| v.render(plain)),
            None => hostile::Drawn::plain(plain.to_owned()),
        };
        if drawn.hostile.iter().any(|d| excluded.contains(d))
            || drawn.value.chars().any(|c| !hostile::xml::representable(c))
        {
            continue;
        }
        // A literal `TaskName`, `AssemblyFile` or `AssemblyName` written
        // empty is the loader's to refuse, at load time.
        let (writes, body) = document(place, &drawn.value, source);
        tally.cases += 1;
        let graded = grade(&mut oracle, &writes, &body);
        tally.msbuild_rejects += usize::from(graded.msbuild_rejects);
        if graded.msbuild_rejects && graded.walk.is_none() {
            // `grade` let this pass only on a value the walk holds none of.
            // Shown to rest on that value: through a property the walk holds
            // it in, where it does, MSBuild rejects and the walk claims.
            let (writes, body) = document(place, &drawn.value, Source::Certain);
            let certain = grade(&mut oracle, &writes, &body);
            assert!(
                certain.v_unheld || (certain.msbuild_rejects && certain.walk.is_some()),
                "MSBuild rejects a value the walk refused to compute, and not the value through a \
                 certain property: {body}"
            );
            tally.unheld_value += 1;
            census.reached(&drawn.hostile, "rejects-on-an-unheld-value");
            continue;
        }
        match graded.walk {
            Some(RejectionCertainty::Certain) => tally.certain += 1,
            Some(RejectionCertainty::Possible) => tally.possible += 1,
            None => {}
        }
        census.reached(
            &drawn.hostile,
            match (graded.msbuild_rejects, graded.walk) {
                (true, Some(RejectionCertainty::Certain)) => "rejects-claimed",
                (true, _) => "rejects-perhaps",
                (false, Some(_)) => "evaluates-withdrawn",
                (false, None) => "evaluates-committed",
            },
        );
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         using_task_registration_diff registration_sweep_fixed_seed",
    );
    tally
}

/// [`registration_sweep`] at a fixed seed.
#[test]
fn registration_sweep_fixed_seed() {
    let tally = registration_sweep(0x1099_7a5c, 600);
    eprintln!("registration sweep: {tally:?}");
    assert!(tally.msbuild_rejects >= 100, "{tally:?}");
    assert!(tally.certain >= 50, "{tally:?}");
    assert!(tally.cases - tally.msbuild_rejects >= 100, "{tally:?}");
}

/// The fresh-seed twin of [`registration_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run with --ignored"]
fn registration_sweep_soak() {
    let (seed, cases) = common::soak_parameters("using-task registration", 3000);
    registration_sweep(seed, cases);
}
