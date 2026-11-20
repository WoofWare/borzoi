//! Generated projects whose conditions and property bodies MSBuild may throw
//! on (#1009), graded against MSBuild through `tools/msbuild-condition-oracle`.
//!
//! MSBuild evaluates a condition left to right, stopping at the operand that
//! decides it, and throws on an operand it reaches that is ill typed, that
//! calls a property function failing on its input (an indexer out of range, a
//! malformed version), or, in an item's condition, that forms an item
//! expression it cannot expand. It throws on the same property functions in a
//! property body, an item's `Include` and metadata. A throw rejects the whole
//! project. The walk classifies each operand it cannot evaluate three ways
//! (MSBuild throws; MSBuild may throw, because the walk does not model it;
//! MSBuild returns a boolean the walk cannot compute) and judges a rejection
//! from that.
//!
//! The generator puts a generated condition or text in each position MSBuild
//! evaluates one (and some it does not), over certain properties holding
//! hostile values (`borzoi_oracle_harness::hostile`) and an uncertain one the
//! walk holds one value of while MSBuild holds another, with operands that
//! throw in every position of `And`/`Or` chains. Each project is graded
//! certain-implies-exact against design-time evaluation, the evaluation the
//! walk's rejection model follows (`evaluator/rejection.rs`):
//!
//! - MSBuild rejects it: the walk commits no value;
//! - MSBuild evaluates it: the walk claims no certain rejection, and every
//!   value it commits is MSBuild's.
//!
//! [`classified_judgement_sweep`] holds the condition judgement itself
//! (`test_support::judge`) to MSBuild under every assignment of the uncertain
//! names, on the same operands: a claim that MSBuild cannot throw must hold
//! wherever the judgement makes it, unevaluated operands included.

mod common;

use std::collections::{BTreeSet, HashMap};

use borzoi_msbuild::test_support::{
    Issue, PropertyMap, Throws, judge, property_references, substitute,
};
use borzoi_msbuild::{PropertyRead, RejectionCertainty};
use borzoi_oracle_harness::hostile::{self, Dimension, coverage, value};
use common::{Oracle, SplitMix64, parse_fsproj_with_imports, soak_parameters};
use tempfile::TempDir;

/// A gate the walk cannot decide and that MSBuild evaluates, without
/// throwing, to true: an equality whose case folding the walk does not model.
const UNDECIDED_TRUE: &str = "'É' == 'é'";
/// [`UNDECIDED_TRUE`]'s false twin.
const UNDECIDED_FALSE: &str = "'É' == 'Ê'";

/// The plain values a certain property is drawn from, and the plain value a
/// hostile one is rendered around.
const PLAIN: &[&str] = &["", "1", "2.0", "abc", "true", "a;b", "1.2.3", "x;y;z"];

/// The values the uncertain property is graded under at the condition level.
const GRADED: &[Option<&str>] = &[
    None,
    Some(""),
    Some("1"),
    Some("abc"),
    Some("true"),
    Some("a;b;c;d"),
];

/// A property value: plain, or hostile with the dimensions it carries.
fn draw_value(rng: &mut SplitMix64) -> hostile::Drawn<String> {
    let plain = *rng.pick(PLAIN);
    match value::alphabet().sample(rng.next()) {
        Some(entry) => hostile::Drawn::of(entry).map(|v| v.render(plain)),
        None => hostile::Drawn::plain(plain.to_owned()),
    }
}

/// An operand naming one of `names`: a literal, a reference, or a property
/// function, modelled or not, that may throw on its receiver.
fn operand(rng: &mut SplitMix64, names: &[&str]) -> String {
    let name = *rng.pick(names);
    let other = *rng.pick(names);
    match rng.below(14) {
        0 => format!("'{}'", rng.pick(&["", "1", "2.0", "abc", "true", "x", "É"])),
        1 => format!("'$({name})'"),
        2 => format!("$({name})"),
        3 => format!("'x$({name})'"),
        // Adjacent references, which may form an item expression.
        4 => format!("'$({name})$({other})'"),
        // Indexers, which throw out of range.
        5 => format!("'$({name}.Split(\";\")[{}])'", rng.pick(&["0", "1", "3"])),
        6 => format!("'$({name}[{}])'", rng.pick(&["0", "2", "5"])),
        7 => format!("'$({name}.Length)'"),
        // A malformed version operand throws.
        8 => format!("'$([MSBuild]::VersionGreaterThan(\"$({name})\", \"1.0\"))'"),
        // Functions the walk does not model: one that throws on short input,
        // one that never throws.
        9 => format!("'$({name}.Substring(2))'"),
        10 => format!("'$([System.String]::IsNullOrWhiteSpace(\"$({name})\"))'"),
        11 => format!("'$({name}.Trim())'"),
        12 => "'$(Missing)'".to_owned(),
        _ => format!("'$({name}.Split(\";\")[1].Length)'"),
    }
}

/// A condition over `names`: comparisons of every form that can throw,
/// coerced scalars, built-ins, nested under `!`, `And` and `Or`.
fn condition(rng: &mut SplitMix64, names: &[&str], depth: u32) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(9) {
            0 => rng.pick(&["true", "false"]).to_string(),
            1 => operand(rng, names),
            2 => format!("HasTrailingSlash({})", operand(rng, names)),
            3 => format!(
                "$([MSBuild]::VersionLessThan('$({})', '2.0'))",
                rng.pick(names)
            ),
            4 => format!("Exists({})", operand(rng, names)),
            _ => format!(
                "{} {} {}",
                operand(rng, names),
                rng.pick(&["==", "!=", "<", "<=", ">", ">="]),
                operand(rng, names)
            ),
        };
    }
    match rng.below(3) {
        0 => format!("!({})", condition(rng, names, depth - 1)),
        n => {
            let connective = if n == 1 { " And " } else { " Or " };
            let operands: Vec<String> = (0..2 + rng.below(2))
                .map(|_| condition(rng, names, depth - 1))
                .collect();
            format!("({})", operands.join(connective))
        }
    }
}

/// A property body over `names`: text around operands' expressions. A
/// function the walk does not model and MSBuild may throw on (`Substring`) is
/// left out: in a body it is #1094's gap, which the walk does not judge yet.
fn text(rng: &mut SplitMix64, names: &[&str]) -> String {
    let piece = |rng: &mut SplitMix64| loop {
        let op = operand(rng, names);
        if op.contains("Substring") {
            continue;
        }
        // The operand's quotes are a condition's; a body takes the text.
        break op.trim_matches('\'').to_owned();
    };
    match rng.below(3) {
        0 => piece(rng),
        1 => format!("a{}b", piece(rng)),
        _ => format!("{};{}", piece(rng), piece(rng)),
    }
}

/// `xml` with each line cut to a readable length: a long hostile value
/// otherwise buries the site a failure is about.
fn elide(xml: &str) -> String {
    xml.lines()
        .map(|line| match line.char_indices().nth(400) {
            Some((at, _)) => format!("{}… ({} bytes)", &line[..at], line.len()),
            None => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn xml_text(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

fn xml_attribute(s: &str) -> String {
    xml_text(s).replace('"', "&quot;")
}

/// Where a generated piece goes: `{c}` a condition, `{t}` a text.
const SITES: &[&str] = &[
    "<PropertyGroup><R Condition=\"{c}\">x</R></PropertyGroup>",
    "<PropertyGroup Condition=\"{c}\"><R>x</R></PropertyGroup>",
    "<PropertyGroup><R>{t}</R></PropertyGroup>",
    "<PropertyGroup><R Condition=\"UNDECIDED_TRUE\">{t}</R></PropertyGroup>",
    "<PropertyGroup><R Condition=\"UNDECIDED_FALSE\">{t}</R></PropertyGroup>",
    "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><R>{t}</R></PropertyGroup>",
    "<PropertyGroup Condition=\"false\"><R>{t}</R></PropertyGroup>",
    "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><R Condition=\"{c}\">x</R></PropertyGroup>",
    "<ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup>",
    "<ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup>",
    "<ItemGroup><I Include=\"{t}\" /></ItemGroup>",
    "<ItemGroup Condition=\"false\"><I Include=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\"><M>{t}</M></I></ItemGroup>",
    "<ItemGroup><I Include=\"x\"><M Condition=\"{c}\">m</M></I></ItemGroup>",
    "<ItemGroup><I Include=\"x\" Exclude=\"{t}\" /></ItemGroup>",
    "<ItemDefinitionGroup><I><M>{t}</M></I></ItemDefinitionGroup>",
    "<Import Project=\"there.props\" Condition=\"{c}\" />",
    "<Choose><When Condition=\"{c}\"><PropertyGroup><R>x</R></PropertyGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_FALSE\" /><When Condition=\"{c}\" /></Choose>",
];

/// What became of a generated project, as the census counts it.
fn outcome(rejected: bool, committed: bool) -> &'static str {
    match (rejected, committed) {
        (true, _) => "msbuild-rejects",
        (false, true) => "commit",
        (false, false) => "withdraw",
    }
}

#[derive(Debug, Default)]
struct ProjectCensus {
    cases: usize,
    msbuild_rejects: usize,
    certain: usize,
    possible: usize,
    committed: usize,
    /// Projects MSBuild evaluates whose every value the walk commits.
    evaluated_and_committed: usize,
    /// Projects MSBuild rejects over a value it holds and the walk does not
    /// (of `U`, or of a write the walk refused to compute), which the walk
    /// commits: the judgement over the values a name may hold, #1009's second
    /// stage (#1051), not made yet.
    rejected_on_an_uncertain_value: usize,
    /// Projects MSBuild rejects over a text holding an expression the walk
    /// does not model, which the walk commits: a refused body is no rejection
    /// site yet (#1094).
    rejected_on_an_unmodelled_body: usize,
}

/// The hostile values the project sweep cannot carry yet.
const PROJECT_EXCLUDED: &[(Dimension, &str)] = &[(
    Dimension::ReadsTheBuild,
    "each value calls a property function in a property body, and one the walk does not model \
     there, which MSBuild may throw on, is no rejection site yet (#1094)",
)];

/// Generate `cases` projects from `rng` and grade each against MSBuild.
fn project_sweep(rng: &mut SplitMix64, cases: usize) -> ProjectCensus {
    let census = coverage::open(
        "crates/msbuild/tests/rejection_generative_diff.rs",
        "rejection_projects",
        PROJECT_EXCLUDED,
    );
    let excluded: BTreeSet<Dimension> = PROJECT_EXCLUDED.iter().map(|(d, _)| *d).collect();
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(
        dir.join("there.props"),
        "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    let names: Vec<String> = ["A", "B", "U", "R", "After", "Delta"]
        .map(String::from)
        .to_vec();
    let mut tally = ProjectCensus::default();
    while tally.cases < cases {
        let a = draw_value(rng);
        let b = draw_value(rng);
        let held = draw_value(rng);
        let real = draw_value(rng);
        let mut hostile: BTreeSet<Dimension> = BTreeSet::new();
        for drawn in [&a, &b, &held, &real] {
            hostile.extend(drawn.hostile.iter().copied());
        }
        if hostile.iter().any(|d| excluded.contains(d)) {
            continue;
        }
        let operands = ["A", "B", "U"];
        let template = *rng.pick(SITES);
        let body = text(rng, &operands);
        let gate = condition(rng, &operands, 3);
        let site = template
            .replace("{c}", &xml_attribute(&gate))
            .replace("{t}", &xml_attribute(&body))
            .replace("UNDECIDED_TRUE", &xml_attribute(UNDECIDED_TRUE))
            .replace("UNDECIDED_FALSE", &xml_attribute(UNDECIDED_FALSE));
        // A value overwritten later has been read by the site in between.
        let mut later = String::new();
        for (name, drawn) in [("A", &a), ("B", &b)] {
            if drawn.hostile.contains(&Dimension::OverwrittenLater) {
                later.push_str(&format!("<{name}>1</{name}>"));
            }
        }
        // `U` as MSBuild holds it, which the walk cannot know.
        let real_write = format!(
            "<U Condition=\"{}\">{}</U>",
            xml_attribute(UNDECIDED_TRUE),
            xml_text(&real.value)
        );
        let xml = format!(
            "<Project>\n  <PropertyGroup><A>{}</A><B>{}</B><U>{}</U>{real_write}\
             </PropertyGroup>\n  {site}\n  \
             <PropertyGroup><After>ok</After>{later}</PropertyGroup>\n</Project>\n",
            xml_text(&a.value),
            xml_text(&b.value),
            xml_text(&held.value),
        );
        std::fs::write(&project_path, &xml).unwrap();
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let ours: Vec<(&String, String)> = names
            .iter()
            .filter_map(|name| match parsed.property(name) {
                PropertyRead::Unset => Some((name, String::new())),
                read => read.value().map(|v| (name, v.to_owned())),
            })
            .collect();
        let describe = || format!("--- xml ---\n{}\n{:#?}", elide(&xml), parsed.rejection);
        tally.cases += 1;
        match parsed.rejection.as_ref().map(|r| r.certainty) {
            Some(RejectionCertainty::Certain) => tally.certain += 1,
            Some(RejectionCertainty::Possible) => tally.possible += 1,
            None => {}
        }
        let both = oracle.project_both(&xml, &names, Some(&project_path), &[]);
        let Some(theirs) = both.design_time else {
            tally.msbuild_rejects += 1;
            if !ours.is_empty() {
                // Where MSBuild evaluates the project with every name as the
                // walk holds it (`U` without the write the walk could not
                // decide, a reference the walk does not see through as it
                // reads it, a write it refused to compute empty, as the walk
                // substitutes it), it rejects over a value the walk does not
                // hold.
                let walk_held =
                    |name: &str| spelt(parsed.properties.get(name).map_or("", String::as_str));
                let as_held = format!(
                    "<Project>\n  <PropertyGroup><A>{}</A><B>{}</B><U>{}</U></PropertyGroup>\n  \
                     {site}\n  <PropertyGroup><After>ok</After>{later}</PropertyGroup>\n\
                     </Project>\n",
                    walk_held("A"),
                    walk_held("B"),
                    walk_held("U"),
                );
                if oracle
                    .project_design_time(&as_held, &names, Some(&project_path), &[])
                    .is_some()
                {
                    tally.rejected_on_an_uncertain_value += 1;
                    census.reached(&hostile, "msbuild-rejects-on-an-uncertain-value");
                    continue;
                }
                // The generated piece reads a name the walk holds no value
                // of (a write it refused to compute): whether MSBuild's value
                // makes it throw is the same judgement as for `U`.
                let piece = if template.contains("{t}") {
                    &body
                } else {
                    &gate
                };
                if property_references(piece).iter().any(|name| {
                    ["A", "B", "U"].contains(name) && !parsed.properties.contains_key(*name)
                }) {
                    tally.rejected_on_an_uncertain_value += 1;
                    census.reached(&hostile, "msbuild-rejects-on-an-uncertain-value");
                    continue;
                }
                // A text holding an expression the walk does not model, which
                // MSBuild may throw on: #1094's gap.
                let held_values = property_map(&[
                    ("A".to_owned(), walk_held("A")),
                    ("B".to_owned(), walk_held("B")),
                    ("U".to_owned(), walk_held("U")),
                ]);
                let unmodelled = template.contains("{t}")
                    && substitute(&body, &held_values)
                        .1
                        .iter()
                        .any(|issue| matches!(issue, Issue::Unsupported { .. }));
                assert!(
                    unmodelled,
                    "certain-implies-exact violated: MSBuild rejects this project, as the walk \
                     holds `U` too, and the walk committed {ours:?}\n{}",
                    describe()
                );
                tally.rejected_on_an_unmodelled_body += 1;
                census.reached(&hostile, "msbuild-rejects-on-an-unmodelled-body");
                continue;
            }
            census.reached(&hostile, outcome(true, false));
            continue;
        };
        assert_ne!(
            parsed.rejection.as_ref().map(|r| r.certainty),
            Some(RejectionCertainty::Certain),
            "certain-implies-exact violated: the walk claims MSBuild rejects this project, \
             and MSBuild evaluates it\n{}",
            describe()
        );
        for (name, value) in &ours {
            tally.committed += 1;
            assert_eq!(
                Some(value),
                theirs.get(*name),
                "certain-implies-exact violated for {name}\n{}",
                describe()
            );
        }
        let committed = ours.iter().any(|(name, _)| name.as_str() == "After");
        tally.evaluated_and_committed += usize::from(committed);
        census.reached(&hostile, outcome(false, committed));
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff project_sweep_fixed_seed",
    );
    tally
}

/// [`project_sweep`] at a fixed seed.
#[test]
fn project_sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1009_0b5e_55ed);
    let tally = project_sweep(&mut rng, 1_500);
    eprintln!("rejection project sweep: {tally:?}");
    // Anti-vacuity: MSBuild rejects and evaluates generated projects, the walk
    // claims rejections and allows them, and commits values beside them.
    assert!(tally.msbuild_rejects >= 200, "{tally:?}");
    assert!(tally.certain >= 100, "{tally:?}");
    assert!(tally.possible >= 100, "{tally:?}");
    assert!(tally.evaluated_and_committed >= 200, "{tally:?}");
    // The projects MSBuild rejects that the walk commits, by the open gap
    // each is: pinned, so that closing one, or widening one, shows here.
    assert_eq!(
        (
            tally.rejected_on_an_uncertain_value,
            tally.rejected_on_an_unmodelled_body
        ),
        (25, 4),
        "the projects MSBuild rejects that the walk commits moved: pin the new counts if \
         #1051's second stage or #1094 now judges more of them, or if the generator changed \
         ({tally:?})"
    );
}

/// Fresh-seed twin of [`project_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the rejection judgement"]
fn project_sweep_soak() {
    let (seed, cases) = soak_parameters("rejection project", 10_000);
    let mut rng = SplitMix64(seed);
    let tally = project_sweep(&mut rng, cases);
    eprintln!("rejection project soak: {tally:?}");
}

/// The table the oracle's `eval` evaluates against, which writes each value
/// as a property's text: text of whitespace alone is no text to MSBuild
/// (`'$(B)' == ''` is true for `B` written as a space; probed,
/// msbuild-condition-oracle, SDK 10.0.401).
fn property_map<'a>(pairs: impl IntoIterator<Item = &'a (String, String)>) -> PropertyMap {
    let mut map = PropertyMap::new();
    for (name, value) in pairs {
        let blank = value.chars().all(|c| matches!(c, ' ' | '\t' | '\r' | '\n'));
        map.insert(name.as_str(), if blank { "" } else { value.as_str() });
    }
    map
}

/// `value`, a value as MSBuild holds it, spelt as property text MSBuild
/// reads back to exactly it: every character MSBuild unescapes or expands,
/// every control character (which XML cannot hold), and XML's markup
/// characters, as `%XX`.
fn spelt(value: &str) -> String {
    value
        .chars()
        .map(|c| {
            if c.is_ascii() && (c.is_ascii_control() || "%*?@$();'<>&\"".contains(c)) {
                format!("%{:02X}", c as u32)
            } else {
                c.to_string()
            }
        })
        .collect()
}

#[derive(Debug, Default)]
struct JudgeCensus {
    cases: usize,
    /// Conditions judged unable to throw where an operand reached on certain
    /// values had no boolean: MSBuild evaluated them without throwing.
    never_though_unevaluated: usize,
    /// Conditions judged to throw perhaps, past an operand the walk does not
    /// model on certain values, where MSBuild threw.
    maybe_on_certain_values_threw: usize,
    /// Conditions judged to throw whatever the uncertain values hold.
    certainly: usize,
}

/// The hostile values the condition-level sweep cannot carry: an
/// `expression`-bearing value is one only a property write expands, and the
/// sweep hands the evaluator values, not writes.
const JUDGE_EXCLUDED: &[(Dimension, &str)] = &[
    (
        Dimension::SelfSetProperty,
        "a reference in a value is expanded only by a property write; the project sweep reaches it",
    ),
    (
        Dimension::ReadsTheBuild,
        "a property function in a value is expanded only by a property write; the project sweep \
         reaches it",
    ),
    (
        Dimension::OverwrittenLater,
        "a condition is evaluated against one table, with no later write; the project sweep \
         reaches it",
    ),
];

/// `judge` held to MSBuild under every assignment of the uncertain names from
/// [`GRADED`], certain names holding hostile values: its value is MSBuild's
/// wherever MSBuild gives one; [`Throws::Never`] means MSBuild throws under no
/// assignment, whatever operand had no boolean on certain values; and
/// [`Throws::Certainly`] means it throws under every one.
fn classified_judgement_sweep(rng: &mut SplitMix64, cases: usize) -> JudgeCensus {
    let census = coverage::open(
        "crates/msbuild/tests/rejection_generative_diff.rs",
        "judge_operands",
        JUDGE_EXCLUDED,
    );
    let excluded: BTreeSet<Dimension> = JUDGE_EXCLUDED.iter().map(|(d, _)| *d).collect();
    let mut oracle = Oracle::spawn();
    let mut tally = JudgeCensus::default();
    let uncertain = |name: &str| ["U", "V"].iter().any(|u| u.eq_ignore_ascii_case(name));
    while tally.cases < cases {
        let a = draw_value(rng);
        let b = draw_value(rng);
        if a.hostile
            .iter()
            .chain(&b.hostile)
            .any(|d| excluded.contains(d))
        {
            continue;
        }
        let hostile: BTreeSet<Dimension> = a.hostile.iter().chain(&b.hostile).copied().collect();
        let condition = condition(rng, &["A", "B", "U", "V"], 3);
        let certain = vec![("A".to_owned(), a.value), ("B".to_owned(), b.value)];
        // The values the walk holds for the uncertain names, which a sound
        // judgement never reads.
        let held: Vec<(String, String)> = ["U", "V"]
            .iter()
            .filter_map(|name| rng.pick(GRADED).map(|v| (name.to_string(), v.to_string())))
            .collect();
        let judged = judge(
            &condition,
            &property_map(certain.iter().chain(&held)),
            &uncertain,
        );
        // On certain values alone, the uncertain names as held: whether an
        // operand the walk does not model was reached.
        let on_held = judge(
            &condition,
            &property_map(certain.iter().chain(&held)),
            &|_| false,
        );
        tally.cases += 1;
        let (mut threw, mut held_value) = (false, false);
        for u in GRADED {
            for v in GRADED {
                let mut props = certain.clone();
                props.extend(u.map(|u| ("U".to_string(), u.to_string())));
                props.extend(v.map(|v| ("V".to_string(), v.to_string())));
                match oracle.eval(&condition, &props) {
                    Some(value) => {
                        held_value = true;
                        assert!(
                            judged.value.is_none_or(|judged| judged == value),
                            "{condition}: judged {judged:?}, MSBuild gives {value} under {props:?}"
                        );
                        assert_ne!(
                            judged.throws,
                            Throws::Certainly,
                            "{condition}: MSBuild gives {value} under {props:?}"
                        );
                    }
                    None => {
                        threw = true;
                        assert_ne!(
                            judged.throws,
                            Throws::Never,
                            "{condition}: judged {judged:?}, and MSBuild throws under {props:?}"
                        );
                    }
                }
            }
        }
        tally.never_though_unevaluated +=
            usize::from(judged.throws == Throws::Never && judged.unevaluated && held_value);
        tally.maybe_on_certain_values_threw +=
            usize::from(on_held.throws == Throws::Maybe && on_held.unevaluated && threw);
        tally.certainly += usize::from(judged.throws == Throws::Certainly);
        let verdict = match judged.throws {
            Throws::Never => "never",
            Throws::Maybe => "maybe",
            Throws::Certainly => "certainly",
        };
        census.reached(&hostile, verdict);
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff classified_judgement_sweep_fixed_seed",
    );
    tally
}

/// [`classified_judgement_sweep`] at a fixed seed.
#[test]
fn classified_judgement_sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1009_c1a5_51f1);
    let tally = classified_judgement_sweep(&mut rng, 600);
    eprintln!("classified judgement sweep: {tally:?}");
    assert!(tally.never_though_unevaluated >= 5, "{tally:?}");
    assert!(tally.maybe_on_certain_values_threw >= 20, "{tally:?}");
    assert!(tally.certainly >= 20, "{tally:?}");
}

/// Fresh-seed twin of [`classified_judgement_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching condition.rs"]
fn classified_judgement_sweep_soak() {
    let (seed, cases) = soak_parameters("classified judgement", 5_000);
    let mut rng = SplitMix64(seed);
    let tally = classified_judgement_sweep(&mut rng, cases);
    eprintln!("classified judgement soak: {tally:?}");
}
