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
//! throw in every position of `And`/`Or` chains, and a write after the site
//! that the item pass reads and the property pass does not. Each project is graded
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
use borzoi_oracle_harness::manifest::{self, Manifest};
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

/// [`draw_value`] for a property's last write: no hostile value a later
/// write would put back, as nothing does.
fn draw_final_value(rng: &mut SplitMix64) -> hostile::Drawn<String> {
    let plain = *rng.pick(PLAIN);
    let finals = value::alphabet().filtered(|entry| entry.value.write == value::Write::Final);
    match hostile::sample(&finals, rng.next()) {
        Some(entry) => hostile::Drawn::of(entry).map(|v| v.render(plain)),
        None => hostile::Drawn::plain(plain.to_owned()),
    }
}

#[test]
fn a_last_write_draws_no_value_a_later_write_puts_back() {
    let mut rng = SplitMix64(0x1092);
    let drawn: Vec<_> = (0..20_000).map(|_| draw_final_value(&mut rng)).collect();
    assert!(drawn.iter().any(|d| !d.hostile.is_empty()));
    assert!(
        drawn
            .iter()
            .all(|d| !d.hostile.contains(&Dimension::OverwrittenLater))
    );
}

/// An operand naming one of `names`: a literal, a reference, or a property
/// function, modelled or not, that may throw on its receiver.
fn operand(rng: &mut SplitMix64, names: &[&str]) -> String {
    let name = *rng.pick(names);
    let other = *rng.pick(names);
    match rng.below(31) {
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
        // A version function's arguments in each string delimiter.
        13 => format!(
            "'$([MSBuild]::VersionLessThan({q}$({name}){q}, {q}2.0{q}))'",
            q = rng.pick(&["`", "\""])
        ),
        // An unquoted literal argument, and the `null` MSBuild binds to none.
        14 => format!("'$({name}.TrimStart(vV))'"),
        15 => format!(
            "'$({name}.Contains({}))'",
            rng.pick(&["null", "NULL", "ab"])
        ),
        16 => "'$([System.String]::IsNullOrEmpty(null))'".to_owned(),
        // A boolean the walk does not compute (whitespace outside ASCII).
        17 => "'$([System.String]::IsNullOrWhiteSpace(\"\u{a0}\"))'".to_owned(),
        // A literal tab, which MSBuild reads as itself in an attribute.
        18 => format!("'$({name}.Split(\"\t\")[1])'"),
        19 => format!("'$({name}[0])$({other}[9])'"),
        // Arguments in each spelling MSBuild reads: unquoted around an
        // expansion, unquoted and bare, two expansions.
        21 => format!("'$([MSBuild]::VersionLessThan($({name}).0, 2.0))'"),
        22 => format!("'$([MSBuild]::VersionGreaterThan($({name}), 1.0))'"),
        23 => format!("'$([MSBuild]::VersionLessThan($({name}),$({other})))'"),
        // An item list and a metadatum in a function's argument: read as
        // written in a condition or an operation, the metadatum's value in a
        // metadatum.
        24 => "'$([MSBuild]::VersionEquals(\"@(J)\", \"1.0\"))'".to_owned(),
        25 => "'$([System.String]::IsNullOrEmpty(\"%(V)\"))'".to_owned(),
        // A boolean the walk does not compute beside each check that may
        // throw on it: text, a version parse, a reference that may complete
        // an item expression.
        26 => "'x$([System.String]::IsNullOrWhiteSpace(\"\u{a0}\"))'".to_owned(),
        27 => {
            "'$([System.Version]::Parse($([System.String]::IsNullOrWhiteSpace(\"\u{a0}\"))).Build)'"
                .to_owned()
        }
        28 => format!("'$([System.String]::IsNullOrWhiteSpace(\"\u{a0}\"))$({name})$({other})'"),
        // Text before a throw: equality asks whether the operand is empty
        // without expanding it, so a comparison with an empty one never
        // reaches the throw.
        30 => format!("'a$({name}[9])'"),
        // A throw before a later step that reads another name.
        29 => format!("'$({name}.Split(\";\")[9].Contains(\"$({other})\"))'"),
        _ => format!("'$({name}.Split(\";\")[1].Length)'"),
    }
}

/// An [`operand`] for a condition: one without an item list or metadata
/// reference written in it, which puts the whole condition outside the
/// grammar the walk parses, a gap of its own (#1095) the sweep would only
/// pin.
fn condition_operand(rng: &mut SplitMix64, names: &[&str]) -> String {
    loop {
        let op = operand(rng, names);
        if !op.contains("@(") && !op.contains("%(") {
            break op;
        }
    }
}

/// A condition over `names`: comparisons of every form that can throw,
/// coerced scalars, built-ins, nested under `!`, `And` and `Or`.
fn condition(rng: &mut SplitMix64, names: &[&str], depth: u32) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(10) {
            0 => rng.pick(&["true", "false"]).to_string(),
            1 => condition_operand(rng, names),
            2 => format!("HasTrailingSlash({})", condition_operand(rng, names)),
            3 => format!(
                "$([MSBuild]::VersionLessThan({q}$({}){q}, {q}2.0{q}))",
                rng.pick(names),
                q = rng.pick(&["'", "`", "\""])
            ),
            9 => "$([System.String]::IsNullOrWhiteSpace('\u{a0}'))".to_owned(),
            // The version part the condition grammar reads itself, of a
            // boolean the walk does not compute.
            8 => format!(
                "$([System.Version]::Parse($([System.String]::IsNullOrWhiteSpace('\u{a0}'))).Build) {} 1",
                rng.pick(&["==", "<"])
            ),
            4 => format!("Exists({})", condition_operand(rng, names)),
            _ => format!(
                "{} {} {}",
                condition_operand(rng, names),
                rng.pick(&["==", "!=", "<", "<=", ">", ">="]),
                condition_operand(rng, names)
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

/// What a text's expression on a name the walk is not sure of is struck to:
/// the values the walk's own judgement tries such an expression as returning
/// (`condition::RETURNED`), so that a rejection that survives every one is
/// one the walk claims.
const STRUCK_AS: &[&str] = &["", "x", "1", "1.2", "true", "false", "a;b", "-"];

/// The ways `n` struck expressions can each take a value of [`STRUCK_AS`]:
/// all of them, where there are few enough (`n` ≤ 3), else each value for
/// all and each pair of values split in turn. None for no expression.
fn assignments(n: usize) -> Vec<Vec<&'static str>> {
    if n == 0 {
        return Vec::new();
    }
    if n <= 3 {
        let mut all: Vec<Vec<&'static str>> = vec![Vec::new()];
        for _ in 0..n {
            all = all
                .into_iter()
                .flat_map(|prefix| {
                    STRUCK_AS.iter().map(move |value| {
                        let mut next = prefix.clone();
                        next.push(*value);
                        next
                    })
                })
                .collect();
        }
        return all;
    }
    let mut some: Vec<Vec<&'static str>> = Vec::new();
    for a in STRUCK_AS {
        for b in STRUCK_AS {
            for split in 0..n {
                some.push((0..n).map(|i| if i == split { *b } else { *a }).collect());
            }
        }
    }
    some
}

/// The innermost `$(…)` expressions of a generated `piece` that `reads`
/// accepts: those holding no other such expression, so that striking each
/// leaves a function around it standing (`VersionLessThan('$(X)', …)` keeps
/// its type when `$(X)` is struck).
fn innermost_expressions(piece: &str, reads: &dyn Fn(&str) -> bool) -> Vec<String> {
    let mut found = Vec::new();
    let mut pending = vec![piece.to_owned()];
    while let Some(text) = pending.pop() {
        for expression in expressions(&text) {
            if !reads(expression) {
                continue;
            }
            let inner = &expression[2..expression.len() - 1];
            if expressions(inner).iter().any(|nested| reads(nested)) {
                pending.push(inner.to_owned());
            } else {
                found.push(expression.to_owned());
            }
        }
    }
    found
}

/// Every `$(…)` expression of a generated `piece`, at any depth, whose
/// receiver is one of `names` (`$(X.Split(';')[9])`): its evaluation reads
/// that name before anything else.
fn receiver_expressions(piece: &str, names: &[&str]) -> Vec<String> {
    let mut found = Vec::new();
    let mut pending = vec![piece.to_owned()];
    while let Some(text) = pending.pop() {
        for expression in expressions(&text) {
            let inner = &expression[2..expression.len() - 1];
            let receiver: String = inner
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if names.contains(&receiver.as_str()) {
                found.push(expression.to_owned());
            }
            pending.push(inner.to_owned());
        }
    }
    found
}

/// The outermost `$(…)` expressions of a generated `piece`, in order. The
/// generator writes no parenthesis inside a string, so counting them finds
/// each one's end.
fn expressions(piece: &str) -> Vec<&str> {
    let mut found = Vec::new();
    let mut rest = piece;
    while let Some(at) = rest.find("$(") {
        let mut depth = 0usize;
        let mut end = None;
        for (i, c) in rest[at + 1..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(at + 1 + i + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else { break };
        found.push(&rest[at..end]);
        rest = &rest[end..];
    }
    found
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

/// Items every generated project declares before its site: `J`, which a
/// function's argument names as an item list (`@(J)`), and `Foo`, which a
/// value of the item-expression dimension completes one over
/// (`@(Foo->…)`).
const ITEMS: &str = "<ItemGroup><J Include=\"1.0\" /><Foo Include=\"f\" /></ItemGroup>";

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
    // Metadata MSBuild substitutes before it calls a function on it.
    "<ItemDefinitionGroup><I><V>1.0</V><M>{t}$([MSBuild]::VersionLessThan('%(V)', '2.0'))</M></I></ItemDefinitionGroup>",
    "<ItemGroup><I Include=\"x\" V=\"1.0\" M=\"{t}$([MSBuild]::VersionLessThan('%(V)', '2.0'))\" /></ItemGroup>",
    // Attributes MSBuild does not expand, and metadata it expands only where
    // an update applies.
    "<ItemGroup><I Include=\"x\" Label=\"{t}\" /></ItemGroup>",
    "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Label=\"{t}\" />",
    "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Runtime=\"{t}\" />",
    "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" RequiredRuntime=\"{t}\" />",
    // An inline task's body, which MSBuild expands as it
    // registers the task.
    "<UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\"><Task>{t}</Task></UsingTask>",
    "<ItemGroup><I Update=\"nothere\" M=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\" /><I Update=\"x\" M=\"{t}\" /></ItemGroup>",
    // Each operation's attributes, on its own item and on others'.
    "<ItemGroup><I Include=\"x\" /><I Remove=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Update=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\" /><I Remove=\"@(J)\" MatchOnMetadata=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Remove=\"@(J)\" MatchOnMetadata=\"M\" MatchOnMetadataOptions=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\" MatchOnMetadata=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Update=\"x\" MatchOnMetadata=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\" KeepMetadata=\"{t}\" /></ItemGroup>",
    "<ItemGroup><I Include=\"x\" V=\"1.0\"><M>{t}</M></I></ItemGroup>",
    "<Import Project=\"there.props\" Condition=\"{c}\" />",
    "<Choose><When Condition=\"{c}\"><PropertyGroup><R>x</R></PropertyGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_FALSE\" /><When Condition=\"{c}\" /></Choose>",
    // Content the walk does not take: a write then a read on one path, and a
    // write in one branch beside a read in its sibling, items and conditions
    // alike (what the walk judges there it judges with those names unknown).
    "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><A>1</A><R>{t}</R></PropertyGroup>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><Choose><When Condition=\"UNDECIDED_FALSE\"><PropertyGroup><A>abcdefghijklmnop</A></PropertyGroup></When><Otherwise><ItemGroup><I Include=\"{t}\" /></ItemGroup></Otherwise></Choose></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><Choose><When Condition=\"UNDECIDED_FALSE\"><PropertyGroup><B>abcdefghijklmnop</B></PropertyGroup></When><Otherwise><ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup></Otherwise></Choose></When></Choose>",
    // An arm the walk does not take, whose items MSBuild evaluates in its item
    // pass, against the final table, a write after the `<Choose>` included
    // (#1092).
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><ItemGroup><I Include=\"x\"><M>{t}</M></I></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_FALSE\" /><Otherwise><ItemGroup><I Include=\"{t}\" /></ItemGroup></Otherwise></Choose>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>1</A></PropertyGroup><ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup></When></Choose>",
];

/// Whether `template` puts its text in a metadatum's value, where MSBuild
/// expands metadata references before properties.
fn is_metadata_site(template: &str) -> bool {
    template.contains("<M>{t}") || template.contains("M=\"{t}")
}

/// Whether `template` puts its piece where MSBuild reads it after every
/// property write: in an `<ItemGroup>`, an `<ItemDefinitionGroup>` or a
/// `<UsingTask>`, however deep in a `<Choose>`. A condition of a `<When>` or a
/// property is read by the property pass.
fn read_in_item_pass(template: &str) -> bool {
    let at = template
        .find("{c}")
        .or_else(|| template.find("{t}"))
        .expect("a site holds a piece");
    let before = &template[..at];
    ["ItemGroup", "ItemDefinitionGroup", "UsingTask"]
        .iter()
        .any(|tag| {
            before.matches(&format!("<{tag}")).count()
                > before.matches(&format!("</{tag}>")).count()
        })
}

#[test]
fn sites_read_in_the_item_pass_are_the_item_groups_and_tasks() {
    let item_pass: Vec<&str> = SITES
        .iter()
        .copied()
        .filter(|t| read_in_item_pass(t))
        .collect();
    assert!(item_pass.iter().all(|t| !t.starts_with("<PropertyGroup")));
    assert!(read_in_item_pass(
        "<Choose><When Condition=\"UNDECIDED_TRUE\"><ItemGroup><I Include=\"{t}\" /></ItemGroup></When></Choose>"
    ));
    assert!(!read_in_item_pass(
        "<ItemGroup><I Include=\"x\" /></ItemGroup><Choose><When Condition=\"{c}\" /></Choose>"
    ));
    assert!(read_in_item_pass(
        "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Runtime=\"{t}\" />"
    ));
}

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
    /// Projects the baseline revision answers wrongly
    /// (`manifests/rejection_projects_baseline.txt`): it commits a value of a
    /// project MSBuild rejects, a value MSBuild does not hold, or a certain
    /// rejection of a project MSBuild evaluates.
    baseline_wrong: usize,
    /// Of those, the ones the walk under test answers rightly or withdraws.
    baseline_wrong_now_not: usize,
}

/// What the baseline revision made of each fixed-seed project, by case
/// (`tests/rejection_baseline.rs`, `tools/rejection-baseline.sh`).
struct Baseline {
    revision: String,
    cases: HashMap<String, BaselineCase>,
}

struct BaselineCase {
    hash: String,
    certain: bool,
    /// Each value committed, by name, as [`encode`] spells it.
    committed: Vec<(String, String)>,
}

impl Baseline {
    fn load() -> Self {
        let path = format!(
            "{}/tests/manifests/rejection_projects_baseline.txt",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = borzoi_msbuild::observed::host_fs::read_to_string(&path).unwrap_or_default();
        let mut revision = String::new();
        let mut cases = HashMap::new();
        for line in text.lines() {
            if let Some(rest) = line.strip_prefix("# Regenerate: bash tools/rejection-baseline.sh ")
            {
                revision = rest.to_owned();
            }
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let mut fields = line.splitn(4, '\t');
            let (Some(key), Some(hash), Some(rejection), committed) =
                (fields.next(), fields.next(), fields.next(), fields.next())
            else {
                panic!("{path}: malformed line {line:?}");
            };
            let committed = committed
                .unwrap_or("")
                .split(' ')
                .filter(|field| !field.is_empty())
                .map(|field| {
                    let (name, value) = field.split_once('=').expect("name=value");
                    (name.to_owned(), value.to_owned())
                })
                .collect();
            cases.insert(
                key.to_owned(),
                BaselineCase {
                    hash: hash.to_owned(),
                    certain: rejection == "certain",
                    committed,
                },
            );
        }
        Baseline { revision, cases }
    }

    /// Whether the baseline answered `key` wrongly, MSBuild holding `theirs`
    /// (`None`: it rejects); `None` where the baseline has no record of this
    /// project's text, `hash`.
    fn wrong(
        &self,
        key: &str,
        hash: &str,
        theirs: Option<&HashMap<String, String>>,
    ) -> Option<bool> {
        let case = self.cases.get(key).filter(|case| case.hash == hash)?;
        Some(match theirs {
            None => !case.committed.is_empty(),
            Some(theirs) => {
                case.certain
                    || case.committed.iter().any(|(name, value)| {
                        theirs.get(name).map(|v| encode(v)) != Some(value.clone())
                    })
            }
        })
    }
}

/// `value` as one space-free field, as `tests/rejection_baseline.rs` spells
/// it.
fn encode(value: &str) -> String {
    value.escape_default().to_string().replace(' ', "\\x20")
}

/// FNV-1a over `text`'s bytes, as hex, as `tests/rejection_baseline.rs`
/// computes it.
fn fnv1a(text: &str) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{hash:016x}")
}

/// What [`project_sweep`] holds the walk to beyond MSBuild, at a fixed seed:
/// the baseline revision's answers, and the pin of each project the walk
/// answers wrongly.
struct Grading {
    baseline: Baseline,
    /// Where to write each generated project, for `tools/rejection-baseline.sh`.
    dump: Option<std::path::PathBuf>,
    /// Projects whose text the baseline has no record of.
    stale: Vec<String>,
    /// Projects the baseline answered rightly, or withdrew, that the walk
    /// under test answers wrongly.
    regressed: Vec<String>,
    /// Each project the walk under test answers wrongly, by the gap it is.
    wrong: Vec<(String, String)>,
}

/// The hostile values the project sweep cannot carry yet.
const PROJECT_EXCLUDED: &[(Dimension, &str)] = &[(
    Dimension::ReadsTheBuild,
    "each value calls a property function in a property body, and one the walk does not model \
     there, which MSBuild may throw on, is no rejection site yet (#1094)",
)];

/// The body of `X`, a write the walk refuses to compute (a function it does
/// not model), so that it holds no value of `X`; MSBuild holds `Debug`, and
/// throws on nothing.
const REFUSED: &str = "$([System.String]::Copy('Debug'))";

/// The values the names the walk is not sure of are varied over (beside
/// `""`), to show that MSBuild's rejection rests on them: a number, a word, a
/// version, a boolean, and a long value every indexer and separator the
/// generator uses finds room in.
const VARIED_VALUES: &[&str] = &[
    "1",
    "abc",
    "a;b\tc;d\te;f\tg;h\ti;j;k\tl;m;n;o",
    "1.2.3",
    "true",
];

/// What a value of the overwritten-later dimension is reset to after the
/// site.
const RESET: &str = "1";

/// The value of `name` (`A` or `B`, first written as `drawn`) that a site
/// reads: the property pass reads the first write; the item pass the last,
/// the rewrite, else the reset, else the first.
fn value_read_at_site(
    item_pass: bool,
    name: &str,
    drawn: &hostile::Drawn<String>,
    rewrite: Option<&str>,
    rewritten: &hostile::Drawn<String>,
) -> hostile::Drawn<String> {
    if item_pass && rewrite == Some(name) {
        rewritten.clone()
    } else if item_pass && drawn.hostile.contains(&Dimension::OverwrittenLater) {
        hostile::Drawn::plain(RESET.to_owned())
    } else {
        drawn.clone()
    }
}

#[test]
fn a_site_reads_the_write_its_pass_sees() {
    let reset = value::alphabet()
        .of(Dimension::OverwrittenLater)
        .next()
        .map(|entry| hostile::Drawn::of(entry).map(|v| v.render("abc")))
        .expect("the alphabet has an overwritten-later value");
    let plain = hostile::Drawn::plain("abc".to_owned());
    let rewritten = hostile::Drawn::plain("2.0".to_owned());
    let read = |item_pass, drawn: &hostile::Drawn<String>, rewrite| {
        value_read_at_site(item_pass, "A", drawn, rewrite, &rewritten).value
    };
    assert_eq!(read(false, &reset, Some("A")), reset.value);
    assert_eq!(read(true, &reset, Some("A")), "2.0");
    assert_eq!(read(true, &reset, Some("B")), RESET);
    assert_eq!(read(true, &reset, None), RESET);
    assert_eq!(read(true, &plain, Some("B")), "abc");
    assert_eq!(read(true, &plain, Some("A")), "2.0");
}

/// Whether the rewrite after the site reaches what is graded: where MSBuild
/// evaluates the property pass through to it, which it does wherever it
/// evaluates the project (`evaluated`), and wherever the site is read in the
/// item pass (`item_pass`), after every property write. A rejection in the
/// property pass, before it, is none of the rewrite's.
fn rewrite_is_graded(item_pass: bool, evaluated: bool) -> bool {
    item_pass || evaluated
}

#[test]
fn a_rejection_before_the_rewrite_is_none_of_its() {
    assert!(!rewrite_is_graded(false, false));
    assert!(rewrite_is_graded(false, true));
    assert!(rewrite_is_graded(true, false));
    assert!(rewrite_is_graded(true, true));
}

/// What one generated project is made of.
struct Drawing {
    /// The certain properties' values.
    a: hostile::Drawn<String>,
    b: hostile::Drawn<String>,
    /// `U` as the walk holds it, and as MSBuild does.
    held: hostile::Drawn<String>,
    real: hostile::Drawn<String>,
    /// A write of `A` or `B` after the site, of a value of its own: a read of
    /// the item pass (and of `UsingTask`'s pass) is of this value, one of the
    /// property pass of the value before it (#1092).
    rewritten: hostile::Drawn<String>,
    rewrite: Option<&'static str>,
    /// Where the piece goes ([`SITES`]), and the pieces: a text and a
    /// condition.
    template: &'static str,
    body: String,
    gate: String,
}

/// A project drawn from `rng`, or `None` where a value it drew carries an
/// `excluded` dimension, before it draws the pieces.
fn draw_project(rng: &mut SplitMix64, excluded: &BTreeSet<Dimension>) -> Option<Drawing> {
    let a = draw_value(rng);
    let b = draw_value(rng);
    let held = draw_value(rng);
    let real = draw_value(rng);
    let rewritten = draw_final_value(rng);
    let rewrite: Option<&'static str> = *rng.pick(&[None, None, Some("A"), Some("B")]);
    let carried = [&a, &b, &held, &real]
        .into_iter()
        .chain(rewrite.map(|_| &rewritten))
        .flat_map(|drawn| drawn.hostile.iter());
    if carried.into_iter().any(|d| excluded.contains(d)) {
        return None;
    }
    // `X` is a write the walk refuses to compute: it holds no value of it.
    let operands = ["A", "B", "U", "X"];
    let template = *rng.pick(SITES);
    let body = text(rng, &operands);
    let gate = condition(rng, &operands, 3);
    Some(Drawing {
        a,
        b,
        held,
        real,
        rewritten,
        rewrite,
        template,
        body,
        gate,
    })
}

/// A project held to the gap it pins, whatever the generator's stream
/// draws: each of [`project_sweep`]'s classifications of a project MSBuild
/// rejects and the walk commits keeps a witness, so that a classifier no
/// drawn project reaches still answers for one.
struct Witness {
    /// `A`, `B`, `U` as the walk holds it, `U` as MSBuild holds it.
    values: [&'static str; 4],
    template: &'static str,
    body: &'static str,
    gate: &'static str,
    /// The gap it pins (`manifests/rejection_projects_wrong.txt`'s spelling).
    gap: &'static str,
    /// Whether only striking both its unmodelled expressions and those on the
    /// names the walk is not sure of shows the rejection, with the values the
    /// classifier tries: held, so that a value added to them that rescues the
    /// witness fails here rather than retiring the step it answers for.
    both_strikes: bool,
}

impl Witness {
    fn drawing(&self) -> Drawing {
        let [a, b, held, real] = self.values.map(|v| hostile::Drawn::plain(v.to_owned()));
        Drawing {
            a,
            b,
            held,
            real,
            rewritten: hostile::Drawn::plain(String::new()),
            rewrite: None,
            template: self.template,
            body: self.body.to_owned(),
            gate: self.gate.to_owned(),
        }
    }
}

/// One witness per gap, each a project an earlier fixed seed drew.
const WITNESSES: &[Witness] = &[
    Witness {
        values: ["1.2.3", "true @evil.rsp", "1", "1.2.3"],
        template: "<Choose><When Condition=\"UNDECIDED_TRUE\"><Choose><When Condition=\"UNDECIDED_FALSE\"><PropertyGroup><B>abcdefghijklmnop</B></PropertyGroup></When><Otherwise><ItemGroup Condition=\"{c}\"><I Include=\"x\" /></ItemGroup></Otherwise></Choose></When></Choose>",
        body: "",
        gate: "!(Exists('$([MSBuild]::VersionLessThan(`$(X)`, `2.0`))'))",
        gap: "uncertain-value",
        both_strikes: false,
    },
    Witness {
        values: ["1.2.3", "x;y;z", "1.2.3", "2.0"],
        template: "<ItemGroup Condition=\"false\"><I Include=\"{t}\" /></ItemGroup>",
        body: "$(A.Contains(NULL))",
        gate: "",
        gap: "unmodelled-body",
        both_strikes: false,
    },
    // The same gap, beside an expression on `X` no value tried for it
    // rescues (none is 41 characters long): the classifier reaches it only by
    // striking both, so this keeps that step answering for a project.
    Witness {
        values: ["2.0", "true\n/out:obj/Evil.dll", "1.2.3", "abc"],
        template: "<ItemGroup><I Include=\"{t}\" /></ItemGroup>",
        body: "$([MSBuild]::VersionGreaterThan($(B), 1.0));$(X[40])",
        gate: "",
        gap: "unmodelled-body",
        both_strikes: true,
    },
];

/// The long value of [`VARIED_VALUES`] has room for every indexer
/// [`operand`] writes: `Split(";")[9]`, `Split("\t")[1]` and `[9]`.
#[test]
fn a_varied_value_has_room_for_every_indexer() {
    assert!(VARIED_VALUES.iter().any(|value| {
        value.split(';').count() > 9 && value.split('\t').count() > 1 && value.chars().count() > 9
    }));
}

#[test]
fn every_witness_stands_at_a_site_the_generator_draws() {
    for witness in WITNESSES {
        assert!(SITES.contains(&witness.template), "{}", witness.template);
    }
}

/// Generate `cases` projects from `rng` and grade each against MSBuild.
fn project_sweep(
    rng: &mut SplitMix64,
    cases: usize,
    mut grading: Option<&mut Grading>,
) -> ProjectCensus {
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
    let names: Vec<String> = ["A", "B", "U", "X", "R", "After", "Delta"]
        .map(String::from)
        .to_vec();
    let mut tally = ProjectCensus::default();
    // The witnesses first, each held to the gap it pins; then the drawn
    // projects.
    let mut witnesses = WITNESSES.iter().enumerate();
    // The gap the case just graded was pinned as, and the witness's own
    // expectation of it.
    let gap_seen: std::cell::Cell<Option<&'static str>> = std::cell::Cell::new(None);
    let strikes_seen = std::cell::Cell::new(false);
    let mut expected: Option<(String, &'static str, bool)> = None;
    let held_to = |expected: Option<(String, &'static str, bool)>| {
        if let Some((key, gap, both_strikes)) = expected {
            assert_eq!(
                (gap_seen.get(), strikes_seen.get()),
                (Some(gap), both_strikes),
                "the witness {key} no longer pins the gap it stands for, by the step it stands for"
            );
        }
    };
    loop {
        held_to(expected.take());
        gap_seen.set(None);
        strikes_seen.set(false);
        let (drawing, witness) = match witnesses.next() {
            Some((index, witness)) => (
                witness.drawing(),
                Some((index, witness.gap, witness.both_strikes)),
            ),
            None if tally.cases < cases => match draw_project(rng, &excluded) {
                Some(drawing) => (drawing, None),
                None => continue,
            },
            None => break,
        };
        let Drawing {
            a,
            b,
            held,
            real,
            rewritten,
            rewrite,
            template,
            body,
            gate,
        } = drawing;
        let mut hostile: BTreeSet<Dimension> = BTreeSet::new();
        for drawn in [&a, &b, &held, &real] {
            hostile.extend(drawn.hostile.iter().copied());
        }
        assert!(
            !hostile
                .iter()
                .chain(rewrite.iter().flat_map(|_| &rewritten.hostile))
                .any(|d| excluded.contains(d)),
            "an excluded dimension is drawn"
        );
        // A witness is graded by its own expectation, not by the baseline, and
        // counted in neither the tally nor the census of drawn projects.
        let mut grading = match witness {
            Some(_) => None,
            None => grading.as_deref_mut(),
        };
        let mut witness_counts = ProjectCensus::default();
        let counts: &mut ProjectCensus = match witness {
            Some(_) => &mut witness_counts,
            None => &mut tally,
        };
        let reach = |hostile: &BTreeSet<Dimension>, outcome: &str| {
            if witness.is_none() {
                census.reached(hostile, outcome);
            }
        };
        // A later write is made of `A` and `B` alone (below), and a value it
        // overwrites reaches only a read of the property pass between the
        // two writes: of the site's piece, at a site of the property pass.
        let piece = if template.contains("{t}") {
            &body
        } else {
            &gate
        };
        let item_pass = read_in_item_pass(template);
        let overwritten_read = [("A", &a), ("B", &b)].into_iter().any(|(name, drawn)| {
            drawn.hostile.contains(&Dimension::OverwrittenLater)
                && !item_pass
                && property_references(piece).contains(&name)
        });
        if !overwritten_read {
            hostile.remove(&Dimension::OverwrittenLater);
        }
        let read_at_site = |name: &str, drawn: &'_ hostile::Drawn<String>| {
            value_read_at_site(item_pass, name, drawn, rewrite, &rewritten)
        };
        let site = template
            .replace("{c}", &xml_attribute(&gate))
            .replace("{t}", &xml_attribute(&body))
            .replace("UNDECIDED_TRUE", &xml_attribute(UNDECIDED_TRUE))
            .replace("UNDECIDED_FALSE", &xml_attribute(UNDECIDED_FALSE));
        // A value overwritten later has been read by the site in between.
        let mut resets = String::new();
        for (name, drawn) in [("A", &a), ("B", &b)] {
            if drawn.hostile.contains(&Dimension::OverwrittenLater) {
                resets.push_str(&format!("<{name}>{RESET}</{name}>"));
            }
        }
        // The writes after the site: the resets, then the rewrite, its body
        // as given.
        let after_site = |rewrite_body: &str| match rewrite {
            Some(name) => format!("{resets}<{name}>{rewrite_body}</{name}>"),
            None => resets.clone(),
        };
        let later = after_site(&xml_text(&rewritten.value));
        // The project, its first group's writes as given: `U` as the walk
        // holds it, then (`real`) as MSBuild holds it, which the walk cannot
        // know.
        let document = |(writes, later): &(String, String), site: &str| {
            format!(
                "<Project>\n  <PropertyGroup>{writes}</PropertyGroup>\n  {ITEMS}\n  {site}\n  \
                 <PropertyGroup><After>ok</After>{later}</PropertyGroup>\n</Project>\n"
            )
        };
        let a_write = format!("<A>{}</A>", xml_text(&a.value));
        let b_write = format!("<B>{}</B>", xml_text(&b.value));
        let x_write = format!("<X>{REFUSED}</X>");
        let writes = format!(
            "{a_write}{b_write}<U>{}</U><U Condition=\"{}\">{}</U>{x_write}",
            xml_text(&held.value),
            xml_attribute(UNDECIDED_TRUE),
            xml_text(&real.value),
        );
        let xml = document(&(writes.clone(), later.clone()), &site);
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
        let key = match witness {
            Some((index, gap, both_strikes)) => {
                let key = format!("witness-{index}");
                expected = Some((key.clone(), gap, both_strikes));
                key
            }
            None => {
                counts.cases += 1;
                format!("case-{:04}", counts.cases)
            }
        };
        match parsed.rejection.as_ref().map(|r| r.certainty) {
            Some(RejectionCertainty::Certain) => counts.certain += 1,
            Some(RejectionCertainty::Possible) => counts.possible += 1,
            None => {}
        }
        let both = oracle.project_both(&xml, &names, Some(&project_path), &[]);
        if rewrite.is_some() && rewrite_is_graded(item_pass, both.design_time.is_some()) {
            hostile.extend(rewritten.hostile.iter().copied());
        }
        let hash = fnv1a(&xml);
        // Whether the baseline answered this project wrongly, and a note of
        // the walk under test answering it wrongly.
        let baseline_wrong = grading.as_deref_mut().and_then(|grading| {
            if let Some(dump) = &grading.dump {
                std::fs::write(dump.join(format!("{key}.xml")), &xml).unwrap();
            }
            let wrong = grading
                .baseline
                .wrong(&key, &hash, both.design_time.as_ref());
            if wrong.is_none() {
                grading.stale.push(key.clone());
            }
            wrong
        });
        counts.baseline_wrong += usize::from(baseline_wrong == Some(true));
        let answered_wrongly = |gap: &'static str, grading: Option<&mut Grading>| {
            gap_seen.set(Some(gap));
            if let Some(grading) = grading {
                grading.wrong.push((key.clone(), format!("{hash} {gap}")));
                if baseline_wrong == Some(false) {
                    grading.regressed.push(format!("{key} ({gap})"));
                }
            }
        };
        let Some(theirs) = both.design_time else {
            counts.msbuild_rejects += 1;
            if ours.is_empty() {
                counts.baseline_wrong_now_not += usize::from(baseline_wrong == Some(true));
                reach(&hostile, outcome(true, false));
                continue;
            }
            // MSBuild rejects, and the walk committed: wrong, unless the
            // rejection rests on what the walk does not judge yet. That is
            // shown, not assumed. With every name as the walk holds it (`U`
            // without the write the walk could not decide, a name it holds a
            // value of written as it holds it), MSBuild evaluates the project:
            // it rejected over a value the walk does not hold. Or it does once
            // the names the walk holds no value of (`X`, a refused write) hold
            // some value, which the walk's judgement leaves to them: a throw
            // on the `""` the walk substitutes is no claim.
            // The walk's reading at the site, before a later write puts a
            // name's plain value back: the property pass's. The item pass
            // reads the final table.
            let at_site = if later.is_empty() || item_pass {
                None
            } else {
                let xml = format!(
                    "<Project>\n  <PropertyGroup>{writes}</PropertyGroup>\n  {ITEMS}\n  {site}\n</Project>\n"
                );
                std::fs::write(&project_path, &xml).unwrap();
                Some(
                    parse_fsproj_with_imports(
                        &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                            .expect("a project path spelt as its full path"),
                        &HashMap::new(),
                        &common::oracle_environment(),
                        None,
                        None,
                    )
                    .expect("well-formed"),
                )
            };
            let parsed = at_site.as_ref().unwrap_or(&parsed);
            let as_held = |name: &str, drawn: &hostile::Drawn<String>, unheld: &str| {
                let text = match (parsed.property(name), parsed.properties.get(name)) {
                    (PropertyRead::Value(_), _) => xml_text(&drawn.value),
                    (_, Some(_)) if !drawn.value.contains("$(") => xml_text(&drawn.value),
                    (_, Some(value)) => spelt(value),
                    (_, None) => xml_text(unheld),
                };
                format!("<{name}>{text}</{name}>")
            };
            // The rewrite the item pass reads, as the walk holds it; one only
            // the property pass reads past, as given.
            let varied = |unheld: &str| {
                let writes = format!(
                    "{}{}{}<X>{}</X>",
                    as_held("A", &a, unheld),
                    as_held("B", &b, unheld),
                    as_held("U", &held, unheld),
                    xml_text(unheld)
                );
                let later = match rewrite {
                    Some(name) if item_pass => {
                        let held = as_held(name, &rewritten, unheld);
                        let body = held
                            .strip_prefix(&format!("<{name}>"))
                            .and_then(|rest| rest.strip_suffix(&format!("</{name}>")))
                            .expect("as_held writes one element");
                        after_site(body)
                    }
                    _ => later.clone(),
                };
                (writes, later)
            };
            let evaluates = |oracle: &mut Oracle, writes: &(String, String), site: &str| {
                oracle
                    .project_design_time(&document(writes, site), &names, Some(&project_path), &[])
                    .is_some()
            };
            if std::iter::once(&"")
                .chain(VARIED_VALUES)
                .any(|value| evaluates(&mut oracle, &varied(value), &site))
            {
                counts.rejected_on_an_uncertain_value += 1;
                answered_wrongly("uncertain-value", grading.as_deref_mut());
                reach(&hostile, "msbuild-rejects-on-an-uncertain-value");
                continue;
            }
            // MSBuild may throw on every value of a name the walk is not sure
            // of, by a different expression for each (`$(X.Split(';')[1])`
            // beside a version function of `$(X)`): the judgement over the
            // values a name may hold (#1009's second stage), which the walk
            // leaves to them. So the rejection is the walk's to see only where
            // it survives with every part reading such a name struck from the
            // site: a condition's leaf by a boolean (true for every one, then
            // false), a text's expression by a value.
            let unsure_names: Vec<&str> = ["A", "B", "U", "X"]
                .into_iter()
                .filter(|name| !matches!(parsed.property(name), PropertyRead::Value(_)))
                .collect();
            let reads_unsure = |text: &str| {
                property_references(text)
                    .iter()
                    .any(|name| unsure_names.contains(name))
            };
            let piece = if template.contains("{t}") {
                &body
            } else {
                &gate
            };
            // Struck two ways: the innermost expressions on such names, which
            // leaves a function around one standing (`VersionLessThan('$(U)',
            // …)`), and each expression whose receiver is such a name, whose
            // throw rests on it whatever a later step reads
            // (`$(X.Split(';')[9].Contains('$(U)'))`).
            let strike_sets = [
                innermost_expressions(piece, &reads_unsure),
                receiver_expressions(piece, &unsure_names),
            ];
            let mut shown = false;
            for unsure_expressions in &strike_sets {
                // The walk judges each leaf alone, and follows no correlation
                // between two such expressions, nor between two places one
                // stands: each place takes its own value, every assignment up
                // to a bound.
                let mut places: Vec<(usize, &str)> = Vec::new();
                for expression in unsure_expressions {
                    for (at, _) in piece.match_indices(expression.as_str()) {
                        if !places.iter().any(|(seen, _)| *seen == at) {
                            places.push((at, expression.as_str()));
                        }
                    }
                }
                places.sort();
                // Places nested in an earlier one are struck with it.
                let mut outer: Vec<(usize, &str)> = Vec::new();
                for (at, expression) in places {
                    if outer
                        .last()
                        .is_none_or(|(last, text)| at >= last + text.len())
                    {
                        outer.push((at, expression));
                    }
                }
                let struck_sites: Vec<String> = assignments(outer.len())
                    .into_iter()
                    .map(|assignment| {
                        let mut struck = String::new();
                        let mut from = 0;
                        for ((at, expression), value) in outer.iter().zip(assignment) {
                            struck.push_str(&piece[from..*at]);
                            struck.push_str(value);
                            from = at + expression.len();
                        }
                        struck.push_str(&piece[from..]);
                        site.replace(&xml_attribute(piece), &xml_attribute(&struck))
                    })
                    .collect();
                if struck_sites
                    .iter()
                    .any(|struck| evaluates(&mut oracle, &varied(""), struck))
                {
                    shown = true;
                    break;
                }
            }
            if shown {
                counts.rejected_on_an_uncertain_value += 1;
                answered_wrongly("uncertain-value", grading.as_deref_mut());
                reach(&hostile, "msbuild-rejects-on-an-uncertain-value");
                continue;
            }
            // A text's expressions the walk does not model, on the values it
            // holds, struck from the site.
            // As written where the walk holds it as written, so that its
            // escapes are as at the site.
            let held_value = |name: &str, drawn: Option<&hostile::Drawn<String>>| match (
                drawn,
                parsed.properties.get(name),
            ) {
                (Some(drawn), Some(_)) if !drawn.value.contains("$(") => drawn.value.clone(),
                (_, Some(value)) => spelt(value),
                (_, None) => String::new(),
            };
            let held_values = property_map(&[
                (
                    "A".to_owned(),
                    held_value("A", Some(&read_at_site("A", &a))),
                ),
                (
                    "B".to_owned(),
                    held_value("B", Some(&read_at_site("B", &b))),
                ),
                ("U".to_owned(), held_value("U", Some(&held))),
                ("X".to_owned(), held_value("X", None)),
            ]);
            let unmodelled: Vec<String> = if template.contains("{t}") {
                substitute(&body, &held_values)
                    .1
                    .into_iter()
                    .filter_map(|issue| match issue {
                        Issue::Unsupported { expression } => Some(expression),
                        // One reading item metadata in a metadatum, which
                        // MSBuild hands the metadatum's value the walk does
                        // not hold; an operation reads it as written.
                        Issue::Throws { expression, .. }
                            if expression.contains("%(") && is_metadata_site(template) =>
                        {
                            Some(expression)
                        }
                        _ => None,
                    })
                    .collect()
            } else {
                Vec::new()
            };
            let mut struck = site.clone();
            for expression in &unmodelled {
                struck = struck.replace(&xml_attribute(expression), "s");
            }
            let shown = !unmodelled.is_empty()
                && std::iter::once(&"")
                    .chain(VARIED_VALUES)
                    .any(|value| evaluates(&mut oracle, &varied(value), &struck));
            // Or with the expressions on unsure names struck too, each set by
            // each value. Which of the two shows a rejection turns on the
            // values tried for those names, so both are one gap: a body the
            // walk does not model, perhaps beside an uncertain value.
            let shown_with_unsure = !shown
                && !unmodelled.is_empty()
                && strike_sets.iter().any(|set| {
                    STRUCK_AS.iter().any(|value| {
                        let both = set.iter().fold(struck.clone(), |site, expression| {
                            site.replace(&xml_attribute(expression), value)
                        });
                        both != struck && evaluates(&mut oracle, &varied(""), &both)
                    })
                });
            assert!(
                shown || shown_with_unsure,
                "certain-implies-exact violated: MSBuild rejects this project whatever the names \
                 the walk is not sure of hold, and the walk committed {ours:?}\n{}",
                describe()
            );
            counts.rejected_on_an_unmodelled_body += 1;
            strikes_seen.set(shown_with_unsure);
            answered_wrongly("unmodelled-body", grading);
            reach(&hostile, "msbuild-rejects-on-an-unmodelled-body");
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
            counts.committed += 1;
            assert_eq!(
                Some(value),
                theirs.get(*name),
                "certain-implies-exact violated for {name}\n{}",
                describe()
            );
        }
        let committed = ours.iter().any(|(name, _)| name.as_str() == "After");
        counts.evaluated_and_committed += usize::from(committed);
        counts.baseline_wrong_now_not += usize::from(baseline_wrong == Some(true));
        reach(&hostile, outcome(false, committed));
    }
    held_to(expected);
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff project_sweep_fixed_seed",
    );
    tally
}

/// [`project_sweep`] at a fixed seed, held to the baseline revision's answers
/// (`manifests/rejection_projects_baseline.txt`): no project the baseline
/// answered rightly, or withdrew, is one the walk under test answers wrongly.
/// Each project it answers wrongly (one MSBuild rejects over what the walk
/// does not judge yet) is pinned in `manifests/rejection_projects_wrong.txt`,
/// so that one closing, or opening, shows there.
#[test]
fn project_sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1009_0b5e_55ed);
    let mut grading = Grading {
        baseline: Baseline::load(),
        dump: std::env::var_os("BORZOI_REJECTION_DUMP").map(std::path::PathBuf::from),
        stale: Vec::new(),
        regressed: Vec::new(),
        wrong: Vec::new(),
    };
    let tally = project_sweep(&mut rng, 1_500, Some(&mut grading));
    eprintln!("rejection project sweep: {tally:?}");
    assert!(
        grading.stale.is_empty(),
        "the generated projects moved: {} of them have no record at the baseline revision; \
         regenerate it with `bash tools/rejection-baseline.sh {}` (or the branch's new merge \
         base with main): {:?}",
        grading.stale.len(),
        grading.baseline.revision,
        &grading.stale[..grading.stale.len().min(10)]
    );
    assert!(
        grading.regressed.is_empty(),
        "projects the baseline ({}) answered rightly, or withdrew, are answered wrongly now: {:?}",
        grading.baseline.revision,
        grading.regressed
    );
    // Anti-vacuity: MSBuild rejects and evaluates generated projects, the walk
    // claims rejections and allows them, and commits values beside them. How
    // many the baseline answered wrongly that the walk under test does not is
    // reported, not floored: a baseline recorded at an unchanged evaluator
    // has none.
    // What is counted is what is pinned: the drawn projects alone.
    assert_eq!(
        tally.rejected_on_an_uncertain_value + tally.rejected_on_an_unmodelled_body,
        grading.wrong.len(),
        "{tally:?}"
    );
    assert!(tally.msbuild_rejects >= 200, "{tally:?}");
    assert!(tally.certain >= 100, "{tally:?}");
    assert!(tally.possible >= 100, "{tally:?}");
    assert!(tally.evaluated_and_committed >= 200, "{tally:?}");
    let manifest = Manifest::from_keyed(grading.wrong).expect("well-formed entries");
    manifest::check(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/manifests/rejection_projects_wrong.txt"),
        &manifest,
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff project_sweep_fixed_seed\n\
         Gaps: `uncertain-value`, a throw on a value the walk does not hold (#1051); \
         `unmodelled-body`, a text the walk does not model (#1094), perhaps beside an \
         uncertain value: which of the two strikes shows such a rejection turns on the \
         values tried, so it is one gap.",
    );
}

/// Fresh-seed twin of [`project_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the rejection judgement"]
fn project_sweep_soak() {
    let (seed, cases) = soak_parameters("rejection project", 10_000);
    let mut rng = SplitMix64(seed);
    let tally = project_sweep(&mut rng, cases, None);
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
    /// model on certain values, where MSBuild threw on those values.
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
        let condition = condition(rng, &["A", "B", "U", "V"], 3);
        // Credited only for the names the condition reads: a value it never
        // reads reaches nothing.
        let reads = property_references(&condition);
        let hostile: BTreeSet<Dimension> = [("A", &a), ("B", &b)]
            .into_iter()
            .filter(|(name, _)| reads.iter().any(|read| read == name))
            .flat_map(|(_, drawn)| drawn.hostile.iter().copied())
            .collect();
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
        let held_of = |name: &str| {
            held.iter()
                .find(|(held_name, _)| held_name == name)
                .map(|(_, value)| value.as_str())
        };
        let (mut threw_on_held, mut held_value) = (false, false);
        for u in GRADED {
            for v in GRADED {
                let mut props = certain.clone();
                props.extend(u.map(|u| ("U".to_string(), u.to_string())));
                props.extend(v.map(|v| ("V".to_string(), v.to_string())));
                let is_held = *u == held_of("U") && *v == held_of("V");
                let evaluated = oracle.eval(&condition, &props);
                threw_on_held |= is_held && evaluated.is_none();
                match evaluated {
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
        // On the held values `on_held` judged, MSBuild threw: under that one
        // assignment, not any.
        tally.maybe_on_certain_values_threw +=
            usize::from(on_held.throws == Throws::Maybe && on_held.unevaluated && threw_on_held);
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
