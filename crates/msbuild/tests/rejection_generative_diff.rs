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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use borzoi_msbuild::test_support::{
    Issue, PropertyMap, Throws, judge, property_references, published_sites, second_walk_sites,
    substitute,
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
/// empty, a word, a number, a version, a boolean either way, a list, and the
/// hyphen a prerelease version joins with. Where MSBuild evaluates a project
/// with such an expression struck to one of them, its rejection rests on that
/// name's value, which the walk does not know (#1051).
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

/// The walk's reading of `writes`, the property writes before a site, and
/// of `site` where it is given: a site's condition reads the names before
/// the site, which may unsettle them after it; a text in the site reads them
/// after what the site writes before it.
fn read_before_site(
    project_path: &std::path::Path,
    writes: &str,
    site: Option<&str>,
) -> borzoi_msbuild::ParsedProject {
    let site = site.unwrap_or("");
    let xml = format!(
        "<Project>\n  <PropertyGroup>{writes}</PropertyGroup>\n  {ITEMS}\n  {site}\n</Project>\n"
    );
    std::fs::write(project_path, &xml).unwrap();
    parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(project_path, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed")
}

/// The generated names `parsed` holds no certain value of.
fn unsure_names(parsed: &borzoi_msbuild::ParsedProject) -> Vec<&'static str> {
    ["A", "B", "U", "X"]
        .into_iter()
        .filter(|name| !matches!(parsed.property(name), PropertyRead::Value(_)))
        .collect()
}

/// The names the attribution strikes are those the walk is not sure of at
/// the site, not after it: an import the walk cannot decide unsettles every
/// name read after it, `A` and `B` among them, though the site's condition
/// read them certain. Each name struck adds places to the bounded search over
/// assignments, and striking names the condition read certain can put the
/// one assignment that isolates a throw on an unsure name outside that bound.
#[test]
fn the_names_struck_are_those_unsure_at_the_site() {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(
        dir.join("there.props"),
        "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    let writes = format!(
        "<A>2.0</A><B>1.2.3</B><U></U><U Condition=\"{}\">\n</U>\
         <X>$([System.String]::Copy('Debug'))</X>",
        xml_attribute(UNDECIDED_TRUE)
    );
    assert_eq!(
        unsure_names(&read_before_site(&project_path, &writes, None)),
        ["U", "X"]
    );
    // Read after the import, as the final table is, every name is unsure.
    let xml = format!(
        "<Project>\n  <PropertyGroup>{writes}</PropertyGroup>\n  {ITEMS}\n  \
         <Import Project=\"there.props\" Condition=\"{}\" />\n</Project>\n",
        xml_attribute(UNDECIDED_TRUE)
    );
    std::fs::write(&project_path, &xml).unwrap();
    let after = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml).unwrap(),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed");
    assert_eq!(unsure_names(&after), ["A", "B", "U", "X"]);
}

/// `xml` with each line cut to a readable length: a long hostile value
/// otherwise buries the site a failure is about. `BORZOI_REJECTION_FULL`
/// set prints it whole, to reproduce a failure from.
fn elide(xml: &str) -> String {
    if std::env::var_os("BORZOI_REJECTION_FULL").is_some() {
        return xml.to_owned();
    }
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

/// Sites [`refused_history_sweep`] draws beside [`SITES`]: in an arm the walk
/// does not take, after a write of `A` there, a text under a gate MSBuild
/// evaluates first, of a metadatum, an update and a definition. A gate reading
/// a name the arm writes decides whether MSBuild reaches the text at all, in
/// any reading of the name (#1153). [`project_sweep`] draws [`SITES`] alone,
/// so its pinned projects do not move.
const HISTORY_SITES: &[&str] = &[
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>1</A></PropertyGroup><ItemGroup><I Include=\"x\"><M Condition=\"{c}\">{t}</M></I></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>1</A></PropertyGroup><ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"{c}\"><M>{t}</M></I></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>1</A></PropertyGroup><ItemDefinitionGroup><I Condition=\"{c}\"><M>{t}</M></I></ItemDefinitionGroup></When></Choose>",
    // A write in content the walk does not take of a value a function throws
    // on, beside writes of names a later group rewrites (to their first
    // values), each perhaps after a refused write of its name, and a text
    // there reading them all: which names the walk holds none of moves with
    // the history, and MSBuild's throw rests on the written value whatever
    // they hold (#1164). Read by the item pass, and by the property pass.
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>abc</A><B>abc</B><U>nope</U></PropertyGroup><ItemGroup><I Include=\"{t}\" /></ItemGroup></When></Choose><PropertyGroup>{refused:A}<A>{a}</A>{refused:B}<B>{b}</B></PropertyGroup>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>abc</A><B>abc</B><U>nope</U></PropertyGroup><ItemGroup><I Include=\"x\" Condition=\"{c}\" /></ItemGroup></When></Choose><PropertyGroup>{refused:A}<A>{a}</A>{refused:B}<B>{b}</B></PropertyGroup>",
    // The same, the text and the condition a version call over the three
    // names, some spliced together, and the rewrites version-shaped
    // ([`history_shape`]): the shape #1164 was found in.
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>abc</A><B>abc</B><U>nope</U></PropertyGroup><ItemGroup><I Include=\"{v}\" /></ItemGroup></When></Choose><PropertyGroup>{refused:A}<A>{va}</A>{refused:B}<B>{vb}</B></PropertyGroup>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><A>abc</A><B>abc</B><U>nope</U></PropertyGroup><ItemGroup><I Include=\"x\" Condition=\"{v}\" /></ItemGroup></When></Choose><PropertyGroup>{refused:A}<A>{va}</A>{refused:B}<B>{vb}</B></PropertyGroup>",
    "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><A>abc</A><U>nope</U><R>{t}</R></PropertyGroup><PropertyGroup>{refused:A}<A>{a}</A></PropertyGroup>",
    // A write gated on a name with a refused history, in content the walk
    // does not take, then a read of the written name: where MSBuild skips
    // the write, the read sees the name's earlier value (#1164's comments).
    "<PropertyGroup Condition=\"UNDECIDED_TRUE\"><B Condition=\"'$(A)' == 'off'\">abcdefghijkl</B><R>{t}</R></PropertyGroup>",
    "<Choose><When Condition=\"UNDECIDED_TRUE\"><PropertyGroup><B Condition=\"'$(A)' == 'off'\">abcdefghijkl</B></PropertyGroup><ItemGroup><I Include=\"{t}\" /></ItemGroup></When></Choose>",
];

/// The names a [`HISTORY_SITES`] template may rewrite after its arm, each
/// perhaps after a refused write (`{refused:A}` before `<A>{a}</A>`).
const IN_SITE_REWRITES: [&str; 2] = ["A", "B"];

/// What [`history_shape`] draws a rewrite's value from: versions with and
/// without the `v` MSBuild accepts, empty, and words no splice makes one.
const VERSION_SHAPED: &[&str] = &["", "v1.0", "1.0", "1", "2.0.1", "abc", "v"];

/// What [`refused_history_sweep`]'s draws of [`history_shape`] are seeded
/// with, beside the sweep's own seed: a stream of their own, so that the
/// projects without a `{v}` are the ones drawn before it was.
const SHAPE_STREAM: u64 = 0x1164_5ba9_e000;

/// A [`HISTORY_SITES`] template's `{v}`, `{va}` and `{vb}`, as
/// (placeholder, text) pairs: a version function of `A`, `B` and `U`, each
/// argument one name or two spliced, and version-shaped values of the
/// rewrites of `A` and `B`. Where a splice of two names parses as a version
/// on some of their values and not others, which names MSBuild's throw rests
/// on turns on the values tried for the names the walk holds none of.
fn history_shape(rng: &mut SplitMix64) -> [(&'static str, String); 3] {
    let names = ["A", "B", "U"];
    let argument = |rng: &mut SplitMix64| {
        let first = *rng.pick(&names);
        if rng.below(2) == 0 {
            format!("$({first})")
        } else {
            format!("$({first})$({})", rng.pick(&names))
        }
    };
    let function = *rng.pick(&["VersionLessThan", "VersionGreaterThan", "VersionEquals"]);
    let (left, right) = (argument(rng), argument(rng));
    [
        (
            "{v}",
            format!("$([MSBuild]::{function}('{left}','{right}'))"),
        ),
        ("{va}", (*rng.pick(VERSION_SHAPED)).to_owned()),
        ("{vb}", (*rng.pick(VERSION_SHAPED)).to_owned()),
    ]
}

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
    /// Of the projects whose rewrite follows a refused write of its name
    /// ([`REFUSED_BEFORE_REWRITE`]): those MSBuild rejects that the walk
    /// withdraws, and those MSBuild evaluates whose every value the walk
    /// commits.
    refused_rewrite_withdrawn: usize,
    refused_rewrite_committed: usize,
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

/// The hostile values [`refused_history_sweep`] does not draw, nor its census
/// credit:
/// [`PROJECT_EXCLUDED`]'s, and the overwritten-later dimension, which is
/// hostile only to a read between the write and its reset. Which reads
/// MSBuild makes, a walk-only comparison of a twin with its project does not
/// observe; [`project_sweep`] credits it against MSBuild.
const HISTORY_EXCLUDED: &[(Dimension, &str)] = &[
    PROJECT_EXCLUDED[0],
    (
        Dimension::OverwrittenLater,
        "hostile only to a read between the write and its reset, and a walk-only comparison of \
         a twin with its project does not observe which reads MSBuild makes",
    ),
];

/// The body of `X`, a write the walk refuses to compute (a function it does
/// not model), so that it holds no value of `X`; MSBuild holds `Debug`, and
/// throws on nothing.
const REFUSED: &str = "$([System.String]::Copy('Debug'))";

/// A write of a name with [`REFUSED`] just before one of its clean writes: a
/// write history MSBuild does not see (it computes the refused body, which
/// throws on nothing, and the clean write overwrites it), and the walk keeps
/// a mark of after the clean write (`Trust::refused`), though it holds the
/// clean value as MSBuild does (#1153).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefusedBefore {
    /// No such write.
    Nothing,
    /// Before the first write of `A` or `B`.
    FirstWrite(&'static str),
    /// Before the rewrite after the site, whose value the item pass reads.
    Rewrite,
    /// Before a rewrite of `A` or `B` the site itself makes, after the arm it
    /// writes in ([`HISTORY_SITES`]' `{refused:A}` and `{refused:B}`).
    InSite(&'static str),
}

/// Which history [`project_sweep`] draws for a project with a rewrite: the
/// one whose value the item pass reads after it. Drawn from a stream of its
/// own ([`HISTORY_STREAM`]), so that a project without it is the one the
/// generator drew before the axis was.
const REFUSED_BEFORE_REWRITE: &[RefusedBefore] = &[RefusedBefore::Nothing, RefusedBefore::Rewrite];

/// What [`project_sweep`]'s draws of [`REFUSED_BEFORE_REWRITE`] are seeded
/// with, beside the sweep's own seed.
const HISTORY_STREAM: u64 = 0x1153_4157_0b1e;

/// A drawn project as text: the site, the writes before it (the first
/// group's), the resets of values overwritten later, the writes after the
/// site, and the whole document.
struct Rendered {
    site: String,
    writes: String,
    resets: String,
    later: String,
    xml: String,
}

/// The writes after the site: `resets`, then the rewrite of `rewrite`, its
/// body `body` as given, after a refused write of its name where
/// `refused_before_rewrite` says.
fn writes_after_site(
    resets: &str,
    rewrite: Option<&str>,
    refused_before_rewrite: bool,
    body: &str,
) -> String {
    match rewrite {
        Some(name) if refused_before_rewrite => {
            format!("{resets}<{name}>{REFUSED}</{name}><{name}>{body}</{name}>")
        }
        Some(name) => format!("{resets}<{name}>{body}</{name}>"),
        None => resets.to_owned(),
    }
}

/// The project: its first group's `writes`, the items, the `site`, and the
/// group after it, holding `later`.
fn document_text(writes: &str, later: &str, site: &str) -> String {
    format!(
        "<Project>\n  <PropertyGroup>{writes}</PropertyGroup>\n  {ITEMS}\n  {site}\n  \
         <PropertyGroup><After>ok</After>{later}</PropertyGroup>\n</Project>\n"
    )
}

/// `drawing` as text, with the refused writes `refused` names.
fn render(drawing: &Drawing, refused: &[RefusedBefore]) -> Rendered {
    let mut site = drawing
        .template
        .replace("{c}", &xml_attribute(&drawing.gate))
        .replace("{t}", &xml_attribute(&drawing.body))
        .replace("UNDECIDED_TRUE", &xml_attribute(UNDECIDED_TRUE))
        .replace("UNDECIDED_FALSE", &xml_attribute(UNDECIDED_FALSE))
        .replace("{a}", &xml_text(&drawing.a.value))
        .replace("{b}", &xml_text(&drawing.b.value));
    for name in IN_SITE_REWRITES {
        let refused_write = if refused.contains(&RefusedBefore::InSite(name)) {
            format!("<{name}>{REFUSED}</{name}>")
        } else {
            String::new()
        };
        site = site.replace(&format!("{{refused:{name}}}"), &refused_write);
    }
    // A value overwritten later has been read by the site in between.
    let mut resets = String::new();
    for (name, drawn) in [("A", &drawing.a), ("B", &drawing.b)] {
        if drawn.hostile.contains(&Dimension::OverwrittenLater) {
            resets.push_str(&format!("<{name}>{RESET}</{name}>"));
        }
    }
    let later = writes_after_site(
        &resets,
        drawing.rewrite,
        refused.contains(&RefusedBefore::Rewrite),
        &xml_text(&drawing.rewritten.value),
    );
    // The first group's writes as given: `U` as the walk holds it, then
    // (`real`) as MSBuild holds it, which the walk cannot know.
    let first_write = |name: &'static str, drawn: &hostile::Drawn<String>| {
        let refused_write = if refused.contains(&RefusedBefore::FirstWrite(name)) {
            format!("<{name}>{REFUSED}</{name}>")
        } else {
            String::new()
        };
        format!("{refused_write}<{name}>{}</{name}>", xml_text(&drawn.value))
    };
    let writes = format!(
        "{}{}<U>{}</U><U Condition=\"{}\">{}</U><X>{REFUSED}</X>",
        first_write("A", &drawing.a),
        first_write("B", &drawing.b),
        xml_text(&drawing.held.value),
        xml_attribute(UNDECIDED_TRUE),
        xml_text(&drawing.real.value),
    );
    let xml = document_text(&writes, &later, &site);
    Rendered {
        site,
        writes,
        resets,
        later,
        xml,
    }
}

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

/// A project drawn from `rng`, at one of `sites`, or `None` where a value it
/// drew carries an `excluded` dimension, before it draws the pieces.
fn draw_project(
    rng: &mut SplitMix64,
    excluded: &BTreeSet<Dimension>,
    sites: &[&'static str],
) -> Option<Drawing> {
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
    let template = *rng.pick(sites);
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
    // The first gap, at an import the walk cannot decide, after which every
    // name is unsure though only `U` and `X` are at the site: the rejection
    // on `X`'s value shows by striking `$(X.Substring(2))` alone, out of reach
    // of the bounded assignments over every name's expressions (soak seed
    // 1795204238191503702).
    Witness {
        values: ["2.0", "1.2.3", "", "\n"],
        template: "<Import Project=\"there.props\" Condition=\"{c}\" />",
        body: "",
        gate: "((('$([MSBuild]::VersionLessThan($(A).0, 2.0))' And $([System.String]::IsNullOrWhiteSpace('\u{a0}')) And $(B) <= '$([System.String]::IsNullOrEmpty(null))') And (HasTrailingSlash('x$([System.String]::IsNullOrWhiteSpace(\"\u{a0}\"))') Or true Or '$(B.Split(\";\")[1].Length)') And $([System.String]::IsNullOrWhiteSpace('\u{a0}'))) Or '$(X.Substring(2))' Or $([MSBuild]::VersionLessThan(`$(A)`, `2.0`)))",
        gap: "uncertain-value",
        both_strikes: false,
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
    let mut histories = SplitMix64(rng.0 ^ HISTORY_STREAM);
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
            None if tally.cases < cases => match draw_project(rng, &excluded, SITES) {
                Some(drawing) => (drawing, None),
                None => continue,
            },
            None => break,
        };
        let refused = match (witness, drawing.rewrite) {
            (None, Some(_)) => *histories.pick(REFUSED_BEFORE_REWRITE),
            _ => RefusedBefore::Nothing,
        };
        let Rendered {
            site,
            writes,
            resets,
            later,
            xml,
        } = render(&drawing, &[refused]);
        let refused_rewrite = refused == RefusedBefore::Rewrite;
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
        // The writes after the site, a rewrite's body as given.
        let after_site =
            |rewrite_body: &str| writes_after_site(&resets, rewrite, refused_rewrite, rewrite_body);
        let document =
            |(writes, later): &(String, String), site: &str| document_text(writes, later, site);
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
                // A rejection the property pass makes before the rewrite is
                // none of its history's.
                counts.refused_rewrite_withdrawn +=
                    usize::from(refused_rewrite && rewrite_is_graded(item_pass, false));
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
            // name's plain value back: the property pass's. A site's own
            // condition is read before anything the site writes or imports
            // (an import the walk cannot decide unsettles every name after
            // it); a text, after what the site writes before it. The item
            // pass reads the final table.
            let at_site = if item_pass {
                None
            } else if template.contains("{c}") {
                Some(read_before_site(&project_path, &writes, None))
            } else if later.is_empty() {
                None
            } else {
                Some(read_before_site(&project_path, &writes, Some(&site)))
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
            let unsure_names = unsure_names(parsed);
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
        // A commit of the refused history is one of the rewritten name.
        let rewritten_read =
            rewrite.is_some_and(|name| ours.iter().any(|(n, _)| n.as_str() == name));
        counts.refused_rewrite_committed +=
            usize::from(committed && refused_rewrite && rewritten_read);
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
    // The refused-then-rewritten history reaches both outcomes.
    assert!(tally.refused_rewrite_withdrawn > 0, "{tally:?}");
    assert!(tally.refused_rewrite_committed > 0, "{tally:?}");
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

/// What [`refused_history_sweep`] compared.
#[derive(Debug, Default)]
struct HistoryCensus {
    /// Twins compared with their project, by where a refused write went, and
    /// those with more than one.
    first_write: usize,
    rewrite: usize,
    in_site: usize,
    several: usize,
    /// Pairs of twins compared, the refused writes of one among the other's.
    twin_pairs: usize,
    /// Of the twins compared, those whose project the walk withdraws, and
    /// those whose project it commits a value of.
    withdrawn: usize,
    committed: usize,
    /// Sites a twin's walk adopted from its second walk, and of them those
    /// whose cause the project's walk does not note anywhere: the two
    /// documents' spans differ by the refused write, so causes are what the
    /// census compares, and a cause the project notes at another construct
    /// counts as found.
    second_walk_sites: usize,
    second_walk_causes_beyond_project: usize,
}

/// [`RefusedBefore`]'s claim, held to the walk alone. A refused write just
/// before a clean write of the same name changes nothing MSBuild does, so the
/// walk may withdraw more for a project's twin with such writes (the mark it
/// keeps of a refusal is a doubt), never less: where it claims MSBuild may
/// reject the project, it claims so of the twin, and every value it commits of
/// the twin it commits, the same, of the project. A twin it judges more kindly
/// is one whose rejection site it lost to the history (#1153). Each twin holds
/// a non-empty set of the refused writes the project admits, so histories on
/// several names are held too. No oracle is asked, so it covers far more
/// drawn projects than [`project_sweep`] can.
///
/// So are two twins, where one's refused writes are among the other's: the
/// one with more is no more certain, and withdrawn wherever the other is.
/// A judgement that tried values for the names the walk holds none of
/// answered two such twins in no order (#1164).
///
/// A write whose body reads its own name is passed over: there the refused
/// write's value is MSBuild's input, not history.
///
/// The other way, it counts the sites the twin's walk adopts from its second
/// walk, which holds a refused-then-rebound name certain
/// (`test_support::second_walk_sites`), that the project's walk does not
/// find. The project holds the same values, unmarked, but the walk's own
/// course doubts a refused name in a gate around the site, as on main, so the
/// second walk may judge content MSBuild does not reach: a decline, which
/// [`refused_history_sweep_fixed_seed`] pins by count. Its drawn sites are
/// [`SITES`] and [`HISTORY_SITES`].
fn refused_history_sweep(rng: &mut SplitMix64, cases: usize) -> HistoryCensus {
    let excluded: BTreeSet<Dimension> = HISTORY_EXCLUDED.iter().map(|(d, _)| *d).collect();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(
        dir.join("there.props"),
        "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    // Both sides walk under one fixed environment, and no oracle is asked, so
    // the host's SDK is never probed.
    let environment = HashMap::new();
    let walk = |xml: &str| {
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &environment,
            None,
            None,
        )
        .expect("well-formed")
    };
    let census = coverage::open(
        "crates/msbuild/tests/rejection_generative_diff.rs",
        "refused_history",
        HISTORY_EXCLUDED,
    );
    let names = ["A", "B", "U", "X", "R", "After", "Delta"];
    let sites: Vec<&'static str> = SITES.iter().chain(HISTORY_SITES).copied().collect();
    let mut tally = HistoryCensus::default();
    let mut shapes = SplitMix64(rng.0 ^ SHAPE_STREAM);
    let mut drawn = 0;
    while drawn < cases {
        let Some(drawing) = draw_project(rng, &excluded, &sites) else {
            continue;
        };
        drawn += 1;
        let reads_itself = |name: &str, value: &str| property_references(value).contains(&name);
        let mut eligible = Vec::new();
        for (name, value) in [("A", &drawing.a.value), ("B", &drawing.b.value)] {
            if !reads_itself(name, value) {
                eligible.push(RefusedBefore::FirstWrite(name));
            }
        }
        if let Some(name) = drawing.rewrite
            && !reads_itself(name, &drawing.rewritten.value)
        {
            eligible.push(RefusedBefore::Rewrite);
        }
        for (name, value) in [("A", &drawing.a.value), ("B", &drawing.b.value)] {
            // A `{v}` site rewrites to a version-shaped value of its own.
            if drawing.template.contains(&format!("{{refused:{name}}}"))
                && (drawing.template.contains("{v}") || !reads_itself(name, value))
            {
                eligible.push(RefusedBefore::InSite(name));
            }
        }
        let twins = (1..1usize << eligible.len()).map(|mask| {
            eligible
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask & (1 << bit) != 0)
                .map(|(_, refused)| *refused)
                .collect::<Vec<_>>()
        });
        // A `{v}` site's call and rewrites, drawn once for the project and
        // its twins.
        let shape = drawing
            .template
            .contains("{v}")
            .then(|| history_shape(&mut shapes));
        let render = |drawing: &Drawing, refused: &[RefusedBefore]| {
            let mut rendered = render(drawing, refused);
            for (placeholder, text) in shape.iter().flatten() {
                rendered.xml = rendered.xml.replace(placeholder, &xml_attribute(text));
            }
            rendered
        };
        let plain = render(&drawing, &[]);
        let (ours, ours_published) = published_sites(|| walk(&plain.xml));
        // Every twin walked, for the comparison of two twins below.
        let mut walked: Vec<(Vec<RefusedBefore>, String, borzoi_msbuild::ParsedProject)> =
            Vec::new();
        for refused in twins {
            let twin = render(&drawing, &refused);
            let ((theirs, second_sites), theirs_published) =
                published_sites(|| second_walk_sites(|| walk(&twin.xml)));
            if refused.contains(&RefusedBefore::Rewrite) {
                tally.rewrite += 1;
            }
            if refused.len() > 1 {
                tally.several += 1;
            }
            if refused
                .iter()
                .any(|r| matches!(r, RefusedBefore::FirstWrite(_)))
            {
                tally.first_write += 1;
            }
            if refused
                .iter()
                .any(|r| matches!(r, RefusedBefore::InSite(_)))
            {
                tally.in_site += 1;
            }
            let describe = || {
                format!(
                    "--- project ---\n{}\n{:#?}\n--- twin ({refused:?}) ---\n{}\n{:#?}",
                    elide(&plain.xml),
                    ours.rejection,
                    elide(&twin.xml),
                    theirs.rejection
                )
            };
            let certainty = |parsed: &borzoi_msbuild::ParsedProject| {
                parsed.rejection.as_ref().map(|r| r.certainty)
            };
            // A site the twin's walk adopts from its second walk that the
            // project's walk does not find is a decline the walk's own course
            // costs.
            let project_sites: Vec<&borzoi_msbuild::RejectionCause> = ours
                .diagnostics
                .iter()
                .filter_map(|d| match &d.kind {
                    borzoi_msbuild::DiagnosticKind::Rejected { cause }
                    | borzoi_msbuild::DiagnosticKind::MayBeRejected { cause } => Some(cause),
                    _ => None,
                })
                .collect();
            for published in [&ours_published, &theirs_published] {
                assert_no_site_twice(published, &describe);
            }
            for site in &second_sites {
                tally.second_walk_sites += 1;
                if !project_sites.contains(&&site.cause) {
                    tally.second_walk_causes_beyond_project += 1;
                }
            }
            assert!(
                twin_verdict_claims_no_more(certainty(&ours), certainty(&theirs)),
                "the walk judges a project {:?} and its twin with a refused write before a clean \
                 one, which MSBuild evaluates alike, {:?}\n{}",
                certainty(&ours),
                certainty(&theirs),
                describe()
            );
            for name in names {
                assert!(
                    twin_claims_no_more(&ours.property(name), &theirs.property(name)),
                    "the walk reads {name} of the twin with a refused write before a clean one \
                     exactly as {:?}, and of the project as {:?}\n{}",
                    theirs.property(name),
                    ours.property(name),
                    describe()
                );
            }
            let mut carried: BTreeSet<Dimension> = BTreeSet::new();
            for drawn in [&drawing.a, &drawing.b, &drawing.held, &drawing.real] {
                carried.extend(drawn.hostile.iter().copied());
            }
            if drawing.rewrite.is_some() {
                carried.extend(drawing.rewritten.hostile.iter().copied());
            }
            census.reached(
                &carried,
                if ours.rejection.is_some() {
                    "withdraw"
                } else {
                    "commit"
                },
            );
            if ours.rejection.is_some() {
                tally.withdrawn += 1;
            } else if names
                .iter()
                .any(|name| matches!(ours.property(name), PropertyRead::Value(_)))
            {
                tally.committed += 1;
            }
            walked.push((refused, twin.xml, theirs));
        }
        // Two twins whose refused writes are ordered by inclusion: the one
        // with more is held to the other as a twin is to its project. Each
        // refused write only adds a doubt, so the walk's judgement may not
        // withdraw less, nor claim more, for the twin with more of them.
        for (fewer, fewer_xml, fewer_parsed) in &walked {
            for (more, more_xml, more_parsed) in &walked {
                if more.len() <= fewer.len() || !fewer.iter().all(|r| more.contains(r)) {
                    continue;
                }
                tally.twin_pairs += 1;
                let describe = || {
                    format!(
                        "--- twin ({fewer:?}) ---\n{}\n{:#?}\n--- twin ({more:?}) ---\n{}\n{:#?}",
                        elide(fewer_xml),
                        fewer_parsed.rejection,
                        elide(more_xml),
                        more_parsed.rejection
                    )
                };
                let certainty = |parsed: &borzoi_msbuild::ParsedProject| {
                    parsed.rejection.as_ref().map(|r| r.certainty)
                };
                assert!(
                    twin_verdict_claims_no_more(certainty(fewer_parsed), certainty(more_parsed)),
                    "the walk judges a twin {:?} and a twin with more refused writes before clean \
                     ones, which MSBuild evaluates alike, {:?}\n{}",
                    certainty(fewer_parsed),
                    certainty(more_parsed),
                    describe()
                );
                for name in names {
                    assert!(
                        twin_claims_no_more(
                            &fewer_parsed.property(name),
                            &more_parsed.property(name)
                        ),
                        "the walk reads {name} of the twin with more refused writes exactly as \
                         {:?}, and of the one with fewer as {:?}\n{}",
                        more_parsed.property(name),
                        fewer_parsed.property(name),
                        describe()
                    );
                }
            }
        }
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff refused_history_sweep_fixed_seed",
    );
    tally
}

/// Whether the twin's verdict, `twin`, claims nothing the project's,
/// `project`, does not, MSBuild evaluating the two alike: a withdrawal of
/// the project is one of the twin, and a certain rejection of the twin, an
/// exact claim, is one of the project.
fn twin_verdict_claims_no_more(
    project: Option<RejectionCertainty>,
    twin: Option<RejectionCertainty>,
) -> bool {
    match (project, twin) {
        (Some(_), None) => false,
        (project, Some(RejectionCertainty::Certain)) => {
            project == Some(RejectionCertainty::Certain)
        }
        _ => true,
    }
}

#[test]
fn a_twin_is_withdrawn_with_its_project_and_certain_only_with_it() {
    use RejectionCertainty::{Certain, Possible};
    for (project, twin, claims_no_more) in [
        (None, None, true),
        (None, Some(Possible), true),
        (None, Some(Certain), false),
        (Some(Possible), None, false),
        (Some(Possible), Some(Possible), true),
        (Some(Possible), Some(Certain), false),
        (Some(Certain), None, false),
        (Some(Certain), Some(Possible), true),
        (Some(Certain), Some(Certain), true),
    ] {
        assert_eq!(
            twin_verdict_claims_no_more(project, twin),
            claims_no_more,
            "{project:?} {twin:?}"
        );
    }
}

/// Whether the twin's read of a name, `twin`, claims nothing the project's,
/// `project`, does not: it is no exact read ([`PropertyRead::is_exact`], a
/// value or an absence MSBuild shares), or it is the project's read.
fn twin_claims_no_more(project: &PropertyRead, twin: &PropertyRead) -> bool {
    !twin.is_exact() || project == twin
}

#[test]
fn a_twin_claims_an_absence_as_it_claims_a_value() {
    let value = |v: &str| PropertyRead::Value(v.to_owned());
    let inexact = PropertyRead::UnsetInexact(borzoi_msbuild::InexactUnset::Refused);
    assert!(twin_claims_no_more(&value("x"), &value("x")));
    assert!(twin_claims_no_more(
        &PropertyRead::Unset,
        &PropertyRead::Unset
    ));
    assert!(twin_claims_no_more(&value("x"), &inexact));
    assert!(!twin_claims_no_more(&value("x"), &value("y")));
    assert!(!twin_claims_no_more(&value("x"), &PropertyRead::Unset));
    assert!(!twin_claims_no_more(&inexact, &PropertyRead::Unset));
    assert!(!twin_claims_no_more(&PropertyRead::Unset, &value("")));
}

/// Where a reach-grid case writes `P` before its arm and after it: the
/// refused write of the twin goes just before the write that settles `P`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HistoryAt {
    /// `P` is `abc` before the `<Choose>` and rewritten to the final value
    /// after it, the refused write just before the rewrite: the arm's gate
    /// reads `abc`.
    AfterTheChoose,
    /// `P` is written its final value before the `<Choose>`, the refused write
    /// just before that, and not after: the arm's gate reads the final value,
    /// and the arm's own write, where MSBuild takes it, is `P`'s last.
    BeforeTheChoose,
}

/// The grid cells where a walk commits a value MSBuild does not hold, each
/// with which walks do and how ([`wrong_commits`]'s spelling), and the gap it
/// is: a gated item definition's throw on a final value (#1172), or a throw
/// on the value of the arm's own write, where the value the walk holds does
/// not throw (#1051).
/// Pinned by [`refused_history_reach_grid`]'s label and compared exactly, so
/// that one closing, another opening, or a cell moving from one walk or kind
/// to another fails it; none is the history's.
const BOTH_COMMIT_ON_REJECTED: &str =
    "project: commits on a project MSBuild rejects; twin: commits on a project MSBuild rejects";

const REACH_GRID_KNOWN_WRONG: &[(&str, &str, &str)] = &[
    (
        "AfterTheChoose / '$(P)' == 'abc' / <ItemDefinitionGroup Condition=\"'$(P)' == 'z'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / '$(P)' == 'abc' / <ItemDefinitionGroup Condition=\"'$(P)' == 'z'\"><I><M>$(P[9])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / '$(P)' == 'abc' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'z'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / '$(P)' == 'abc' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'z'\"><M>$(P[9])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' == 'z'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' == 'z'\"><I><M>$(P[9])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'z'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "AfterTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'z'\"><M>$(P[9])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / '$(P)' == 'z' / <ItemDefinitionGroup Condition=\"'$(P)' != 'z'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / '$(P)' == 'z' / <ItemDefinitionGroup Condition=\"'$(P)' == 'abcdefghijkl'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / '$(P)' == 'z' / <ItemDefinitionGroup><I Condition=\"'$(P)' != 'z'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / '$(P)' == 'z' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'abcdefghijkl'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' != 'z'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' != 'z'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' == 'abcdefghijkl'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup Condition=\"'$(P)' == 'abcdefghijkl'\"><I><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' != 'z'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' != 'z'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'abcdefghijkl'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemDefinitionGroup><I Condition=\"'$(P)' == 'abcdefghijkl'\"><M>$(P.Split(';')[3])</M></I></ItemDefinitionGroup> / z",
        BOTH_COMMIT_ON_REJECTED,
        "#1172",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"'$(P)' != 'z'\"><M>$(P.Split(';')[3])</M></I></ItemGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1051",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"'$(P)' == 'abcdefghijkl'\"><M>$(P.Split(';')[3])</M></I></ItemGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1051",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemGroup><I Include=\"x\"><M Condition=\"'$(P)' != 'z'\">$(P.Split(';')[3])</M></I></ItemGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1051",
    ),
    (
        "BeforeTheChoose / 'É' == 'é' / <ItemGroup><I Include=\"x\"><M Condition=\"'$(P)' == 'abcdefghijkl'\">$(P.Split(';')[3])</M></I></ItemGroup> / abcdefghijklmn;b;c;d",
        BOTH_COMMIT_ON_REJECTED,
        "#1051",
    ),
];

/// The reach of a site from an arm the walk does not take, in the second walk
/// of a refused-then-rebound name (#1153): every container a gate decides
/// MSBuild's reach of a text in (a metadatum, an update, a definition, a
/// definition group, a condition's short-circuit), every gate on `P` true on
/// the arm's value or the final one, every throw on `P`, every final value,
/// and the arm's own gate (one the walk cannot decide, or one on `P`, false
/// or true on what it reads) with the history before or after the
/// `<Choose>` ([`HistoryAt`]), each walked as is and with a refused write of
/// `P` before the write that settles it. The two projects hold the same
/// values, and MSBuild evaluates them alike, so per case:
///
/// - where MSBuild evaluates the twin, neither walk's rejection is Certain;
/// - a value either walk commits is MSBuild's, but in the cells of
///   [`REACH_GRID_KNOWN_WRONG`], which pins which walk is wrong and how, and
///   nowhere else;
/// - per cell, `manifests/rejection_reach_grid_declines.txt` pins whether the
///   twin's walk adopts a site from its second walk whose cause the project's
///   walk notes nowhere (the documents' spans differ, so causes are
///   compared), and whether, where MSBuild evaluates the twin and the
///   project's walk commits, the twin's walk is withdrawn by its second walk's
///   sites alone (every site it publishes adopted). Each walk decides reach
///   with the walk's own code, which
///   doubts a refused name in the arm's gate, so the second walk may find a
///   site in an arm MSBuild does not take. Such a site is Possible, a decline,
///   and the manifest is its cost. It pins too which walks withdraw a project
///   MSBuild evaluates: each judges a name the arm writes on the value it
///   holds from before the arm (#1164), so it may withdraw where MSBuild,
///   holding the arm's value, evaluates the project (#1200).
#[test]
fn refused_history_reach_grid() {
    const CONTAINERS: &[&str] = &[
        "<ItemGroup><I Include=\"x\"><M Condition=\"{g}\">{t}</M></I></ItemGroup>",
        "<ItemGroup><I Include=\"x\" /><I Update=\"x\" Condition=\"{g}\"><M>{t}</M></I></ItemGroup>",
        "<ItemDefinitionGroup><I Condition=\"{g}\"><M>{t}</M></I></ItemDefinitionGroup>",
        "<ItemDefinitionGroup Condition=\"{g}\"><I><M>{t}</M></I></ItemDefinitionGroup>",
        "<ItemGroup Condition=\"{g} And '{t}' != ''\"><I Include=\"x\" /></ItemGroup>",
        "<ItemGroup Condition=\"!({g}) Or '{t}' != ''\"><I Include=\"x\" /></ItemGroup>",
    ];
    const GATES: &[&str] = &["'$(P)' == 'abcdefghijkl'", "'$(P)' == 'z'", "'$(P)' != 'z'"];
    const THROWS: &[&str] = &["$(P[9])", "$(P.Split(';')[3])"];
    const FINALS: &[&str] = &["z", "abcdefghijklmn;b;c;d"];
    // The arm's own gate: one the walk cannot decide, ones on `P`, false and
    // true on `z` and on `abc`, and one whose second operand throws on a
    // short `P`, which a walk doubting `P` judges a site, and so leaves the
    // `<Choose>` undecided, where one holding `P` short-circuits: the walks'
    // courses part.
    const ARMS: &[&str] = &[
        UNDECIDED_TRUE,
        "'$(P)' == 'off'",
        "'$(P)' == 'z'",
        "'$(P)' == 'abc'",
        "'$(P)' == 'off' And '$(P[12])' != ''",
    ];
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let names = ["P", "After"];
    let oracle_names: Vec<String> = names.map(String::from).to_vec();
    let environment = HashMap::new();
    let walk = |xml: &str| {
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &environment,
            None,
            None,
        )
        .expect("well-formed")
    };
    let sites_of = |parsed: &borzoi_msbuild::ParsedProject| -> Vec<borzoi_msbuild::RejectionCause> {
        parsed
            .diagnostics
            .iter()
            .filter_map(|d| match &d.kind {
                borzoi_msbuild::DiagnosticKind::Rejected { cause }
                | borzoi_msbuild::DiagnosticKind::MayBeRejected { cause } => Some(cause.clone()),
                _ => None,
            })
            .collect()
    };
    let mut oracle = Oracle::spawn();
    let (mut cases, mut second, mut must_commit) = (0, 0, 0);
    let mut failures = Vec::new();
    let mut wrong: BTreeMap<String, String> = BTreeMap::new();
    let mut declines = Vec::new();
    for at in [HistoryAt::AfterTheChoose, HistoryAt::BeforeTheChoose] {
        for arm in ARMS {
            for container in CONTAINERS {
                for gate in GATES {
                    for throw in THROWS {
                        for last in FINALS {
                            let site = container
                                .replace("{g}", &xml_attribute(gate))
                                .replace("{t}", &xml_attribute(throw));
                            let document = |refused: &str| {
                                let (before, after) = match at {
                                    HistoryAt::AfterTheChoose => {
                                        ("<P>abc</P>".to_owned(), format!("{refused}<P>{last}</P>"))
                                    }
                                    HistoryAt::BeforeTheChoose => {
                                        (format!("{refused}<P>{last}</P>"), String::new())
                                    }
                                };
                                format!(
                                    "<Project>\n  <PropertyGroup>{before}</PropertyGroup>\n  \
                                     <ItemGroup><J Include=\"1.0\" /></ItemGroup>\n  \
                                     <Choose><When Condition=\"{}\"><PropertyGroup><P>abcdefghijkl</P></PropertyGroup>{site}</When></Choose>\n  \
                                     <PropertyGroup><After>ok</After>{after}</PropertyGroup>\n</Project>\n",
                                    xml_attribute(arm)
                                )
                            };
                            let plain_xml = document("");
                            let twin_xml = document(&format!("<P>{REFUSED}</P>"));
                            let (plain, plain_published) = published_sites(|| walk(&plain_xml));
                            let ((twin, second_sites), twin_published) =
                                published_sites(|| second_walk_sites(|| walk(&twin_xml)));
                            for published in [&plain_published, &twin_published] {
                                assert_no_site_twice(published, &|| twin_xml.clone());
                            }
                            cases += 1;
                            second += second_sites.len();
                            let label = format!("{at:?} / {arm} / {site} / {last}");
                            let plain_sites = sites_of(&plain);
                            // The two documents' spans differ by the refused
                            // write, so the comparison is by cause.
                            if second_sites
                                .iter()
                                .any(|found| !plain_sites.contains(&found.cause))
                            {
                                declines.push((
                                    label.clone(),
                                    "adopts a cause the project's walk does not note".to_owned(),
                                ));
                            }
                            std::fs::write(&project_path, &twin_xml).unwrap();
                            let theirs = oracle.project_design_time(
                                &twin_xml,
                                &oracle_names,
                                Some(&project_path),
                                &[],
                            );
                            if theirs.is_some() {
                                for (which, parsed) in [("twin", &twin), ("project", &plain)] {
                                    if parsed
                                        .rejection
                                        .as_ref()
                                        .is_some_and(|r| r.certainty == RejectionCertainty::Certain)
                                    {
                                        failures.push(format!(
                                            "{label}: MSBuild evaluates the project, and the \
                                             {which}'s walk claims it rejects it: {:?}",
                                            parsed.rejection
                                        ));
                                    }
                                }
                            }
                            if theirs.is_some() {
                                for (which, parsed) in [("project", &plain), ("twin", &twin)] {
                                    if parsed.rejection.is_some() {
                                        declines.push((
                                            label.clone(),
                                            format!(
                                                "{which}: withdraws a project MSBuild evaluates"
                                            ),
                                        ));
                                    }
                                }
                            }
                            if theirs.is_some() && plain.rejection.is_none() {
                                must_commit += 1;
                                // Every site the twin publishes is one it
                                // adopted: within one evaluation, adoption is
                                // recorded per diagnostic.
                                if twin.rejection.is_some()
                                    && sites_of(&twin).len() == second_sites.len()
                                {
                                    declines.push((
                                        label.clone(),
                                        "withdrawn by the second walk alone".to_owned(),
                                    ));
                                }
                            }
                            let verdict = wrong_commits(
                                [("project", &plain), ("twin", &twin)],
                                theirs.as_ref(),
                                &names,
                            );
                            if !verdict.is_empty() {
                                wrong.insert(label, verdict);
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!(
        "refused history reach grid: {cases} cases, {second} second-walk sites, {must_commit} \
         must-commit points, {} decline verdicts",
        declines.len()
    );
    let known: BTreeMap<String, String> = REACH_GRID_KNOWN_WRONG
        .iter()
        .map(|(label, verdict, _)| ((*label).to_owned(), (*verdict).to_owned()))
        .collect();
    for label in known.keys().chain(wrong.keys()).collect::<BTreeSet<_>>() {
        match (known.get(label), wrong.get(label)) {
            (Some(pinned), Some(found)) if pinned == found => {}
            (pinned, found) => failures.push(format!(
                "{label}: pinned as wrong with {pinned:?}, found wrong with {found:?}"
            )),
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let manifest = Manifest::from_keyed(declines).expect("well-formed entries");
    manifest::check(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/manifests/rejection_reach_grid_declines.txt"),
        &manifest,
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff refused_history_reach_grid\n\
         Each entry is a grid cell where the twin's second walk adopts a cause the project's \
         walk does not note, or where MSBuild evaluates the twin, the project's walk commits, and the \
         twin's second walk alone withdraws it: a decline, the second walk's cost; or where a \
         walk withdraws a project MSBuild evaluates (#1200).",
    );
    // The second walk may adopt no site here: each walk judges the arm's
    // names on the values it holds (#1164).
    assert!(must_commit > 0, "the grid exercises nothing");
}

/// That the evaluation `sites` describe ([`published_sites`]) noted no
/// construct's cause twice: one construct noted by both walks and adopted as
/// if new, or noted twice by the second. A document none of whose files two
/// import points both walk has no other way to note a construct twice.
fn assert_no_site_twice(sites: &[Vec<String>], describe: &dyn Fn() -> String) {
    let [sites] = sites else {
        panic!("one evaluation published: {sites:?}");
    };
    let mut seen = BTreeSet::new();
    let twice: Vec<&String> = sites.iter().filter(|site| !seen.insert(*site)).collect();
    assert!(
        twice.is_empty(),
        "a construct's cause noted twice: {twice:?}\n{}",
        describe()
    );
}

/// Which of `walks` commit a value of `names` (an exact `Unset` among them)
/// that MSBuild, answering `theirs`, does not hold, and how, spelt for
/// [`REACH_GRID_KNOWN_WRONG`]:
/// `<walk>: commits on a project MSBuild rejects` or `<walk>: commits a
/// value MSBuild does not hold`, `; `-separated, empty where none does.
fn wrong_commits(
    walks: [(&str, &borzoi_msbuild::ParsedProject); 2],
    theirs: Option<&HashMap<String, String>>,
    names: &[&str],
) -> String {
    walks
        .iter()
        .filter_map(|(which, parsed)| {
            let wrong = names.iter().any(|name| {
                // An exact `Unset` claims the empty value, as MSBuild reports
                // an undefined property.
                let committed = match parsed.property(name) {
                    PropertyRead::Unset => Some(String::new()),
                    read => read.value().map(str::to_owned),
                };
                committed.is_some_and(|value| theirs.and_then(|t| t.get(*name)) != Some(&value))
            });
            wrong.then(|| match theirs {
                None => format!("{which}: commits on a project MSBuild rejects"),
                Some(_) => format!("{which}: commits a value MSBuild does not hold"),
            })
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// [`refused_history_sweep`] at a fixed seed.
#[test]
fn refused_history_sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1153_0b5e_55ed);
    let census = refused_history_sweep(&mut rng, 3_000);
    eprintln!("refused history sweep: {census:?}");
    assert!(
        census.first_write > 0 && census.rewrite > 0 && census.in_site > 0 && census.several > 0,
        "{census:?}"
    );
    assert!(census.twin_pairs > 0, "{census:?}");
    assert!(census.second_walk_sites > 0, "{census:?}");
    assert_eq!(census.second_walk_causes_beyond_project, 0, "{census:?}");
    assert!(census.withdrawn > 0 && census.committed > 0, "{census:?}");
}

/// #1164's table: an arm the walk cannot decide writes `R` a value
/// `VersionLessThan` throws on, and an item there calls it on `R` and on
/// `P` and `Q`, which the arm writes too and a later group rewrites, each
/// rewrite after a refused write of its name or not, in its `Include` and in
/// its condition. MSBuild takes the arm and rejects every row (MSB4184).
/// Which names the walk leaves unknown moves with the history, so a judgement
/// that tries values for those names answers each row differently; the walk
/// may commit no row's `After`.
#[test]
fn a_throw_in_an_arm_is_judged_alike_whatever_the_history() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let names = vec!["After".to_owned()];
    let call = "$([MSBuild]::VersionLessThan('$(Q)$(P)','$(R)'))";
    let sites = [
        format!("<I Include=\"{call}\" />"),
        format!("<I Include=\"x\" Condition=\"{call}\" />"),
    ];
    for site in &sites {
        for (p, q) in [(false, false), (false, true), (true, false), (true, true)] {
            let refused = |on: bool, name: &str| {
                if on {
                    format!("<{name}>{REFUSED}</{name}>")
                } else {
                    String::new()
                }
            };
            let xml = format!(
                "<Project>\n  <PropertyGroup><R>bad</R></PropertyGroup>\n  \
             <Choose><When Condition=\"{}\">\n    \
             <PropertyGroup><P>abc</P><Q>abc</Q><R>nope</R></PropertyGroup>\n    \
             <ItemGroup>{site}</ItemGroup>\n  \
             </When></Choose>\n  \
             <PropertyGroup>{}<P>v1.0</P>{}<Q></Q><After>ok</After></PropertyGroup>\n</Project>\n",
                xml_attribute(UNDECIDED_TRUE),
                refused(p, "P"),
                refused(q, "Q"),
            );
            assert_eq!(
                oracle.project(&xml, &names, Some(&project_path), &[]),
                None,
                "MSBuild rejects every row:\n{xml}"
            );
            let parsed = parse_fsproj_with_imports(
                &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml).unwrap(),
                &HashMap::new(),
                &HashMap::new(),
                None,
                None,
            )
            .unwrap();
            assert!(
                !matches!(parsed.property("After"), PropertyRead::Value(_)),
                "MSBuild rejects the project, but we commit {:?} ({:?}):\n{xml}",
                parsed.property("After"),
                parsed.rejection
            );
        }
    }
}

/// One cell of [`arm_history_grid`]: its document in each history
/// ([`HISTORIES`], in order), and the document with the write MSBuild may
/// make and the walk does not hold left out.
struct GridCell {
    label: String,
    documents: Vec<String>,
    held: String,
    /// Whether the arm is one MSBuild takes.
    taken: bool,
}

/// [`arm_history_grid`]'s histories: whether a refused write goes before the
/// write of `A`, and of `B`, that MSBuild makes after the site's arm.
const HISTORIES: [[bool; 2]; 4] = [[false, false], [true, false], [false, true], [true, true]];

/// [`arm_history_grid`]'s cells. Family `item`: #1164's own shape, an arm
/// writing a value `U` that a call there throws on (or not), beside `A` and
/// `B`, which a group after the arm rewrites, each perhaps after a refused
/// write; the call in an item's `Include` and in its condition. Family
/// `gated`: #1164's comments' shape, a write in an arm gated on `A`, which
/// has a refused history or not, then a read of the written name, in a
/// property body and an item's `Include`.
fn arm_history_cells() -> Vec<GridCell> {
    let refused = |on: bool, name: &str| {
        if on {
            format!("<{name}>{REFUSED}</{name}>")
        } else {
            String::new()
        }
    };
    let mut cells = Vec::new();
    // (Include text, condition) pairs, each calling on `U`.
    let calls: &[(&str, &str)] = &[
        (
            "$([MSBuild]::VersionLessThan('$(B)$(A)','$(U)'))",
            "$([MSBuild]::VersionLessThan('$(B)$(A)','$(U)'))",
        ),
        (
            "$([MSBuild]::VersionLessThan('$(A)','$(U)'))",
            "$([MSBuild]::VersionLessThan('$(A)','$(U)'))",
        ),
        ("a$(U[3])b", "'$(U[3])' == ''"),
    ];
    for arm in [UNDECIDED_TRUE, UNDECIDED_FALSE] {
        for (text, condition) in calls {
            for site in [
                format!("<I Include=\"{}\" />", xml_attribute(text)),
                format!(
                    "<I Include=\"x\" Condition=\"{}\" />",
                    xml_attribute(condition)
                ),
            ] {
                for before in ["bad", "2.0", "abcd"] {
                    for written in ["nope", "3.0"] {
                        for a in ["v1.0", "abc"] {
                            for b in ["", "1"] {
                                let site_text = site.clone();
                                let document = move |arm_write: &str, history: &[bool]| {
                                    let site = &site_text;
                                    format!(
                                        "<Project>\n  <PropertyGroup><U>{before}</U></PropertyGroup>\n  \
                                         <Choose><When Condition=\"{}\">\
                                         <PropertyGroup><A>abc</A><B>abc</B>{arm_write}</PropertyGroup>\
                                         <ItemGroup>{site}</ItemGroup></When></Choose>\n  \
                                         <PropertyGroup>{}<A>{a}</A>{}<B>{b}</B><After>ok</After></PropertyGroup>\n\
                                         </Project>\n",
                                        xml_attribute(arm),
                                        refused(history[0], "A"),
                                        refused(history[1], "B"),
                                    )
                                };
                                let arm_write = format!("<U>{written}</U>");
                                cells.push(GridCell {
                                    label: format!(
                                        "item / {arm} / {site} / U={before} then {written} / A={a} / B={b}"
                                    ),
                                    held: document("", &HISTORIES[0]),
                                    documents: HISTORIES
                                        .iter()
                                        .map(|history| document(&arm_write, history))
                                        .collect(),
                                    taken: arm == UNDECIDED_TRUE,
                                });
                            }
                        }
                    }
                }
            }
        }
    }
    for arm in [UNDECIDED_TRUE, UNDECIDED_FALSE] {
        for text in ["$(B[9])", "$([MSBuild]::VersionLessThan('$(B)', '2.0'))"] {
            for (kind, site) in [
                (
                    "body",
                    format!(
                        "<PropertyGroup Condition=\"{}\">{{gated}}<R>{}</R></PropertyGroup>",
                        xml_attribute(arm),
                        xml_text(text)
                    ),
                ),
                (
                    "include",
                    format!(
                        "<Choose><When Condition=\"{}\"><PropertyGroup>{{gated}}</PropertyGroup>\
                     <ItemGroup><I Include=\"{}\" /></ItemGroup></When></Choose>",
                        xml_attribute(arm),
                        xml_attribute(text)
                    ),
                ),
            ] {
                for a in ["z", "off"] {
                    for before in ["a", "abcdefghijkl0", "1.0"] {
                        let site_text = site.clone();
                        let document = move |gated: &str, history: &[bool]| {
                            let site = &site_text;
                            format!(
                                "<Project>\n  <PropertyGroup>{}<A>{a}</A><B>{before}</B></PropertyGroup>\n  \
                                 {}\n  <PropertyGroup><After>ok</After></PropertyGroup>\n</Project>\n",
                                refused(history[0], "A"),
                                site.replace("{gated}", gated),
                            )
                        };
                        let gated = format!(
                            "<B Condition=\"{}\">abcdefghijkl</B>",
                            xml_attribute("'$(A)' == 'off'")
                        );
                        cells.push(GridCell {
                            label: format!("gated / {arm} / {kind} / {text} / A={a} / B={before}"),
                            held: document("", &HISTORIES[0]),
                            documents: HISTORIES
                                .iter()
                                .map(|history| document(&gated, history))
                                .collect(),
                            taken: arm == UNDECIDED_TRUE,
                        });
                    }
                }
            }
        }
    }
    cells
}

/// #1164's shapes, graded against MSBuild in every history
/// ([`arm_history_cells`]): each cell walked as is and with a refused write
/// before each later write [`HISTORIES`] names, which MSBuild evaluates
/// alike. Per cell and history:
///
/// - where MSBuild evaluates the project, the walk claims no certain
///   rejection, and a value it commits is MSBuild's;
/// - where MSBuild rejects it, the walk commits nothing, but where MSBuild
///   evaluates the cell's held document (the arm's write the walk does not
///   hold left out): the rejection rests on a value the walk does not know,
///   which it does not judge (#1051). Those cells are pinned in
///   `manifests/rejection_arm_history_grid.txt`, so that one closing, or
///   opening, shows there; so are the cells it withdraws though MSBuild
///   evaluates them, the decline's cost;
/// - of two histories, the one with more refused writes is withdrawn
///   wherever the other is, and certain only where it is;
/// - and where MSBuild takes the arm and evaluates both the project and its
///   held document, the call throws on neither MSBuild's values nor the
///   walk's, so the walk must commit: a judgement that withdrew on every
///   name it is unsure of would fail there.
#[test]
fn arm_history_grid() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let oracle_names = vec!["After".to_owned()];
    let walk = |xml: &str| {
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, xml).unwrap(),
            &HashMap::new(),
            &HashMap::new(),
            None,
            None,
        )
        .unwrap()
    };
    let certainty =
        |parsed: &borzoi_msbuild::ParsedProject| parsed.rejection.as_ref().map(|r| r.certainty);
    let (mut cases, mut must_commit, mut rejected) = (0usize, 0usize, 0usize);
    let mut failures = Vec::new();
    let mut pinned = Vec::new();
    for cell in arm_history_cells() {
        let plain = &cell.documents[0];
        let theirs = oracle.project_design_time(plain, &oracle_names, Some(&project_path), &[]);
        // MSBuild's answer with the names as the walk holds them.
        let held_evaluates = oracle
            .project_design_time(&cell.held, &oracle_names, Some(&project_path), &[])
            .is_some();
        rejected += usize::from(theirs.is_none());
        let walked: Vec<(&[bool; 2], &String, borzoi_msbuild::ParsedProject)> = HISTORIES
            .iter()
            .zip(&cell.documents)
            .map(|(history, xml)| (history, xml, walk(xml)))
            .collect();
        let mut verdicts = BTreeSet::new();
        for (history, xml, parsed) in &walked {
            cases += 1;
            let committed = parsed.property("After");
            match &theirs {
                None if matches!(committed, PropertyRead::Value(_)) => {
                    if held_evaluates {
                        verdicts.insert("commits on a rejection resting on a value the walk does not hold (#1051)");
                    } else {
                        failures.push(format!(
                            "{} / {history:?}: MSBuild rejects, and the walk commits {committed:?}\n{xml}",
                            cell.label
                        ));
                    }
                }
                None => {}
                Some(values) => {
                    if certainty(parsed) == Some(RejectionCertainty::Certain) {
                        failures.push(format!(
                            "{} / {history:?}: MSBuild evaluates, and the walk claims it rejects: {:?}\n{xml}",
                            cell.label, parsed.rejection
                        ));
                    }
                    if let PropertyRead::Value(value) = &committed
                        && values.get("After") != Some(value)
                    {
                        failures.push(format!(
                            "{} / {history:?}: the walk commits {value:?}, MSBuild {:?}\n{xml}",
                            cell.label,
                            values.get("After")
                        ));
                    }
                    if parsed.rejection.is_some() {
                        verdicts.insert("withdraws a project MSBuild evaluates");
                    }
                    if cell.taken && held_evaluates {
                        must_commit += 1;
                        if !matches!(committed, PropertyRead::Value(_)) {
                            failures.push(format!(
                                "{} / {history:?}: the call throws on no value either side holds, \
                                 and the walk withdraws: {:?}\n{xml}",
                                cell.label, parsed.rejection
                            ));
                        }
                    }
                }
            }
        }
        for (fewer, fewer_xml, fewer_parsed) in &walked {
            for (more, _, more_parsed) in &walked {
                let ordered = fewer.iter().zip(more.iter()).all(|(f, m)| !f || *m) && fewer != more;
                if ordered
                    && (!twin_verdict_claims_no_more(
                        certainty(fewer_parsed),
                        certainty(more_parsed),
                    ) || !twin_claims_no_more(
                        &fewer_parsed.property("After"),
                        &more_parsed.property("After"),
                    ))
                {
                    failures.push(format!(
                        "{}: history {fewer:?} judged {:?}, history {more:?} {:?}\n{fewer_xml}",
                        cell.label, fewer_parsed.rejection, more_parsed.rejection
                    ));
                }
            }
        }
        if !verdicts.is_empty() {
            pinned.push((
                cell.label.clone(),
                verdicts.into_iter().collect::<Vec<_>>().join("; "),
            ));
        }
    }
    eprintln!(
        "arm history grid: {cases} cases, {rejected} cells MSBuild rejects, {must_commit} \
         must-commit points, {} cells pinned",
        pinned.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(
        rejected > 0 && must_commit > 0,
        "the grid exercises nothing"
    );
    let manifest = Manifest::from_keyed(pinned).expect("well-formed entries");
    manifest::check(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/manifests/rejection_arm_history_grid.txt"),
        &manifest,
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         rejection_generative_diff arm_history_grid\n\
         Each entry is a grid cell where, in some history, the walk commits on a project MSBuild \
         rejects over a value the walk does not hold (#1051), or withdraws a project MSBuild \
         evaluates: the decline's cost.",
    );
}

/// Fresh-seed twin of [`refused_history_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the rejection judgement"]
fn refused_history_sweep_soak() {
    let (seed, cases) = soak_parameters("refused history", 20_000);
    let mut rng = SplitMix64(seed);
    let census = refused_history_sweep(&mut rng, cases);
    eprintln!("refused history soak: {census:?}");
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

/// What an entry of a guarded import's list names on disk.
#[derive(Clone, Copy, Debug)]
enum GuardedEntry {
    /// A file that loads.
    Loads,
    /// A file MSBuild cannot load (malformed XML).
    Malformed,
    /// Nothing.
    Missing,
    /// A directory, which `Exists` sees and no import loads.
    Directory,
    /// A file that loads, spelled with a trailing slash, which names a
    /// directory to `Exists` and to the import.
    Slashed,
    /// A file that loads, spelled after an escaped `\` (`%5c`), which decodes
    /// after MSBuild has asked whether the path is rooted.
    Escaped,
}

impl GuardedEntry {
    const ALL: [GuardedEntry; 6] = [
        GuardedEntry::Loads,
        GuardedEntry::Malformed,
        GuardedEntry::Missing,
        GuardedEntry::Directory,
        GuardedEntry::Slashed,
        GuardedEntry::Escaped,
    ];
}

/// Every guarded import over a list of one or two entries of each kind
/// ([`GuardedEntry`]), its `Exists` guard spelled as the import or with each
/// `\` respelled, behind a conjunct the walk cannot decide that MSBuild takes
/// true or false, before the guard or after it, on the import or on an
/// `<ImportGroup>` around it: each held certain-implies-exact
/// against MSBuild. Where MSBuild rejects the project, the walk commits no
/// value of the property written after the import; where it evaluates it,
/// the walk claims no certain rejection and commits MSBuild's value. And it
/// must commit where the import loads every entry, or where a guard spelled
/// as the import is false (an entry missing, or a file spelled as a
/// directory): wherever MSBuild takes the undecided conjunct, the project
/// evaluates.
#[test]
fn guarded_import_lists_are_judged_as_msbuild_judges_them() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    // Each list's entries in a directory of their own, one file per position.
    let spell = |kind: GuardedEntry, list: usize, at: usize| -> String {
        std::fs::create_dir_all(dir.join(format!("d{list}"))).unwrap();
        let name = format!("d{list}/e{at}.props");
        let path = dir.join(&name);
        match kind {
            GuardedEntry::Loads | GuardedEntry::Slashed | GuardedEntry::Escaped => {
                std::fs::write(&path, "<Project />").unwrap();
            }
            GuardedEntry::Malformed => std::fs::write(&path, "<Project>").unwrap(),
            GuardedEntry::Missing => {}
            GuardedEntry::Directory => std::fs::create_dir(&path).unwrap(),
        }
        match kind {
            GuardedEntry::Slashed => format!("{name}/"),
            GuardedEntry::Escaped => format!("%5c{name}"),
            _ => name,
        }
    };
    let mut lists: Vec<Vec<GuardedEntry>> = GuardedEntry::ALL.iter().map(|k| vec![*k]).collect();
    for a in GuardedEntry::ALL {
        for b in GuardedEntry::ALL {
            lists.push(vec![a, b]);
        }
    }
    let project_path = dir.join("Demo.fsproj");
    let names = vec!["After".to_owned()];
    let (mut graded, mut rejected, mut committed) = (0usize, 0usize, 0usize);
    for (index, kinds) in lists.iter().enumerate() {
        let entries: Vec<String> = kinds
            .iter()
            .enumerate()
            .map(|(at, kind)| spell(*kind, index, at))
            .collect();
        let list = entries.join(";");
        let loads = kinds.iter().all(|kind| matches!(kind, GuardedEntry::Loads));
        let exists = kinds.iter().all(|kind| {
            matches!(
                kind,
                GuardedEntry::Loads
                    | GuardedEntry::Malformed
                    | GuardedEntry::Directory
                    | GuardedEntry::Escaped
            )
        });
        for guard in [list.clone(), list.replace('/', "\\")] {
            // Where the walk must commit, whatever MSBuild makes of the
            // conjunct it cannot decide.
            // An escaped `\` leaves the guard undecided, which the walk
            // declines whatever the other entries say.
            let escaped = kinds
                .iter()
                .any(|kind| matches!(kind, GuardedEntry::Escaped));
            let own_guard_false = guard == list && !exists && !escaped;
            for (gate, grouped) in [
                format!("'É' == 'é' And Exists('{guard}')"),
                format!("Exists('{guard}') And 'É' == 'é'"),
                format!("'É' == 'Ê' And Exists('{guard}')"),
            ]
            .into_iter()
            .flat_map(|gate| [(gate.clone(), false), (gate, true)])
            {
                // On the import, or on an `<ImportGroup>` around it, which
                // MSBuild evaluates before the group's imports run.
                let import = if grouped {
                    format!(
                        "  <ImportGroup Condition=\"{gate}\">\n    <Import Project=\"{list}\" />\n  \
                         </ImportGroup>\n"
                    )
                } else {
                    format!("  <Import Project=\"{list}\" Condition=\"{gate}\" />\n")
                };
                let xml = format!(
                    "<Project>\n{import}  <PropertyGroup><After>ok</After></PropertyGroup>\n\
                     </Project>\n"
                );
                let theirs = oracle.project(&xml, &names, Some(&project_path), &[]);
                let parsed = parse_fsproj_with_imports(
                    &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml).unwrap(),
                    &HashMap::new(),
                    &HashMap::new(),
                    None,
                    None,
                )
                .unwrap();
                let ours = parsed.property("After");
                // The lists are literal, so a group's guard asks of the
                // import's path what its own would.
                let must_commit = loads || own_guard_false;
                let context = format!("{kinds:?}, guard {guard:?}\n{xml}");
                graded += 1;
                assert!(
                    !must_commit || matches!(ours, PropertyRead::Value(_)),
                    "the project evaluates wherever MSBuild takes the gate, but we decline \
                     {ours:?}: {context}"
                );
                match theirs {
                    None => {
                        rejected += 1;
                        assert!(
                            !matches!(ours, PropertyRead::Value(_)),
                            "MSBuild rejects the project, but we commit {ours:?}: {context}"
                        );
                    }
                    Some(values) => {
                        assert!(
                            parsed
                                .rejection
                                .as_ref()
                                .is_none_or(|r| r.certainty != RejectionCertainty::Certain),
                            "MSBuild evaluates the project, but we reject it: {context}"
                        );
                        if let PropertyRead::Value(value) = &ours {
                            committed += 1;
                            assert_eq!(
                                Some(value),
                                values.get("After"),
                                "certain-implies-exact: {context}"
                            );
                        }
                    }
                }
            }
        }
    }
    eprintln!(
        "guarded import lists: {graded} graded, {rejected} MSBuild rejects, {committed} we commit"
    );
    // Each outcome is graded: a walk that withdrew every project, or a
    // fixture MSBuild rejected wholesale, would pass the contract.
    assert!(
        rejected > 0 && committed > 0,
        "{rejected} rejected, {committed} committed"
    );
}

/// An `<ImportGroup>`'s guard is evaluated once, before its imports run: an
/// earlier import that rewrites `P` (to a spelling naming a directory) does
/// not reach it, so the later import of `$(P)` is made where `'É' == 'é'`
/// holds, and fails. The walk may not ask the group's `Exists` of the
/// rewritten `P`.
#[test]
fn an_import_group_guard_is_not_asked_again_after_its_imports_run() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(dir.join("ok.props"), "<Project />").unwrap();
    std::fs::write(
        dir.join("rewrite.props"),
        "<Project><PropertyGroup><P>ok.props/</P></PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    let xml = "<Project>\n  <PropertyGroup><P>ok.props</P></PropertyGroup>\n  \
               <ImportGroup Condition=\"Exists('$(P)')\">\n    \
               <Import Project=\"rewrite.props\" />\n    \
               <Import Project=\"$(P)\" Condition=\"'É' == 'é'\" />\n  </ImportGroup>\n  \
               <PropertyGroup><After>ok</After></PropertyGroup>\n</Project>\n";
    let theirs = oracle.project(xml, &["After".to_owned()], Some(&project_path), &[]);
    assert_eq!(theirs, None, "MSBuild rejects the project");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, xml).unwrap(),
        &HashMap::new(),
        &HashMap::new(),
        None,
        None,
    )
    .unwrap();
    assert!(
        !matches!(parsed.property("After"), PropertyRead::Value(_)),
        "we commit {:?}",
        parsed.property("After")
    );
}

/// An `<ImportGroup>`'s `Exists` guard says nothing of an import whose path
/// the walk cannot compute: the group's first import rewrites `P` through a
/// function the walk does not model, to a file that does not exist, after
/// the group's gate admitted the old `P`. MSBuild then makes the second
/// import where `'É' == 'é'` holds, and fails (MSB4019).
#[test]
fn a_group_guard_does_not_rule_out_rejecting_an_uncomputed_import() {
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(dir.join("ok.props"), "<Project />").unwrap();
    std::fs::write(
        dir.join("rewrite.props"),
        "<Project><PropertyGroup><P>$([System.String]::Copy('missing.props'))</P>\
         </PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    let xml = "<Project>\n  <PropertyGroup><P>ok.props</P></PropertyGroup>\n  \
               <ImportGroup Condition=\"Exists('$(P)')\">\n    \
               <Import Project=\"rewrite.props\" />\n    \
               <Import Project=\"$(P)\" Condition=\"'É' == 'é'\" />\n  </ImportGroup>\n  \
               <PropertyGroup><After>ok</After></PropertyGroup>\n</Project>\n";
    let theirs = oracle.project(xml, &["After".to_owned()], Some(&project_path), &[]);
    assert_eq!(theirs, None, "MSBuild rejects the project");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project_path, xml).unwrap(),
        &HashMap::new(),
        &HashMap::new(),
        None,
        None,
    )
    .unwrap();
    // Neither a value nor an exact absence: MSBuild rejects the project.
    assert!(
        !parsed.property("After").is_exact(),
        "we claim {:?}",
        parsed.property("After")
    );
}

/// The blocks [`second_walk_site_sweep`] composes documents from: the
/// refused-then-rebound history of `P` and clean writes, sites only the first
/// walk finds, only the second, and both, a `<Choose>` whose course the two
/// walks take apart, a group only the first walk defers, a file
/// (`other.props`, holding a site) the two walks load through different
/// imports, two files (`x.props`, `y.props`) failing one import at one span,
/// a file failing an import that the walks reach through two spellings of
/// its directory (`sub/z.props`, `SUB/z.props`, one file where the file
/// system folds case), one cause in two texts of an element, and texts
/// reached for certain whose throws the two walks name apart (`$(P[9])` in
/// the second, holding the refused `P` at its final value, the certain
/// `$(S[9])` in the first), which is where a second walk adopts a site once
/// both walks judge an arm's names on the values they hold (#1164).
const SITE_BLOCKS: &[&str] = &[
    "<PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup>",
    "<PropertyGroup><P>@(J)</P><P></P></PropertyGroup>",
    "<PropertyGroup><P>abc</P></PropertyGroup>",
    "<Choose><When Condition=\"'$(P)' == 'off' And '$(S[9])' != ''\"><PropertyGroup><W>1</W></PropertyGroup></When><Otherwise><PropertyGroup><W>2</W></PropertyGroup></Otherwise></Choose>",
    "<Choose><When Condition=\"'É' == 'é'\"><PropertyGroup><P>abcdefghijkl</P></PropertyGroup><ItemGroup><I Include=\"$(P[9])\" /></ItemGroup></When></Choose>",
    "<ItemGroup><K Include=\"$(S[9])\" /></ItemGroup>",
    "<ItemGroup><K Include=\"$(P[9])\" /></ItemGroup>",
    "<PropertyGroup><T>$(S[9])</T></PropertyGroup>",
    "<Choose><When Condition=\"'É' == 'é'\"><Choose><When Condition=\"'$(P)' == 'off'\"><ItemGroup><I Include=\"x\" /></ItemGroup></When></Choose></When></Choose>",
    "<Choose><When Condition=\"'É' == 'é'\"><PropertyGroup><Q>nope</Q></PropertyGroup><ItemGroup><I Include=\"$([MSBuild]::VersionLessThan('$(P)v1.0','$(Q)'))\" /></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"'É' == 'é'\"><PropertyGroup><P>abcdefghijkl</P></PropertyGroup><ItemGroup><I Include=\"$(P[9])$(S[9])\" Exclude=\"$(S[9])\" /></ItemGroup></When></Choose>",
    "<Choose><When Condition=\"'$(P)' == 'off' And '$(S[9])' != ''\"><PropertyGroup><W>1</W></PropertyGroup></When><Otherwise><PropertyGroup><F>other.props</F></PropertyGroup></Otherwise></Choose><Import Project=\"$(F)\" Condition=\"'$(F)' != ''\" /><Import Project=\"other.props\" />",
    "<Choose><When Condition=\"'$(P)' == 'off' And '$(S[9])' != ''\"><PropertyGroup><W>1</W></PropertyGroup></When><Otherwise><PropertyGroup><G>x.props</G></PropertyGroup></Otherwise></Choose><Import Project=\"$(G)\" Condition=\"'$(G)' != ''\" /><Import Project=\"y.props\" />",
    "<Choose><When Condition=\"'$(P)' == 'off' And '$(S[9])' != ''\"><PropertyGroup><W>1</W></PropertyGroup></When><Otherwise><PropertyGroup><H>SUB/z.props</H></PropertyGroup></Otherwise></Choose><Import Project=\"$(H)\" Condition=\"'$(H)' != ''\" /><Import Project=\"sub/z.props\" />",
    "<Choose><When Condition=\"'É' == 'é'\"><PropertyGroup><P>abcdefghijkl</P><Q>nope</Q></PropertyGroup><ItemGroup><I Include=\"$([MSBuild]::VersionLessThan('$(P)v1.0','$(Q)'))$([MSBuild]::VersionLessThan('nope','$(Q)'))\" Exclude=\"$([MSBuild]::VersionLessThan('nope','$(Q)'))\" /></ItemGroup></When></Choose>",
    "<PropertyGroup><P>@(J)</P><P>z</P></PropertyGroup><ItemGroup><K Include=\"$(P[9])$(S[9])\" Exclude=\"$(P[9])\" /></ItemGroup>",
    "<PropertyGroup><P>@(J)</P><P>z</P><T>$(P[9])$(S[9])</T></PropertyGroup>",
];

/// What [`second_walk_site_sweep`] compared.
#[derive(Debug, Default)]
struct SiteSweepCensus {
    cases: usize,
    /// Cases whose evaluation adopted a site from its second walk.
    adopted: usize,
    /// Rejection diagnostics compared, over the entry forms.
    sites: usize,
}

/// A site is one construct, however the two walks' courses part and
/// wherever the construct's file stands (#1153). Each case composes two to
/// six [`SITE_BLOCKS`] and evaluates them in the entry project and, behind an
/// `<Import>`, in an imported file, whose constructs share one published span.
/// Per case:
///
/// - neither form notes a construct's cause twice
///   ([`assert_no_site_twice`]): one construct noted by both walks and
///   adopted as if new;
/// - the imported form notes the same causes as the entry form, as many
///   times each: a construct of an imported file matched to another by their
///   shared published span would be lost there.
///
/// No oracle is asked.
fn second_walk_site_sweep(rng: &mut SplitMix64, cases: usize) -> SiteSweepCensus {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    std::fs::write(
        dir.join("other.props"),
        "<Project><ItemGroup><K Include=\"$(S[9])\" /></ItemGroup></Project>",
    )
    .unwrap();
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    // `SUB/` reaches `sub/` on every host: a case-folding file system folds
    // it, and elsewhere a link spells it.
    #[cfg(unix)]
    if borzoi_msbuild::observed::host_fs::symlink_metadata(dir.join("SUB")).is_err() {
        std::os::unix::fs::symlink(dir.join("sub"), dir.join("SUB")).unwrap();
    }
    for parent in ["x.props", "y.props", "sub/z.props"] {
        std::fs::write(
            dir.join(parent),
            "<Project><Import Project=\"missing.props\" /></Project>",
        )
        .unwrap();
    }
    let environment = HashMap::new();
    let walk = |xml: &str| {
        parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &environment,
            None,
            None,
        )
        .expect("well-formed")
    };
    let causes = |parsed: &borzoi_msbuild::ParsedProject| -> Vec<String> {
        let mut causes: Vec<String> = parsed
            .diagnostics
            .iter()
            .filter_map(|d| match &d.kind {
                borzoi_msbuild::DiagnosticKind::Rejected { cause }
                | borzoi_msbuild::DiagnosticKind::MayBeRejected { cause } => {
                    Some(format!("{cause:?}"))
                }
                _ => None,
            })
            .collect();
        causes.sort();
        causes
    };
    let prefix = "<PropertyGroup><S>a</S><Q>bad</Q></PropertyGroup><ItemGroup><J Include=\"1.0\" /></ItemGroup>";
    let mut census = SiteSweepCensus::default();
    for _ in 0..cases {
        let count = 2 + rng.below(5);
        let blocks: String = (0..count).map(|_| *rng.pick(SITE_BLOCKS)).collect();
        let entry_xml = format!("<Project>{prefix}{blocks}</Project>");
        std::fs::write(
            dir.join("inner.props"),
            format!("<Project>{blocks}</Project>"),
        )
        .unwrap();
        let imported_xml = format!("<Project>{prefix}<Import Project=\"inner.props\" /></Project>");
        let ((entry, adopted), entry_published) =
            published_sites(|| second_walk_sites(|| walk(&entry_xml)));
        let (imported, imported_published) = published_sites(|| walk(&imported_xml));
        census.cases += 1;
        census.adopted += usize::from(!adopted.is_empty());
        census.sites += causes(&entry).len();
        assert_no_site_twice(&entry_published, &|| entry_xml.clone());
        assert_no_site_twice(&imported_published, &|| imported_xml.clone());
        assert_eq!(
            causes(&entry),
            causes(&imported),
            "the entry project and the imported file note different sites\n{entry_xml}\n\
             entry: {:#?}\nimported: {:#?}",
            entry.diagnostics,
            imported.diagnostics
        );
    }
    census
}

/// [`second_walk_site_sweep`] at a fixed seed.
#[test]
fn second_walk_site_sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1153_517e);
    let census = second_walk_site_sweep(&mut rng, 1_500);
    eprintln!("second walk site sweep: {census:?}");
    assert!(census.adopted > 100, "{census:?}");
}

/// Fresh-seed twin of [`second_walk_site_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the rejection judgement"]
fn second_walk_site_sweep_soak() {
    let (seed, cases) = soak_parameters("second walk sites", 20_000);
    let mut rng = SplitMix64(seed);
    let census = second_walk_site_sweep(&mut rng, cases);
    eprintln!("second walk site soak: {census:?}");
}
