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
//! `judge_using_task`) is held to it certain-implies-exact:
//!
//! - MSBuild rejects the project: the walk claims it may;
//! - MSBuild evaluates it: the walk claims no certain rejection, and commits
//!   the value written after the `<UsingTask>`;
//! - the walk claims a certain rejection: the construct it names is one
//!   MSBuild refuses, alone ([`assert_msbuild_refuses_alone`]). Which refusal
//!   MSBuild reports first, of several, the walk does not claim.
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

/// An inline task's `<UsingTask>` attributes, but for its children: every
/// value one MSBuild takes, so that what a document refuses is its children's.
const INLINE: &str = "TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\"";

/// Items every graded document declares: `Flags`, a list of one boolean, so
/// that a value naming it expands to one MSBuild takes, where the walk cannot
/// tell; and `Input`, of one short item, which a transform taking more of it
/// throws on.
const ITEMS: &str = "<ItemGroup><Flags Include=\"true\" /><Input Include=\"a\" /></ItemGroup>";

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

/// What `V` holds where a document writes it under a gate the walk cannot
/// decide.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Doubt {
    /// No such write, or one of the value the unconditional write puts.
    None,
    /// A value other than the unconditional write's, which is MSBuild's: the
    /// walk judges the value it holds, not the one MSBuild may (#1051).
    Differs,
}

/// Grade `body` (the `<UsingTask>` and what it needs), after `writes` (a
/// property group's content), against design-time evaluation: certain-
/// implies-exact. A rejection resting on a value the walk holds none of (`V`
/// written by a write it refused) is the judgement over the values a name may
/// hold, which the walk does not make yet (#1051): not graded here, and shown
/// by the caller to rest there; so is one resting on a doubted write of a
/// value other than the one the walk holds ([`Doubt::Differs`]).
///
/// MSBuild's registry failing on two parameters whose names fold to one is
/// an internal error (MSB1025) rather than an invalid project, which the
/// oracle reports as the exception: graded as that rejection.
fn grade(oracle: &mut Oracle, writes: &str, body: &str, doubt: Doubt) -> Graded {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let xml = format!(
        "<Project><PropertyGroup><Empty></Empty>{writes}</PropertyGroup>{ITEMS}{body}\
         <PropertyGroup><After>ok</After></PropertyGroup></Project>"
    );
    std::fs::write(&project_path, &xml).unwrap();
    let code = design_time_code(oracle, &xml, &project_path).map(|r| r.code);
    let msbuild_rejects = code.is_some();
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
    // Every certain registration refusal the walk reports, each a diagnostic
    // the LSP renders, names a construct MSBuild refuses alone; and the value
    // it keeps is bounded.
    for diagnostic in &parsed.diagnostics {
        let (borzoi_msbuild::DiagnosticKind::Rejected { cause }
        | borzoi_msbuild::DiagnosticKind::MayBeRejected { cause }) = &diagnostic.kind
        else {
            continue;
        };
        let bound = 256 + "…".len();
        match cause {
            borzoi_msbuild::RejectionCause::UsingTaskRegistration { task, value, .. } => {
                assert!(
                    value.len() <= bound && task.len() <= bound,
                    "a refusal keeps a value of {} bytes and a task name of {}: {xml}",
                    value.len(),
                    task.len()
                );
            }
            borzoi_msbuild::RejectionCause::UsingTaskParameterCollision {
                task,
                first,
                second,
            } => {
                assert!(
                    first.len() <= bound && second.len() <= bound,
                    "a collision keeps names of {} and {} bytes",
                    first.len(),
                    second.len()
                );
                assert!(
                    task.len() <= bound,
                    "a collision keeps a task name of {} bytes",
                    task.len()
                );
            }
            _ => {}
        }
        if matches!(
            diagnostic.kind,
            borzoi_msbuild::DiagnosticKind::Rejected { .. }
        ) && !matches!(cause, borzoi_msbuild::RejectionCause::LoadTime(_))
        {
            assert!(
                code.is_some(),
                "MSBuild evaluates, and the walk claims a refusal: {xml}\n{diagnostic:#?}"
            );
            let rejection = borzoi_msbuild::Rejection {
                certainty: RejectionCertainty::Certain,
                cause: cause.clone(),
                span: diagnostic.span.clone(),
                origin: diagnostic.origin.clone(),
            };
            assert_msbuild_refuses_alone(oracle, writes, &rejection, &xml, &project_path);
        }
    }
    let v_unheld = writes.contains("<V>") && !parsed.properties.contains_key("V");
    if code.is_some() {
        assert!(
            walk.is_some() || v_unheld || doubt == Doubt::Differs,
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

/// How MSBuild's design-time evaluation rejects `xml`, at `path`, if it does.
/// Its registry failing on two parameters whose names fold to one is an
/// internal error (MSB1025) rather than an invalid project, which the oracle
/// reports as the exception: that rejection, at no place.
fn design_time_code(
    oracle: &mut Oracle,
    xml: &str,
    path: &std::path::Path,
) -> Option<common::DesignTimeRejection> {
    match oracle.design_time_rejection(xml, path) {
        Ok(rejected) => rejected,
        Err(error) if error.contains("same key") => Some(common::DesignTimeRejection {
            code: "MSB1025".to_owned(),
            line: 0,
            column: 0,
        }),
        Err(error) => panic!("MSBuild fails by another exception, {error}: {xml}"),
    }
}

/// `value` as an attribute's text, its whitespace kept.
fn attribute_text(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('"', "&quot;")
        .replace('\t', "&#9;")
        .replace('\n', "&#10;")
        .replace('\r', "&#13;")
}

/// A `<UsingTask>` holding the construct `cause` names and nothing else
/// MSBuild refuses, and the attribute it is: what MSBuild must refuse, alone,
/// for the walk's claim that it refuses the construct to hold. A refused
/// attribute is replayed as written (`raw`, the source text of the attribute
/// in the element the rejection spans), so MSBuild expands it as it did in
/// the document, not the walk's expansion of it. `None` for a cause this
/// differential does not isolate.
fn alone(
    cause: &borzoi_msbuild::RejectionCause,
    raw: Option<&str>,
) -> Option<(String, &'static str)> {
    use borzoi_msbuild::RejectionCause;
    Some(match cause {
        RejectionCause::UsingTaskRegistration {
            attribute, value, ..
        } => {
            // An attribute written empty, or not written, is the loader's to
            // refuse, never the registration's.
            let v = match raw {
                Some(raw) if !raw.is_empty() => raw.to_owned(),
                _ => panic!(
                    "a registration refusal of `{attribute}`, not written with text ({value:?})"
                ),
            };
            match attribute.as_str() {
                "TaskName" => (
                    format!("<UsingTask TaskName=\"{v}\" AssemblyFile=\"y.dll\" />"),
                    "TaskName",
                ),
                "TaskFactory" => (
                    format!(
                        "<UsingTask TaskName=\"X\" TaskFactory=\"{v}\" AssemblyFile=\"y.dll\">\
                         <Task>x</Task></UsingTask>"
                    ),
                    "TaskFactory",
                ),
                "AssemblyFile" => (
                    format!("<UsingTask TaskName=\"X\" AssemblyFile=\"{v}\" />"),
                    "AssemblyFile",
                ),
                "AssemblyName" => (
                    format!("<UsingTask TaskName=\"X\" AssemblyName=\"{v}\" />"),
                    "AssemblyName",
                ),
                "Evaluate" => (
                    format!("<UsingTask {INLINE}><Task Evaluate=\"{v}\">x</Task></UsingTask>"),
                    "Evaluate",
                ),
                "ParameterType" | "Output" | "Required" => {
                    let name = match attribute.as_str() {
                        "ParameterType" => "ParameterType",
                        "Output" => "Output",
                        _ => "Required",
                    };
                    (
                        format!(
                            "<UsingTask {INLINE}><ParameterGroup><A {name}=\"{v}\" />\
                             </ParameterGroup><Task>x</Task></UsingTask>"
                        ),
                        name,
                    )
                }
                other => panic!("a registration attribute the differential does not know: {other}"),
            }
        }
        // `raw`: the two parameters as written, the names whole.
        RejectionCause::UsingTaskParameterCollision { .. } => (
            format!(
                "<UsingTask {INLINE}><ParameterGroup>{}</ParameterGroup><Task>x</Task></UsingTask>",
                raw.expect("a collision's parameters, read from the document")
            ),
            "",
        ),
        RejectionCause::ThrowingExpression { expression } => (
            format!(
                "<UsingTask TaskName=\"{}\" AssemblyFile=\"y.dll\" />",
                attribute_text(expression)
            ),
            "TaskName",
        ),
        RejectionCause::IllegalCondition { condition } => (
            format!(
                "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Condition=\"{}\" />",
                attribute_text(condition)
            ),
            "Condition",
        ),
        _ => return None,
    })
}

/// That the construct `rejection` names is in `xml`, the document the walk
/// claimed it in, where the rejection says (an attribute of that name in the
/// element it spans), and that MSBuild refuses it, alone ([`alone`]), after
/// the same `writes`: it rejects the project, with the error the construct
/// earns ([`code_of`]), pointing at the attribute it is.
fn assert_msbuild_refuses_alone(
    oracle: &mut Oracle,
    writes: &str,
    rejection: &borzoi_msbuild::Rejection,
    xml: &str,
    path: &std::path::Path,
) {
    let cause = &rejection.cause;
    if let borzoi_msbuild::RejectionCause::UsingTaskRegistration { attribute, .. } = cause {
        assert!(
            xml[rejection.span.clone()].contains(&format!(" {attribute}=")),
            "the walk claims MSBuild refuses `{attribute}`, and the element it names has no such \
             attribute: {xml}\n{rejection:#?}"
        );
    }
    let raw = match cause {
        borzoi_msbuild::RejectionCause::UsingTaskRegistration { attribute, .. } => {
            raw_attribute(xml, rejection.span.clone(), attribute)
        }
        borzoi_msbuild::RejectionCause::UsingTaskParameterCollision { .. } => {
            Some(colliding_parameters(xml, rejection.span.start))
        }
        _ => None,
    };
    let Some((body, attribute)) = alone(cause, raw.as_deref()) else {
        panic!("a certain refusal the differential does not isolate: {cause:?}: {xml}");
    };
    // At the document's own path, so that what reads the project's name or
    // directory reads what it did there.
    // The document as it was, every property and item in it, with its
    // `<UsingTask>`s replaced by the one construct.
    let _ = writes;
    let alone = without_using_tasks(xml).replacen("</Project>", &format!("{body}</Project>"), 1);
    std::fs::write(path, &alone).unwrap();
    let Some(rejected) = design_time_code(oracle, &alone, path) else {
        panic!(
            "the walk claims MSBuild refuses {cause:?}, and alone MSBuild evaluates it: \
             {alone}\nclaimed in {xml}"
        );
    };
    if let Some(expected) = code_of(cause) {
        assert_eq!(
            rejected.code, expected,
            "the walk claims MSBuild refuses {cause:?}, and alone it rejects otherwise: \
             {alone}\nclaimed in {xml}"
        );
    }
    if let Some(name) = attribute_at(&alone, &rejected) {
        assert_eq!(
            name, attribute,
            "the walk claims MSBuild refuses {cause:?}, and alone it points at {name}: \
             {alone}\nclaimed in {xml}"
        );
    }
}

/// The parameter starting at `at` in `xml` and the earlier one its name folds
/// to, as empty elements of their names as written: what a collision the walk
/// claims there is between.
fn colliding_parameters(xml: &str, at: usize) -> String {
    let name = |node: roxmltree::Node<'_, '_>| -> String {
        xml[node.range().start + 1..]
            .chars()
            .take_while(|c| !c.is_whitespace() && *c != '/' && *c != '>')
            .collect()
    };
    let document = borzoi_msbuild::document::parse(xml).expect("well-formed");
    let second = document
        .descendants()
        .find(|node| node.is_element() && node.range().start == at)
        .expect("the collision's span starts at a parameter");
    let second_name = name(second);
    let first_name =
        std::iter::successors(second.prev_sibling_element(), |n| n.prev_sibling_element())
            .map(name)
            .find(|first| first.eq_ignore_ascii_case(&second_name))
            .expect("an earlier parameter of the folded name");
    format!("<{first_name} /><{second_name} />")
}

/// `xml` without its `<UsingTask>` elements (any prefix), the rest as
/// written.
fn without_using_tasks(xml: &str) -> String {
    let document = borzoi_msbuild::document::parse(xml).expect("well-formed");
    let mut ranges: Vec<std::ops::Range<usize>> = document
        .descendants()
        .filter(|node| node.is_element() && node.tag_name().name() == "UsingTask")
        .map(|node| node.range())
        .collect();
    ranges.sort_by_key(|range| std::cmp::Reverse(range.start));
    let mut out = xml.to_owned();
    for range in ranges {
        out.replace_range(range, "");
    }
    out
}

/// The source text of the attribute `name` of the element `span` starts in
/// `xml`, as written (escaped), if it has one.
fn raw_attribute(xml: &str, span: std::ops::Range<usize>, name: &str) -> Option<String> {
    let element = &xml[span];
    // The start tag ends at the first `>` outside an attribute's quotes.
    let mut quote = None;
    let mut end = element.len();
    for (at, c) in element.char_indices() {
        match quote {
            Some(open) if c == open => quote = None,
            Some(_) => {}
            None if c == '"' || c == '\'' => quote = Some(c),
            None if c == '>' => {
                end = at;
                break;
            }
            None => {}
        }
    }
    let tag = &element[..end];
    let at = tag.find(&format!(" {name}="))? + name.len() + 2;
    let open = tag[at..].chars().next()?;
    let rest = &tag[at + 1..];
    Some(rest[..rest.find(open)?].to_owned())
}

/// The attribute MSBuild's rejection of `xml` points at, if it points at one.
fn attribute_at(xml: &str, rejected: &common::DesignTimeRejection) -> Option<String> {
    if rejected.line == 0 {
        return None;
    }
    // XML's line breaks (`\r\n`, `\r` and `\n` alike), and its columns in
    // UTF-16 units, as `XmlReader` counts them.
    let mut line_start = 0;
    let mut lines = 1;
    let mut chars = xml.char_indices().peekable();
    while lines < rejected.line {
        let Some((at, c)) = chars.next() else {
            panic!("MSBuild points past the file: {rejected:?}: {xml}");
        };
        if c == '\r' && chars.peek().is_some_and(|(_, next)| *next == '\n') {
            continue;
        }
        if c == '\r' || c == '\n' {
            lines += 1;
            line_start = at + 1;
        }
    }
    let mut offset = line_start;
    let mut units = 1;
    for c in xml[line_start..].chars() {
        if units >= rejected.column {
            break;
        }
        units += c.len_utf16();
        offset += c.len_utf8();
    }
    let name: String = xml[offset..]
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.' | ':'))
        .collect();
    (!name.is_empty() && xml[offset + name.len()..].starts_with('=')).then_some(name)
}

/// The error MSBuild rejects a construct with, alone ([`alone`]), as
/// [`Oracle::design_time_rejection_code`] reports it, for a `cause` the walk
/// claims certainly: `MSB4184` for an expression that throws, `MSB1025` for
/// two parameters one name to its registry, `MSB4022` for an attribute whose
/// value the registration does not take, `MSB4069` for a parameter type it
/// does not resolve, `MSB4067` for a body under no task factory. A condition
/// MSBuild refuses has a code by why it does, which the cause does not carry
/// (`condition_diff` grades conditions): `None`, its place alone graded.
fn code_of(cause: &borzoi_msbuild::RejectionCause) -> Option<String> {
    use borzoi_msbuild::RejectionCause;
    Some(match cause {
        RejectionCause::ThrowingExpression { .. } => "MSB4184".to_owned(),
        RejectionCause::UsingTaskParameterCollision { .. } => "MSB1025".to_owned(),
        RejectionCause::UsingTaskRegistration {
            attribute, value, ..
        } => match attribute.as_str() {
            "TaskFactory" => "MSB4067",
            "ParameterType" if !value.is_empty() => "MSB4069",
            _ => "MSB4022",
        }
        .to_owned(),
        RejectionCause::IllegalCondition { .. } => return None,
        other => panic!("a refusal the registration differential does not expect: {other:?}"),
    })
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
    "@(Flags)",
    "@(Nothing)",
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
    /// Through a property written under a gate the walk cannot decide, over
    /// an unconditional write of another value (or the same one): MSBuild
    /// holds the value.
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

/// `value` as an element's text.
fn element_text(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

/// A document putting `value` in `place` through `source`: its writes and
/// its body. `other` is what a [`Source::Doubted`] write puts first.
fn document(place: &str, value: &str, source: Source, other: &str) -> (String, String) {
    let text = element_text(value);
    let attribute = text.replace('"', "&quot;");
    let (writes, spliced) = match source {
        Source::Literal => (String::new(), attribute),
        Source::Certain => (format!("<V>{text}</V>"), "$(V)".to_owned()),
        Source::Doubted => (
            format!(
                "<V>{}</V><V Condition=\"{UNDECIDED_TRUE}\">{text}</V>",
                element_text(other)
            ),
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
        // `AssemblyFile`'s own `\` turned into `/` before it expands, where `\` is no
        // separator: on Windows the split finds no `\`, and the file is named.
        (
            "<PropertyGroup><Slash>/foo</Slash></PropertyGroup>\
             <UsingTask TaskName=\"X\" AssemblyFile=\"$(Slash.Split('\\')[0])\" />"
                .to_owned(),
            !cfg!(windows),
            (!cfg!(windows)).then_some(Certain),
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
        // A value the walk does not compute: MSBuild's verdict either way,
        // and the walk's a decline.
        (
            inline_task(
                "",
                "<Task Evaluate=\"$([System.Runtime.InteropServices.RuntimeInformation]::ProcessArchitecture)\">x</Task>",
            ),
            true,
            Some(Possible),
        ),
        (inline_task("", "<Task Evaluate=\"@(Flags)\">x</Task>"), false, Some(Possible)),
        (inline_task("", "<Task Evaluate=\"@(Nothing)\">x</Task>"), true, Some(Possible)),
        // A factory name a fold outside ASCII may match: a decline.
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"É\" AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>".to_owned(),
            false,
            Some(Possible),
        ),
        // The body is the last child and the parameters the first: a body
        // before the parameters is neither, and nothing of either is read.
        (
            inline_task("", "<Task Evaluate=\"off\">x</Task><ParameterGroup><A Required=\"no\" /></ParameterGroup>"),
            false,
            None,
        ),
        (
            inline_task("", "<ParameterGroup /><Task Evaluate=\"off\">x</Task>"),
            true,
            Some(Certain),
        ),
        // A refusal after a step MSBuild may stop at, a parameter type the
        // walk does not know: MSBuild rejects either way, and the walk names
        // a construct it refuses, whichever error MSBuild reports
        // (`assert_msbuild_refuses_alone` grades it alone).
        (
            inline_task(
                "",
                "<ParameterGroup><A ParameterType=\"System.Object\" Required=\"bad\" /></ParameterGroup><Task>x</Task>",
            ),
            true,
            Some(Certain),
        ),
        // So after an earlier task MSBuild may stop at.
        (
            format!(
                "{}{}",
                inline_task(
                    "",
                    "<ParameterGroup><A ParameterType=\"System.Object\" /></ParameterGroup><Task>x</Task>"
                ),
                inline_task("", "<Task Evaluate=\"off\">x</Task>").replace("\"X\"", "\"Y\""),
            ),
            true,
            Some(Certain),
        ),
        // A name that may form an item list with the text after it (`At`
        // holds `@`, so the name is `@(Nothing)`, which is empty, and MSBuild
        // refuses it): a value the walk does not compute, a decline.
        (
            format!(
                "<PropertyGroup><At>@</At><At Condition=\"{UNDECIDED_TRUE}\">@</At></PropertyGroup>\
                 <UsingTask TaskName=\"$(At)(Nothing)\" TaskFactory=\"RoslynCodeTaskFactory\" \
                 AssemblyFile=\"y.dll\"><Task>x</Task></UsingTask>"
            ),
            true,
            Some(Possible),
        ),
        // A function standing alone that returns a boolean the walk does not
        // fold: a flag MSBuild reads, whichever it is.
        (
            inline_task(
                "",
                "<ParameterGroup><A Required=\"$([System.String]::IsNullOrWhiteSpace('é'))\" /></ParameterGroup><Task>x</Task>",
            ),
            false,
            None,
        ),
        (
            inline_task(
                "",
                "<Task Evaluate=\"$([System.String]::IsNullOrWhiteSpace('é'))\">x</Task>",
            ),
            false,
            None,
        ),
        // A value the walk does not hold for certain (a toolset's directory)
        // before a refusal.
        (
            "<UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" \
             AssemblyFile=\"$(MSBuildToolsPath)\\Microsoft.Build.Tasks.Core.dll\">\
             <Task Evaluate=\"off\">x</Task></UsingTask>"
                .to_owned(),
            true,
            Some(Certain),
        ),
        // An earlier task MSBuild may refuse, on a value the walk doubts and
        // takes (`F` is `first`, or empty), before a later refusal.
        (
            format!(
                "<PropertyGroup><F>first</F><F Condition=\"{UNDECIDED_TRUE}\"></F></PropertyGroup>\
                 <UsingTask TaskName=\"$(F)\" AssemblyFile=\"y.dll\" />\
                 <UsingTask TaskName=\"Y\" AssemblyFile=\"$(Missing)\" />"
            ),
            true,
            Some(Certain),
        ),
        // A name with literal text that MSBuild may fail to expand (`T` may
        // hold a transform that throws on `Input`), before a refusal.
        (
            format!(
                "<PropertyGroup><T>y</T><T Condition=\"{UNDECIDED_TRUE}\">@(Input->Substring(4))</T>\
                 </PropertyGroup><UsingTask TaskName=\"Prefix$(T)\" AssemblyFile=\"$(Missing)\" />"
            ),
            true,
            Some(Certain),
        ),
        // A body MSBuild does not expand, its `Evaluate` certainly false: a
        // throw in it (`P` is `a`) is none of MSBuild's. Expanded, it is.
        (
            format!(
                "<PropertyGroup><P>a</P></PropertyGroup>{}",
                inline_task("", "<Task Evaluate=\"false$(Missing)\">$(P[9])</Task>")
            ),
            false,
            None,
        ),
        (
            format!(
                "<PropertyGroup><P>a</P></PropertyGroup>{}",
                inline_task("", "<Task Evaluate=\"true$(Missing)\">$(P[9])</Task>")
            ),
            true,
            Some(Certain),
        ),
        // A later task's illegal condition, after a task MSBuild may stop at.
        (
            format!(
                "{}<UsingTask TaskName=\"Y\" AssemblyFile=\"y.dll\" Condition=\"1\" />",
                inline_task(
                    "",
                    "<ParameterGroup><A ParameterType=\"Nope.Type\" /></ParameterGroup><Task>x</Task>"
                ),
            ),
            true,
            Some(Certain),
        ),
        // A task MSBuild may skip before a later refusal.
        (
            format!(
                "{}{}",
                inline_task(&format!(" Condition=\"{UNDECIDED_TRUE}\""), "<Task>x</Task>"),
                inline_task("", "<Task Evaluate=\"off\">x</Task>").replace("\"X\"", "\"Y\""),
            ),
            true,
            Some(Certain),
        ),
        // A padded reference, which MSBuild expands to empty, and the walk
        // does not model: a decline.
        (
            format!(
                "<PropertyGroup><Flag>true</Flag></PropertyGroup>{}",
                inline_task(
                    "",
                    "<ParameterGroup><A Required=\"$( Flag)\" /></ParameterGroup><Task>x</Task>"
                )
            ),
            true,
            Some(Possible),
        ),
        // A value whose expansion holds `$(`: MSBuild does not expand it
        // again, so `$(Dollar)(Bool)` is the text `$(Bool)`, no boolean.
        (
            format!(
                "<PropertyGroup><Dollar>$</Dollar><Bool>true</Bool></PropertyGroup>{}",
                inline_task(
                    "",
                    "<ParameterGroup><A Required=\"$(Dollar)(Bool)\" /></ParameterGroup><Task>x</Task>"
                )
            ),
            true,
            Some(Certain),
        ),
        // Two parameters spelt alike: the loader's refusal, and no registry
        // collision besides (every certain diagnostic is graded alone).
        (
            inline_task("", "<ParameterGroup><A /><A /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Certain),
        ),
        // `Evaluate` written empty reads as absent, `true`: the body is
        // expanded, and its throw (`P` is `a`) is certain.
        (
            format!(
                "<PropertyGroup><P>a</P></PropertyGroup>{}",
                inline_task("", "<Task Evaluate=\"\">$(P[9])</Task>")
            ),
            true,
            Some(Certain),
        ),
        // A name written empty is the loader's refusal alone, with no
        // registration refusal besides (each certain one is graded alone,
        // replaying the attribute as written).
        (
            "<UsingTask TaskName=\"\" AssemblyFile=\"y.dll\" />".to_owned(),
            true,
            Some(Certain),
        ),
        (
            inline_task("", "<Task>x</Task>").replace(" TaskFactory=\"RoslynCodeTaskFactory\"", ""),
            true,
            Some(Certain),
        ),
        // A long task name, which each refusal of its parameters names: kept
        // bounded.
        (
            format!(
                "<UsingTask TaskName=\"{}\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
                 <ParameterGroup><A Required=\"bad\" /><B Required=\"bad\" /></ParameterGroup>\
                 <Task>x</Task></UsingTask>",
                "N".repeat(1000)
            ),
            true,
            Some(Certain),
        ),
        // A value that reads the project's own name: graded alone at the same
        // path.
        (
            "<UsingTask TaskName=\"$(MSBuildProjectName.TrimStart('Demo'))\" AssemblyFile=\"y.dll\" />"
                .to_owned(),
            true,
            Some(Certain),
        ),
        // A refusal that rests on a write in the document (`R` is `x`, so
        // the flag is `xtrue`): graded alone with that write kept.
        (
            format!(
                "<PropertyGroup><R>x</R></PropertyGroup>{}",
                inline_task(
                    "",
                    "<ParameterGroup><A Required=\"$(R)true\" /></ParameterGroup><Task>x</Task>"
                )
            ),
            true,
            Some(Certain),
        ),
        // Names the loader refuses alone (MSB5016 for the dot): no registry
        // collision besides, which renaming one would not fix.
        (
            inline_task("", "<ParameterGroup><A.b /><a.b /></ParameterGroup><Task>x</Task>"),
            true,
            Some(Certain),
        ),
        // Long names one to the registry: kept bounded.
        (
            inline_task(
                "",
                &format!(
                    "<ParameterGroup><{0}a /><{0}A /></ParameterGroup><Task>x</Task>",
                    "N".repeat(1000)
                ),
            ),
            true,
            Some(Certain),
        ),
        // A child the loader does not take, where no parse configuration can
        // have it skipped
        // ([`a_child_a_parse_configuration_may_skip_needs_no_certain_factory`]).
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\"><Extension /></UsingTask>".to_owned(),
            true,
            Some(Certain),
        ),
    ];
    let mut oracle = Oracle::spawn();
    for (body, rejects, claim) in rows {
        let graded = grade(&mut oracle, "", &body, Doubt::None);
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

/// The registration expands each attribute it reads once, for its throws and
/// its rules alike (`rejection::registration_expansion`): five attributes,
/// five expansions.
#[test]
fn attributes_no_rule_judges_are_expanded_once() {
    let xml = "<Project><UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Runtime=\"NET\" \
               Architecture=\"x64\" Override=\"true\" /></Project>";
    let (_, costs) = borzoi_msbuild::test_support::count_walk_costs(|| {
        borzoi_msbuild::parse_fsproj(
            &borzoi_msbuild::ProjectFile::buffer(std::path::Path::new("/p/p.fsproj"), xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("well-formed")
    });
    assert_eq!(costs.registration_expansions, 5, "{costs:?}");
}

/// A `<UsingTask>` whose child is one the loader does not take, beside a
/// `Directory.Parse.config`, which a newer MSBuild may read and skip the
/// child by: an unknown element, or a `<Task>` under a prefix, which the
/// loader reads by its name as written (`ext:Task` is no `Task`). Skipped,
/// the task has no child, needs no task factory, and has no body whose
/// `Evaluate` it reads, so the walk claims neither the loader's refusal nor
/// the registration's for certain. SDK 10 reads no such file, and rejects.
#[test]
fn a_child_a_parse_configuration_may_skip_needs_no_certain_factory() {
    let mut oracle = Oracle::spawn();
    for using_task in [
        "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\"><Extension /></UsingTask>".to_owned(),
        format!(
            "<UsingTask {INLINE}><ext:Task xmlns:ext=\"urn:x\" Evaluate=\"off\">x</ext:Task>\
             </UsingTask>"
        ),
        "<ext:UsingTask xmlns:ext=\"urn:x\" TaskName=\"$(Missing)\" AssemblyFile=\"y.dll\" />"
            .to_owned(),
    ] {
        let tmp = tempfile::TempDir::new().unwrap();
        let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
        std::fs::write(dir.join("Directory.Parse.config"), "<Configuration />").unwrap();
        let project_path = dir.join("Demo.fsproj");
        let xml = format!(
            "<Project>{using_task}<PropertyGroup><After>ok</After></PropertyGroup></Project>"
        );
        std::fs::write(&project_path, &xml).unwrap();
        let code = oracle
            .design_time_rejection_code(&xml, &project_path)
            .expect("MSBuild's evaluation fails by no other exception");
        assert_eq!(code.as_deref(), Some("MSB4067"), "{xml}");
        let parsed = common::parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let rejection = parsed.rejection.expect("the walk claims the rejection");
        assert_eq!(
            rejection.certainty,
            RejectionCertainty::Possible,
            "{xml}\n{rejection:#?}"
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
    let rejection = parsed.rejection.expect("the walk claims the rejection");
    assert_eq!(rejection.certainty, RejectionCertainty::Certain, "{xml}");
    assert_eq!(
        rejection.cause,
        borzoi_msbuild::RejectionCause::UsingTaskParameterCollision {
            task: "X".into(),
            first: "A".into(),
            second: "a".into(),
        },
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
    /// Rejections resting on a value the walk holds none of, or on a doubted
    /// write's (#1051).
    unheld_value: usize,
}

/// `cases` documents from `rng`, each graded ([`grade`]).
fn registration_sweep(seed: u64, cases: usize) -> Census {
    let census = coverage::open(file!(), "using_task_registration", EXCLUDED);
    let excluded: BTreeSet<Dimension> = EXCLUDED.iter().map(|(d, _)| *d).collect();
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut tally = Census::default();
    // Every entry of the alphabet once, as a witness, before the draws.
    let mut witnesses = value::alphabet().entries().iter();
    while tally.cases < cases {
        let place = *rng.pick(PLACES);
        let source = *rng.pick(SOURCES);
        let plain = *rng.pick(PLAIN);
        // What a doubted write puts first: half the time the value itself.
        let other = if rng.next().is_multiple_of(2) {
            None
        } else {
            Some(*rng.pick(PLAIN))
        };
        let entry = witnesses
            .next()
            .or_else(|| value::alphabet().sample(rng.next()));
        let drawn = match entry {
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
        let other = other.unwrap_or(&drawn.value);
        let doubt = if matches!(source, Source::Doubted) && other != drawn.value {
            Doubt::Differs
        } else {
            Doubt::None
        };
        let (writes, body) = document(place, &drawn.value, source, other);
        tally.cases += 1;
        let graded = grade(&mut oracle, &writes, &body, doubt);
        tally.msbuild_rejects += usize::from(graded.msbuild_rejects);
        if graded.msbuild_rejects && graded.walk.is_none() {
            // `grade` let this pass only on a value the walk holds none of,
            // or a doubted write's. Shown to rest on that value: through a
            // property the walk holds it in, where it does, MSBuild rejects
            // and the walk claims.
            let (writes, body) = document(place, &drawn.value, Source::Certain, "");
            let certain = grade(&mut oracle, &writes, &body, Doubt::None);
            assert!(
                certain.v_unheld || (certain.msbuild_rejects && certain.walk.is_some()),
                "MSBuild rejects a value the walk does not hold, and not the value through a \
                 certain property: {body}"
            );
            tally.unheld_value += 1;
            census.reached(
                &drawn.hostile,
                match doubt {
                    Doubt::Differs => "rejects-on-a-doubted-value",
                    Doubt::None => "rejects-on-an-unheld-value",
                },
            );
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

/// Values a whole `<UsingTask>` draws besides [`PLAIN`]'s: an expression
/// MSBuild throws on (`P` is `a`), one it computes and the walk does not, a
/// boolean it does not fold, a name that expands to empty, a metadatum it
/// leaves as written, and a name the walk doubts that holds `@`, which may
/// form an item list with the text after it.
const SPECIAL: &[&str] = &[
    "$(P[9])",
    "$([System.String]::IsNullOrWhiteSpace('é'))",
    "$(At)(Nothing)",
    "$(At)",
    "$(F)",
    "Prefix$(T)",
    "false$(Missing)",
    "$( P)",
    "$(D)(B)",
    "$([System.Runtime.InteropServices.RuntimeInformation]::ProcessArchitecture)",
    "$(Empty)",
    "%(M)",
];

/// The `ParameterType`s a parameter draws besides any value.
const TYPES: &[&str] = &[
    "System.String",
    "System.Boolean[]",
    "Microsoft.Build.Framework.ITaskItem",
    "System.Object",
    "Nope.Type",
];

/// The `Runtime` and `Architecture` values a task draws besides any value.
const HOSTS: &[&str] = &[
    "CLR4",
    "NET",
    "CurrentRuntime",
    "*",
    "x64",
    "arm64",
    "CurrentArchitecture",
];

/// One value of an attribute, escaped for one.
fn composite_value(rng: &mut SplitMix64) -> String {
    let value = if rng.below(5) == 0 {
        *rng.pick(SPECIAL)
    } else {
        *rng.pick(PLAIN)
    };
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('"', "&quot;")
}

/// `value` most of the time, else a drawn one.
fn mostly(rng: &mut SplitMix64, value: &str) -> String {
    if rng.below(4) == 0 {
        composite_value(rng)
    } else {
        value.to_owned()
    }
}

/// A whole `<UsingTask>` from `rng`: every attribute MSBuild registers, and
/// its children in either order, each value drawn, so that the steps of the
/// registration meet in every order and combination: a refusal after one
/// MSBuild may stop at, a body that is not the last child, parameters that
/// are not the first, names that fold to one.
fn composite_document(rng: &mut SplitMix64) -> String {
    let mut children = Vec::new();
    if rng.below(3) != 0 {
        let mut names = vec!["A", "B", "a", "A"];
        let count = 1 + rng.below(3);
        let mut parameters = String::new();
        for _ in 0..count {
            let name = names.remove(rng.below(names.len()));
            let mut attributes = String::new();
            if rng.below(2) == 0 {
                let ty = if rng.below(2) == 0 {
                    (*rng.pick(TYPES)).to_owned()
                } else {
                    composite_value(rng)
                };
                attributes += &format!(" ParameterType=\"{ty}\"");
            }
            for flag in ["Output", "Required"] {
                if rng.below(2) == 0 {
                    attributes += &format!(" {flag}=\"{}\"", mostly(rng, "true"));
                }
            }
            parameters += &format!("<{name}{attributes} />");
        }
        children.push(format!("<ParameterGroup>{parameters}</ParameterGroup>"));
    }
    if rng.below(3) != 0 {
        let evaluate = if rng.below(2) == 0 {
            format!(" Evaluate=\"{}\"", composite_value(rng))
        } else {
            String::new()
        };
        let text = if rng.below(4) == 0 {
            composite_value(rng)
        } else {
            "x".to_owned()
        };
        children.push(format!("<Task{evaluate}>{text}</Task>"));
    }
    if rng.below(3) == 0 {
        children.reverse();
    }
    let mut attributes = format!(" TaskName=\"{}\"", mostly(rng, "X"));
    let factory = if children.is_empty() {
        (rng.below(3) == 0).then(|| composite_value(rng))
    } else {
        Some(mostly(rng, "RoslynCodeTaskFactory"))
    };
    if let Some(factory) = factory {
        attributes += &format!(" TaskFactory=\"{factory}\"");
    }
    let assembly = if rng.below(2) == 0 {
        "AssemblyFile"
    } else {
        "AssemblyName"
    };
    attributes += &format!(" {assembly}=\"{}\"", mostly(rng, "y.dll"));
    for name in ["Runtime", "Architecture"] {
        if rng.below(6) == 0 {
            let value = if rng.below(2) == 0 {
                (*rng.pick(HOSTS)).to_owned()
            } else {
                composite_value(rng)
            };
            attributes += &format!(" {name}=\"{value}\"");
        }
    }
    if rng.below(6) == 0 {
        attributes += &format!(" Override=\"{}\"", composite_value(rng));
    }
    if rng.below(4) == 0 {
        attributes += &format!(" Condition=\"{}\"", rng.pick(CONDITIONS));
    }
    format!("<UsingTask{attributes}>{}</UsingTask>", children.concat())
}

/// The conditions a whole `<UsingTask>` draws: true, false, undecided by the
/// walk, illegal, and one that throws.
const CONDITIONS: &[&str] = &["true", "false", "'É' == 'é'", "1", "'$(P[9])' == ''"];

/// [`COMPOSITE_WRITES`] with each doubted name holding only the value the walk
/// holds.
const COMPOSITE_HELD: &str = "<P>a</P><At>@</At><F>first</F><T>y</T><D>$</D><B>true</B>";

/// The property writes every [`composite_sweep`] document makes.
const COMPOSITE_WRITES: &str = "<P>a</P><At>@</At><At Condition=\"'É' == 'é'\">@</At>\
                                <F>first</F><F Condition=\"'É' == 'é'\"></F>\
                                <T>y</T><T Condition=\"'É' == 'é'\">@(Input->Substring(4))</T>\
                                <D>$</D><B>true</B>";

/// `cases` documents of one or two whole `<UsingTask>`s from `seed`
/// ([`composite_document`]), each graded ([`grade`]): a certain rejection
/// must be MSBuild's, and name a construct MSBuild refuses alone.
fn composite_sweep(seed: u64, cases: usize) -> Census {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut tally = Census::default();
    for _ in 0..cases {
        let body: String = (0..1 + rng.below(2))
            .map(|_| composite_document(&mut rng))
            .collect();
        tally.cases += 1;
        // `F` and `T` are written under an undecided gate with a value other
        // than the one the walk holds: a rejection resting on MSBuild's is
        // the #1051 gap, which `grade` lets pass only where one is read.
        let doubt = if body.contains("$(F)") || body.contains("$(T)") {
            Doubt::Differs
        } else {
            Doubt::None
        };
        let graded = grade(&mut oracle, COMPOSITE_WRITES, &body, doubt);
        if graded.msbuild_rejects && graded.walk.is_none() {
            // Shown to rest on the doubted values: with `F` and `T` holding
            // only what the walk holds, MSBuild evaluates, or the walk claims
            // its rejection (`grade`).
            grade(&mut oracle, COMPOSITE_HELD, &body, Doubt::None);
            tally.unheld_value += 1;
        }
        tally.msbuild_rejects += usize::from(graded.msbuild_rejects);
        match graded.walk {
            Some(RejectionCertainty::Certain) => tally.certain += 1,
            Some(RejectionCertainty::Possible) => tally.possible += 1,
            None => {}
        }
    }
    tally
}

/// [`composite_sweep`] at a fixed seed.
#[test]
fn composite_sweep_fixed_seed() {
    let tally = composite_sweep(0x1099_c0de, 600);
    eprintln!("composite sweep: {tally:?}");
    assert!(tally.msbuild_rejects >= 100, "{tally:?}");
    assert!(tally.certain >= 50, "{tally:?}");
    assert!(tally.cases - tally.msbuild_rejects >= 50, "{tally:?}");
}

/// The fresh-seed twin of [`composite_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run with --ignored"]
fn composite_sweep_soak() {
    let (seed, cases) = common::soak_parameters("using-task composite", 3000);
    composite_sweep(seed, cases);
}
