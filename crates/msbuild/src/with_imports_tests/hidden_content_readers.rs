//! What the walk publishes once it has passed content it could not see: a
//! value bound before that content may have been rewritten there (#792), and
//! a write made inside an import followed on a gate the walk could not decide
//! may not happen (#791). Neither is published as the real build's.

use super::*;
use crate::{DefineConstantsUncertaintyCauseKind, ItemMetadataValue, PropertyRead};

/// A condition MSBuild evaluates to `true` and the walk cannot evaluate.
const UNDECIDABLE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";

fn hidden_import() -> String {
    format!("  <Import Project=\"Hidden.props\" Condition=\"{UNDECIDABLE}\" />\n")
}

fn parse(dir: &Path, body: &str) -> ParsedProject {
    // The hidden import names a file that exists: one that did not would be
    // a possible rejection, which withdraws every value on its own account.
    write_at(dir, "Hidden.props", "<Project />\n");
    let project = write_at(dir, "p.fsproj", &format!("<Project>\n{body}</Project>\n"));
    parse_file_std(&project)
}

fn defines_hidden(parsed: &ParsedProject) -> bool {
    parsed.define_constants_uncertainties.iter().any(|cause| {
        matches!(
            cause.kind,
            DefineConstantsUncertaintyCauseKind::HiddenContent(_)
        )
    })
}

/// `Hidden.props` may rewrite every name bound before it, so each reads as
/// untrusted, as does a copy made after it; a literal written after it is the
/// real build's.
#[test]
fn a_value_bound_before_hidden_content_is_published_untrusted() {
    let tmp = tempfile::tempdir().unwrap();
    let parsed = parse(
        tmp.path(),
        &format!(
            "  <PropertyGroup>\n    <Kept>1</Kept>\n    <AssemblyName>Mine</AssemblyName>\n    \
             <DefineConstants>A</DefineConstants>\n  </PropertyGroup>\n{}  <PropertyGroup>\n    \
             <Copy>$(Kept)x</Copy>\n    <Fresh>2</Fresh>\n  </PropertyGroup>\n",
            hidden_import()
        ),
    );
    for name in ["Kept", "Copy", "AssemblyName", "DefineConstants"] {
        assert!(
            matches!(parsed.property(name), PropertyRead::Untrusted(_)),
            "{name}: {:?}",
            parsed.property(name)
        );
    }
    assert_eq!(parsed.property("Fresh"), PropertyRead::Value("2".into()));
    assert_eq!(parsed.target_name, ItemMetadataValue::Unknown);
    assert!(parsed.define_constants_uncertain);
    assert!(defines_hidden(&parsed));
}

/// A name the walk holds unset after hidden content may be defined there: the
/// output name and the `#if` symbols rest on such names.
#[test]
fn a_name_unset_after_hidden_content_is_not_published_as_unset() {
    let tmp = tempfile::tempdir().unwrap();
    let parsed = parse(tmp.path(), &hidden_import());
    assert_eq!(parsed.target_name, ItemMetadataValue::Unknown);
    assert!(parsed.define_constants_uncertain);
    assert!(defines_hidden(&parsed));
}

/// A literal written after everything hidden is the real build's value,
/// whatever the hidden content wrote. (The define set is withdrawn by the
/// hidden content itself, wherever the write is: `defines_uncertain`.)
#[test]
fn a_literal_written_after_hidden_content_is_published() {
    let tmp = tempfile::tempdir().unwrap();
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <PropertyGroup>\n    <TargetName>Out</TargetName>\n    \
             <Fresh>A</Fresh>\n  </PropertyGroup>\n",
            hidden_import()
        ),
    );
    assert_eq!(parsed.target_name, ItemMetadataValue::known("Out"));
    assert_eq!(parsed.property("Fresh"), PropertyRead::Value("A".into()));
}

/// After hidden content an unset `$(Gate)` is not exactly unset, so the import
/// gated on it is one MSBuild may skip: what the followed file writes is not
/// published, nested groups and conditions included, while a later literal
/// overwrite is.
#[test]
fn a_write_inside_an_import_followed_on_an_undecided_gate_is_untrusted() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(
        tmp.path(),
        "Followed.props",
        "<Project>\n  <PropertyGroup>\n    <FromFollowed>1</FromFollowed>\n    \
         <Overwritten>followed</Overwritten>\n  </PropertyGroup>\n  \
         <PropertyGroup Condition=\"'$(FromFollowed)' == '1'\">\n    \
         <Nested>1</Nested>\n  </PropertyGroup>\n</Project>\n",
    );
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <Import Project=\"Followed.props\" Condition=\"'$(Gate)' == ''\" />\n  \
             <PropertyGroup>\n    <Overwritten>body</Overwritten>\n  </PropertyGroup>\n",
            hidden_import()
        ),
    );
    assert_eq!(
        parsed.properties.get("FromFollowed").map(String::as_str),
        Some("1"),
        "the walk follows the import"
    );
    for name in ["FromFollowed", "Nested"] {
        assert!(
            matches!(parsed.property(name), PropertyRead::Untrusted(_)),
            "{name}: {:?}",
            parsed.property(name)
        );
    }
    assert_eq!(
        parsed.property("Overwritten"),
        PropertyRead::Value("body".into())
    );
}

const INNER: &str = "<Project>\n  <PropertyGroup>\n    <DefineConstants>inner</DefineConstants>\n    \
                     <FromInner>1</FromInner>\n  </PropertyGroup>\n</Project>\n";

/// The followed file is walked as any other, so an import it makes through a
/// property it wrote is followed, and registers as one MSBuild may not make.
/// A later import of that file is then no certain duplicate, and no certain
/// import either: what it writes is not published.
#[test]
fn an_import_through_a_property_the_followed_file_wrote_is_followed_and_doubted() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Inner.props", INNER);
    write_at(
        tmp.path(),
        "Mid.props",
        "<Project>\n  <PropertyGroup>\n    <P>Inner.props</P>\n  </PropertyGroup>\n  \
         <Import Project=\"$(P)\" />\n</Project>\n",
    );
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <Import Project=\"Mid.props\" Condition=\"'$(Gate)' == ''\" />\n  \
             <PropertyGroup>\n    <DefineConstants>middle</DefineConstants>\n  \
             </PropertyGroup>\n  <Import Project=\"Inner.props\" />\n",
            hidden_import()
        ),
    );
    assert!(parsed.define_constants_uncertain);
    for name in ["DefineConstants", "FromInner", "P"] {
        assert!(
            matches!(parsed.property(name), PropertyRead::Untrusted(_)),
            "{name}: {:?}",
            parsed.property(name)
        );
    }
}

/// An import made inside one MSBuild may skip is not certainly made, so a
/// later import of the same file is not certainly a duplicate: MSBuild may
/// make it there, after the body's write.
#[test]
fn an_import_made_inside_a_followed_undecided_import_is_not_a_certain_duplicate() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Inner.props", INNER);
    write_at(
        tmp.path(),
        "Mid.props",
        "<Project>\n  <Import Project=\"Inner.props\" />\n</Project>\n",
    );
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <Import Project=\"Mid.props\" Condition=\"'$(Gate)' == ''\" />\n  \
             <PropertyGroup>\n    <DefineConstants>middle</DefineConstants>\n  \
             </PropertyGroup>\n  <Import Project=\"Inner.props\" />\n",
            hidden_import()
        ),
    );
    assert!(parsed.define_constants_uncertain);
    assert!(
        matches!(
            parsed.property("DefineConstants"),
            PropertyRead::Untrusted(_)
        ),
        "{:?}",
        parsed.property("DefineConstants")
    );
}

/// A file imported behind many undecided gates is walked once, as MSBuild
/// walks it: a value it doubles does not double per import.
#[test]
fn a_file_imported_behind_many_undecided_gates_is_walked_once() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(
        tmp.path(),
        "Double.props",
        "<Project>\n  <PropertyGroup>\n    <D>$(D)$(D)</D>\n  </PropertyGroup>\n</Project>\n",
    );
    let gated = "  <Import Project=\"Double.props\" Condition=\"'$(Gate)' == ''\" />\n".repeat(40);
    let parsed = parse(
        tmp.path(),
        &format!(
            "  <PropertyGroup>\n    <D>x</D>\n  </PropertyGroup>\n{}{gated}  \
             <Import Project=\"Double.props\" />\n",
            hidden_import()
        ),
    );
    assert_eq!(parsed.properties.get("D").map(String::as_str), Some("xx"));
    assert!(matches!(parsed.property("D"), PropertyRead::Untrusted(_)));
}

/// A later import of a file a followed import made may reach files the first
/// did not, so the names the first wrote are not all it could write: nothing
/// decided on a name it leaves unset is published.
#[test]
fn a_later_import_of_a_followed_file_may_reach_files_the_first_did_not() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(
        tmp.path(),
        "Mid.props",
        "<Project>\n  <Import Project=\"$(Child).props\" />\n</Project>\n",
    );
    write_at(
        tmp.path(),
        "a.props",
        "<Project>\n  <PropertyGroup>\n    <A>1</A>\n  </PropertyGroup>\n</Project>\n",
    );
    write_at(
        tmp.path(),
        "b.props",
        "<Project>\n  <PropertyGroup>\n    <Mode>preview</Mode>\n  </PropertyGroup>\n</Project>\n",
    );
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <PropertyGroup>\n    <Child>a</Child>\n  </PropertyGroup>\n  \
             <Import Project=\"Mid.props\" Condition=\"'$(Gate)' == ''\" />\n  \
             <PropertyGroup>\n    <Child>b</Child>\n  </PropertyGroup>\n  \
             <Import Project=\"Mid.props\" />\n  \
             <PropertyGroup>\n    <Result>base</Result>\n  </PropertyGroup>\n  \
             <PropertyGroup Condition=\"'$(Mode)' == 'preview'\">\n    \
             <Result>updated</Result>\n  </PropertyGroup>\n",
            hidden_import()
        ),
    );
    assert!(
        matches!(parsed.property("Result"), PropertyRead::Untrusted(_)),
        "{:?}",
        parsed.property("Result")
    );
}

/// Hidden content may already have imported `Inner.props`, and MSBuild then
/// skips the import after it as a duplicate: what the file writes there is not
/// published, and neither is a name the body wrote that it overwrites (#891).
#[test]
fn an_import_after_hidden_content_may_be_a_duplicate_of_a_hidden_one() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Inner.props", INNER);
    let parsed = parse(
        tmp.path(),
        &format!(
            "{}  <PropertyGroup>\n    <DefineConstants>middle</DefineConstants>\n    \
             <Untouched>1</Untouched>\n  </PropertyGroup>\n  \
             <Import Project=\"Inner.props\" />\n",
            hidden_import()
        ),
    );
    for name in ["DefineConstants", "FromInner"] {
        assert!(
            matches!(parsed.property(name), PropertyRead::Untrusted(_)),
            "{name}: {:?}",
            parsed.property(name)
        );
    }
    assert_eq!(
        parsed.property("Untouched"),
        PropertyRead::Value("1".into()),
        "a name the later import does not write is the body's"
    );
}
