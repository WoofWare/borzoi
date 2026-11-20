//! `define_constants_uncertain` and content the walk did not enter (#843,
//! #862).
//!
//! Content the walk could not see may write `DefineConstants`, or import a
//! user file that does. No later read need see it: the hidden write may be the
//! last one, and a `<DefineConstants>$(DefineConstants);B</DefineConstants>`
//! append's read of its own name is exempt from doubting the define set. So
//! once the walk has passed such content the define set is never certain, in
//! an SDK file as in a user's, and the exemption ends there too. Each shape's MSBuild value is in its test's docs (dotnet
//! 10.0.401); `tests/fsproj_sdk_import_graph_generative_diff.rs` grades the
//! define set against the oracle on generated import graphs.

use super::*;
use tempfile::TempDir;

/// A gate MSBuild takes and the walk cannot decide: it computes no property
/// function.
const UNDECIDED: &str = "'É' == 'é'";

/// Parse `proj/Demo.fsproj`, whose body is `body`, against the SDK `MySdk`
/// with the given `Sdk.props` and `Sdk.targets`. `user` are further files,
/// relative to `proj`, and `sdk_extra` files beside the SDK's two.
fn parse_project(
    sdk_props: &str,
    sdk_targets: &str,
    sdk_extra: &[(&str, &str)],
    user: &[(&str, &str)],
    body: &str,
) -> ParsedProject {
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) =
        write_synthetic_sdk_with_extras(tmp.path(), "MySdk", sdk_props, sdk_targets, sdk_extra);
    let proj = tmp.path().join("proj");
    for (name, text) in user {
        write_at(&proj, name, text);
    }
    let project_path = write_at(
        &proj,
        "Demo.fsproj",
        &format!("<Project Sdk=\"MySdk\">\n{body}\n</Project>"),
    );
    parse_file_with_sdk(&project_path, |name| {
        if name == "MySdk" {
            Ok(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            })
        } else {
            Err(SdkResolveError::NotFound)
        }
    })
}

/// Assert the walk hid content and withdrew the define set for it, with a
/// cause naming the hidden content.
#[track_caller]
fn assert_withdrawn(parsed: &ParsedProject, msbuild: &str) {
    assert!(
        parsed.hidden_content.is_some(),
        "the shape must hide content from the walk"
    );
    assert!(
        parsed.define_constants_uncertain,
        "MSBuild's DefineConstants is `{msbuild}`; the walk published {:?} as certain",
        parsed.define_constants
    );
    assert!(
        parsed
            .define_constants_uncertainties
            .iter()
            .any(|cause| matches!(
                cause.kind,
                DefineConstantsUncertaintyCauseKind::HiddenContent(_)
            )),
        "no cause names the hidden content: {:?}",
        parsed.define_constants_uncertainties
    );
}

const APPEND_FOO: &str = "<Project><PropertyGroup><DefineConstants>$(DefineConstants);FOO</DefineConstants></PropertyGroup></Project>";

/// #843: a user file imported under a gate the walk cannot decide defines `A`,
/// and the body appends `B` to it. MSBuild's value is `A;B`; the self-append's
/// read of `$(DefineConstants)` must not let the walk publish `["B"]`.
#[test]
fn an_undecided_user_import_hides_the_define_the_body_appends_to() {
    let tmp = TempDir::new().unwrap();
    write_at(
        tmp.path(),
        "Other.props",
        "<Project><PropertyGroup><DefineConstants>A</DefineConstants></PropertyGroup></Project>",
    );
    let source = format!(
        r#"<Project>
  <Import Project="Other.props" Condition="{UNDECIDED}" />
  <PropertyGroup><DefineConstants>$(DefineConstants);B</DefineConstants></PropertyGroup>
</Project>"#
    );
    let project_path = write_at(tmp.path(), "Demo.fsproj", &source);
    let parsed = parse(&project_path, &source);
    assert_withdrawn(&parsed, "A;B");
    // The append's own read doubts the set too: it is not the SDK-free view
    // once hidden content may have written the name.
    assert!(
        parsed
            .define_constants_uncertainties
            .iter()
            .any(|cause| cause.kind
                == DefineConstantsUncertaintyCauseKind::Diagnostic(
                    DiagnosticKind::UndefinedProperty {
                        name: "DefineConstants".to_string()
                    }
                )),
        "the append's read was exempted: {:?}",
        parsed.define_constants_uncertainties
    );
}

/// The environment names `DefineConstants` in two spellings with different
/// values, so promotion binds neither, and the walk reads it as undefined.
/// MSBuild holds one of them: with `DefineConstants=A` and
/// `DEFINECONSTANTS=C`, its value is `A;B`. The append's read is not the
/// SDK-free view, so it doubts the set.
#[test]
fn an_append_to_a_define_the_environment_holds_unseen_makes_defines_uncertain() {
    let tmp = TempDir::new().unwrap();
    let source = "<Project><PropertyGroup><DefineConstants>$(DefineConstants);B</DefineConstants></PropertyGroup></Project>";
    let project_path = canon(&write_at(tmp.path(), "Demo.fsproj", source));
    let environment: HashMap<String, String> = [("DefineConstants", "A"), ("DEFINECONSTANTS", "C")]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    let parsed = sound(&project_path, |through| {
        through
            .evaluate(
                source,
                &project_path,
                &HashMap::new(),
                &environment,
                None,
                None,
            )
            .expect("well-formed XML parses")
    });
    assert!(
        parsed.define_constants_uncertain,
        "MSBuild's DefineConstants is `A;B`; the walk published {:?} as certain",
        parsed.define_constants
    );
}

/// #862: the hidden user file is the last writer, so no later read sees what
/// it wrote. MSBuild's value is `;FOO`.
#[test]
fn an_undecided_user_import_that_appends_a_define_makes_defines_uncertain() {
    let tmp = TempDir::new().unwrap();
    write_at(tmp.path(), "d.props", APPEND_FOO);
    let source = format!(
        r#"<Project>
  <Import Project="$(MSBuildProjectDirectory)/d.props" Condition="{UNDECIDED}" />
</Project>"#
    );
    let project_path = write_at(tmp.path(), "Demo.fsproj", &source);
    let parsed = parse(&project_path, &source);
    assert_withdrawn(&parsed, ";FOO");
}

/// #862 through the SDK: `Sdk.props` imports the user's file under the
/// undecided gate. MSBuild's value is `;FOO`. That the hidden import sits in an
/// SDK file says nothing of the file it reaches.
#[test]
fn an_undecided_sdk_import_of_a_user_file_makes_defines_uncertain() {
    let parsed = parse_project(
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildProjectDirectory)/d.props" Condition="{UNDECIDED}" />
</Project>"#
        ),
        "<Project/>",
        &[],
        &[("d.props", APPEND_FOO)],
        "",
    );
    assert_withdrawn(&parsed, ";FOO");
}

/// The same after the body, from `Sdk.targets`, with the body's own append:
/// MSBuild's value is `;B;FOO`.
#[test]
fn an_undecided_sdk_import_after_the_body_makes_defines_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildProjectDirectory)/d.props" Condition="{UNDECIDED}" />
</Project>"#
        ),
        &[],
        &[("d.props", APPEND_FOO)],
        "<PropertyGroup><DefineConstants>$(DefineConstants);B</DefineConstants></PropertyGroup>",
    );
    assert_withdrawn(&parsed, ";B;FOO");
}

/// Hidden content inside the SDK withdraws the set too: a file beside the
/// SDK's own may import a user file, so where the hidden import sits proves
/// nothing about what it reaches. Here it writes the define itself, and
/// MSBuild's value is `;FOO`.
#[test]
fn an_undecided_import_of_an_sdk_file_makes_defines_uncertain() {
    let parsed = parse_project(
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildThisFileDirectory)Via.props" Condition="{UNDECIDED}" />
</Project>"#
        ),
        "<Project/>",
        &[("Via.props", APPEND_FOO)],
        &[],
        "",
    );
    assert_withdrawn(&parsed, ";FOO");
}

/// The same with the gate on an `<ImportGroup>`.
#[test]
fn an_undecided_import_group_makes_defines_uncertain() {
    let parsed = parse_project(
        &format!(
            r#"<Project>
  <ImportGroup Condition="{UNDECIDED}">
    <Import Project="$(MSBuildProjectDirectory)/d.props" />
  </ImportGroup>
</Project>"#
        ),
        "<Project/>",
        &[],
        &[("d.props", APPEND_FOO)],
        "",
    );
    assert_withdrawn(&parsed, ";FOO");
}

/// An import the walk cannot follow at all (a missing SDK) hides content as
/// surely as an undecided gate.
#[test]
fn an_unresolved_sdk_import_makes_defines_uncertain() {
    let parsed = parse_project(
        r#"<Project><Import Project="Sdk.props" Sdk="Missing" /></Project>"#,
        "<Project/>",
        &[],
        &[],
        "<PropertyGroup><DefineConstants>$(DefineConstants);B</DefineConstants></PropertyGroup>",
    );
    assert!(parsed.hidden_content.is_some());
    assert!(
        parsed.define_constants_uncertain,
        "the missing SDK may define anything; the walk published {:?} as certain",
        parsed.define_constants
    );
}

/// The append idiom stays certain when the walk saw everything: the self-read
/// of an undefined `DefineConstants` is the project's own view, without the
/// defines the SDK adds in targets (`ParsedProject::define_constants_uncertain`).
/// MSBuild's evaluated value is `;B`.
#[test]
fn the_append_idiom_stays_certain_when_nothing_is_hidden() {
    let parsed = parse_project(
        "<Project/>",
        "<Project/>",
        &[],
        &[],
        "<PropertyGroup><DefineConstants>$(DefineConstants);B</DefineConstants></PropertyGroup>",
    );
    assert!(parsed.hidden_content.is_none());
    assert!(
        !parsed.define_constants_uncertain,
        "{:?}",
        parsed.define_constants_uncertainties
    );
    assert_eq!(parsed.define_constants, vec!["B".to_string()]);
}
