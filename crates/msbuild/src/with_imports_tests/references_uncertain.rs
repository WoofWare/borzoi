//! `project_references_uncertain` and content the walk did not enter (#848).
//!
//! Content the walk could not see may hold a `<ProjectReference Remove=…>` or
//! `Update=…`, import a user file that does, or import a file a later import
//! names again, which MSBuild then skips as a duplicate. So once the walk has
//! passed such content the reference list is never certain, in an SDK file as
//! in a user's: that the hidden import sits in an SDK file says nothing of the
//! file it reaches. The shapes here are graded against MSBuild by
//! `tests/fsproj_sdk_import_graph_generative_diff.rs`.

use super::*;
use tempfile::TempDir;

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

/// A gate MSBuild takes and the walk cannot decide: it computes no property
/// function.
const UNDECIDED: &str = "'É' == 'é'";

const BODY_REFERENCE: &str =
    r#"<ItemGroup><ProjectReference Include="../b/b.fsproj" /></ItemGroup>"#;

/// #848: `Sdk.targets` imports a user file under a gate the walk cannot
/// decide, and the file strips the body's reference. MSBuild has no
/// `ProjectReference`; the walk must not publish `b.fsproj` as certain.
#[test]
fn an_undecided_sdk_import_of_a_user_file_that_removes_a_reference_makes_references_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildProjectDirectory)/strip.targets" Condition="{UNDECIDED}" />
</Project>"#
        ),
        &[],
        &[(
            "strip.targets",
            r#"<Project><ItemGroup><ProjectReference Remove="../b/b.fsproj" /></ItemGroup></Project>"#,
        )],
        BODY_REFERENCE,
    );
    assert!(
        parsed.project_references_uncertain,
        "MSBuild strips b.fsproj; the walk published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// The same through an SDK file: the hidden import is of a file beside the
/// SDK's own, which imports the user's. That the hidden file lies under an SDK
/// root proves nothing about what it reaches.
#[test]
fn an_undecided_import_of_an_sdk_file_that_reaches_a_user_file_makes_references_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildThisFileDirectory)Via.targets" Condition="{UNDECIDED}" />
</Project>"#
        ),
        &[(
            "Via.targets",
            r#"<Project><Import Project="$(MSBuildProjectDirectory)/strip.targets" /></Project>"#,
        )],
        &[(
            "strip.targets",
            r#"<Project><ItemGroup><ProjectReference Remove="../b/b.fsproj" /></ItemGroup></Project>"#,
        )],
        BODY_REFERENCE,
    );
    assert!(
        parsed.project_references_uncertain,
        "MSBuild strips b.fsproj; the walk published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// The same with the gate on an `<ImportGroup>`.
#[test]
fn an_undecided_sdk_import_group_makes_references_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        &format!(
            r#"<Project>
  <ImportGroup Condition="{UNDECIDED}">
    <Import Project="$(MSBuildProjectDirectory)/strip.targets" />
  </ImportGroup>
</Project>"#
        ),
        &[],
        &[(
            "strip.targets",
            r#"<Project><ItemGroup><ProjectReference Remove="../b/b.fsproj" /></ItemGroup></Project>"#,
        )],
        BODY_REFERENCE,
    );
    assert!(
        parsed.project_references_uncertain,
        "MSBuild strips b.fsproj; the walk published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// #819's shape on the reference axis: `Sdk.props` imports `shared.props`
/// under a gate the walk cannot decide, so MSBuild skips the body's later
/// import of it as a duplicate (MSB4011). The body removed the reference
/// `shared.props` declares before that import; MSBuild keeps the reference
/// the hidden import made and the body removed, so it has none, while the
/// walk captures it at the body's import.
#[test]
fn an_import_after_a_hidden_sdk_import_of_its_file_makes_references_uncertain() {
    let parsed = parse_project(
        &format!(
            r#"<Project>
  <Import Project="$(MSBuildProjectDirectory)/shared.props" Condition="{UNDECIDED}" />
</Project>"#
        ),
        "<Project/>",
        &[],
        &[(
            "shared.props",
            r#"<Project><ItemGroup><ProjectReference Include="../c/c.fsproj" /></ItemGroup></Project>"#,
        )],
        r#"<ItemGroup><ProjectReference Remove="../c/c.fsproj" /></ItemGroup>
  <Import Project="$(MSBuildProjectDirectory)/shared.props" />"#,
    );
    assert!(
        parsed.project_references_uncertain,
        "MSBuild skips the body's import of shared.props and has no reference; the walk \
         published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// An SDK import whose path the walk cannot compute is content it did not
/// enter, like one whose gate it could not decide.
#[test]
fn an_unresolved_sdk_import_makes_references_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        r#"<Project>
  <PropertyGroup><Hidden>strip</Hidden></PropertyGroup>
  <Import Project="$(MSBuildProjectDirectory)/$(Hidden.Substring(0)).targets" />
</Project>"#,
        &[],
        &[(
            "strip.targets",
            r#"<Project><ItemGroup><ProjectReference Remove="../b/b.fsproj" /></ItemGroup></Project>"#,
        )],
        BODY_REFERENCE,
    );
    assert!(parsed.hidden_content.is_some());
    assert!(
        parsed.project_references_uncertain,
        "the import the walk could not resolve may strip b.fsproj; the walk published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// A `<Choose>` MSBuild refuses to load, in an SDK file: there is no build for
/// the captured list to describe.
#[test]
fn a_malformed_choose_in_the_sdk_makes_references_uncertain() {
    let parsed = parse_project(
        "<Project/>",
        r#"<Project>
  <Choose>
    <Otherwise />
    <When Condition="true" />
  </Choose>
</Project>"#,
        &[],
        &[],
        BODY_REFERENCE,
    );
    assert!(
        parsed.project_references_uncertain,
        "MSBuild rejects the project; the walk published {:?}",
        paths_of(&parsed.project_references)
    );
}

/// The other side: an SDK whose imports the walk decides and follows keeps the
/// list certain, so the rule withdraws only what hidden content could change.
#[test]
fn decided_sdk_imports_keep_references_certain() {
    let parsed = parse_project(
        r#"<Project>
  <PropertyGroup><Open>true</Open></PropertyGroup>
  <Import Project="$(MSBuildThisFileDirectory)Inner.props" Condition="'$(Open)' == 'true'" />
  <Import Project="$(MSBuildThisFileDirectory)Missing.props" Condition="Exists('$(MSBuildThisFileDirectory)Missing.props')" />
</Project>"#,
        "<Project/>",
        &[("Inner.props", "<Project/>")],
        &[],
        BODY_REFERENCE,
    );
    assert!(
        parsed.hidden_content.is_none(),
        "{:?}",
        parsed.hidden_content
    );
    assert!(
        !parsed.project_references_uncertain,
        "diagnostics: {:?}",
        parsed.diagnostics
    );
    assert_eq!(parsed.project_references.len(), 1);
}
