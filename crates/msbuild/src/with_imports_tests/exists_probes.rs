//! `Exists()` and `GetDirectoryNameOfFileAbove` as MSBuild answers them: the
//! directory a condition resolves against, and .NET's existence rules (a
//! dangling symlink exists, `..` collapses as text). `tests/condition_diff.rs`
//! and `tests/fsproj_file_above_diff.rs` grade the rules against MSBuild; these
//! hold the walk to them with the read-set soundness sweep over symlinks.

use super::*;
use std::os::unix::fs::symlink;
use tempfile::TempDir;

/// A `<When>` in an imported file resolves `Exists` against the project's
/// directory, while a property group's condition in the same file resolves it
/// against the file's own.
#[test]
fn a_when_in_an_imported_file_tests_exists_against_the_project() {
    let tmp = TempDir::new().unwrap();
    write_at(tmp.path(), "proj/at-project", "");
    write_at(tmp.path(), "shared/at-import", "");
    write_at(
        tmp.path(),
        "shared/x.props",
        r#"<Project>
  <Choose>
    <When Condition="Exists('at-project')">
      <PropertyGroup><WhenProject>1</WhenProject></PropertyGroup>
    </When>
  </Choose>
  <Choose>
    <When Condition="Exists('at-import')">
      <PropertyGroup><WhenImport>1</WhenImport></PropertyGroup>
    </When>
  </Choose>
  <PropertyGroup Condition="Exists('at-import')"><GroupImport>1</GroupImport></PropertyGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "proj/p.proj",
        r#"<Project><Import Project="../shared/x.props" /></Project>"#,
    );
    let result = parse_file(&project_path);
    assert_eq!(
        result.properties.get("WhenProject").map(String::as_str),
        Some("1")
    );
    assert_eq!(result.properties.get("WhenImport"), None);
    assert_eq!(
        result.properties.get("GroupImport").map(String::as_str),
        Some("1")
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

/// A symlink whose target is missing exists to `Exists()`, and `..` after a
/// directory link collapses as text: `up/..` is the directory holding `up`.
#[test]
fn exists_counts_a_dangling_link_and_collapses_dot_dot_as_text() {
    let tmp = TempDir::new().unwrap();
    write_at(tmp.path(), "proj/f", "");
    std::fs::create_dir_all(tmp.path().join("elsewhere/deeper")).unwrap();
    symlink("missing", tmp.path().join("proj/dangling")).unwrap();
    symlink("../elsewhere/deeper", tmp.path().join("proj/up")).unwrap();
    let project_path = write_at(
        tmp.path(),
        "proj/p.proj",
        r#"<Project>
  <PropertyGroup>
    <Dangling Condition="Exists('dangling')">1</Dangling>
    <DanglingDir Condition="Exists('dangling/')">1</DanglingDir>
    <Lexical Condition="Exists('up/../f')">1</Lexical>
  </PropertyGroup>
</Project>"#,
    );
    let result = parse_file(&project_path);
    assert_eq!(
        result.properties.get("Dangling").map(String::as_str),
        Some("1")
    );
    assert_eq!(result.properties.get("DanglingDir"), None);
    assert_eq!(
        result.properties.get("Lexical").map(String::as_str),
        Some("1")
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

/// `GetDirectoryNameOfFileAbove` stops at a dangling symlink of the name, as
/// .NET's `File.Exists` finds one, and passes a directory of the name.
#[test]
fn file_above_stops_at_a_dangling_link_and_passes_a_directory() {
    let tmp = TempDir::new().unwrap();
    write_at(tmp.path(), "marker", "");
    write_at(tmp.path(), "a/b/c/keep", "");
    symlink("missing", tmp.path().join("a/b/marker")).unwrap();
    std::fs::create_dir(tmp.path().join("a/b/c/marker")).unwrap();
    let project_path = write_at(
        tmp.path(),
        "a/b/c/p.proj",
        r#"<Project>
  <PropertyGroup>
    <Found>$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), 'marker'))</Found>
  </PropertyGroup>
</Project>"#,
    );
    let result = parse_file(&project_path);
    let expected = canon(&tmp.path().join("a/b"));
    assert_eq!(
        result.properties.get("Found").map(String::as_str),
        Some(expected.to_str().unwrap())
    );
}
