//! `Directory.Build.props` and `.targets` arrive where an SDK imports them
//! (#677): the walk follows the SDK's own import, and splices a file itself
//! only as a fallback whose products are uncertain.
//!
//! The fallback runs for a file whose import point the walk did not decide:
//! reached under a gate it could not decide, or not reached at all once the
//! walk has passed content it could not see (which may hold the point). What
//! it marks depends on whether the file's identity is certain. When it is,
//! only whether the file is imported is in doubt, so the walk withdraws what
//! the file contributes and nothing else; an empty file contributes nothing.
//! When the path is in doubt, any file may be imported, so the whole
//! evaluation from that point is uncertain.

use super::*;

/// A condition MSBuild evaluates to `true` and the walk cannot evaluate.
const UNDECIDABLE: &str = "$([System.String]::IsNullOrWhiteSpace(''))";

/// A `Directory.Build.*` file that contributes a property, a Compile item, a
/// `ProjectReference` and a define.
fn contributing(marker: &str) -> String {
    format!(
        "<Project>\n  <PropertyGroup>\n    <From{marker}>1</From{marker}>\n  </PropertyGroup>\n  \
         <ItemGroup>\n    <Compile Include=\"{marker}.fs\" />\n    \
         <ProjectReference Include=\"{marker}.fsproj\" />\n  </ItemGroup>\n</Project>\n"
    )
}

/// A `Directory.Build.targets` that writes nothing, the shape repositories use
/// to stop the upward search.
const EMPTY: &str = "<Project>\n  <!-- empty to prevent directory crawling -->\n</Project>\n";

fn untrusted(project: &ParsedProject, name: &str) -> bool {
    !project.property(name).is_exact()
}

fn property<'p>(project: &'p ParsedProject, name: &str) -> Option<&'p str> {
    project
        .properties
        .iter()
        .find(|(k, _)| k.eq_ignore_ascii_case(name))
        .map(|(_, v)| v.as_str())
}

/// A resolver for the SDK `Opaque`, laid out under `dir`: its `Sdk.props`
/// imports `Hidden.props` under a condition the walk cannot decide, and
/// `Hidden.props` writes `hidden`. `Sdk.targets` is `targets`.
fn opaque_sdk(
    dir: &Path,
    hidden: &str,
    targets: &str,
) -> impl Fn(&str) -> Result<SdkResolution, SdkResolveError> + use<> {
    let root = dir.join("opaque-sdk");
    let props = write_at(
        &root,
        "Sdk.props",
        &format!(
            "<Project>\n  <Import Project=\"$(MSBuildThisFileDirectory)Hidden.props\" \
             Condition=\"{UNDECIDABLE}\" />\n</Project>\n"
        ),
    );
    write_at(
        &root,
        "Hidden.props",
        &format!("<Project>\n  <PropertyGroup>\n{hidden}  </PropertyGroup>\n</Project>\n"),
    );
    let targets = write_at(&root, "Sdk.targets", targets);
    let paths = SdkPaths {
        root,
        props,
        targets,
    };
    move |name: &str| {
        if name == "Opaque" {
            Ok(SdkResolution::from(paths.clone()))
        } else {
            Err(SdkResolveError::NotFound)
        }
    }
}

/// MSBuild imports neither file into a project no SDK reaches: nothing imports
/// them but `Microsoft.Common.props` and `.targets`.
#[test]
fn a_project_with_no_sdk_imports_neither_file() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Directory.Build.props", &contributing("Dbp"));
    write_at(tmp.path(), "Directory.Build.targets", &contributing("Dbt"));
    let project = write_at(
        tmp.path(),
        "proj/p.fsproj",
        "<Project>\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file(&project);
    assert!(!parsed.items_uncertain);
    assert_eq!(
        paths_of(&parsed.items),
        vec![canon(tmp.path()).join("proj/A.fs")]
    );
    assert!(!parsed.project_references_uncertain);
    assert!(parsed.project_references.is_empty());
    for name in ["FromDbp", "FromDbt"] {
        assert_eq!(property(&parsed, name), None, "{name}");
        assert!(!untrusted(&parsed, name), "{name}");
    }
}

/// #811: once the walk has passed content it could not see, an import input
/// it holds no binding for may be one that content defines. Here the hidden
/// file points `DirectoryBuildTargetsPath` at a file that does not exist, and
/// no file MSBuild reads imports the `Directory.Build.targets` beside the
/// project. The walk reaches no import point and cannot tell which file the
/// hidden content would name, so it may not publish a Compile set either way.
#[test]
fn hidden_content_may_define_an_unbound_path_so_an_unreached_point_declines() {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = opaque_sdk(
        tmp.path(),
        "    <DirectoryBuildTargetsPath>$(MSBuildProjectDirectory)/missing.targets</DirectoryBuildTargetsPath>\n",
        "<Project />\n",
    );
    write_at(tmp.path(), "Directory.Build.targets", &contributing("Dbt"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Opaque\">\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.items_uncertain,
        "the Compile set rests on a path hidden content may define: {:?}",
        paths_of(&parsed.items)
    );
    assert!(parsed.project_references_uncertain);
    assert!(parsed.define_constants_uncertain);
    assert!(untrusted(&parsed, "FromDbt"));
}

/// The same opacity with no `Directory.Build.*` file anywhere charges nothing:
/// the walk's doubt about the import points is a doubt about whether the
/// default file is imported, and there is none. (A file the hidden content
/// names is hidden content like any other.)
#[test]
fn an_import_the_walk_cannot_decide_charges_nothing_without_a_directory_build_file() {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = opaque_sdk(
        tmp.path(),
        "    <Unrelated>1</Unrelated>\n",
        &format!("<Project>\n{COMMON_TARGETS_BLOCK}</Project>\n"),
    );
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Opaque\">\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n    \
         <ProjectReference Include=\"B.fsproj\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        !parsed.items_uncertain,
        "{:?}",
        parsed.compile_item_uncertainties
    );
    assert!(!parsed.project_references_uncertain);
    assert!(!parsed.define_constants_uncertain);
}

/// The body names the file outright, so the SDK's discovery never runs and
/// the path is certain whatever the gate holds.
const NAMES_THE_FILE: &str = "    <DirectoryBuildTargetsPath>$(MSBuildProjectDirectory)/Directory.Build.targets</DirectoryBuildTargetsPath>\n";

/// #781: an import point reached under a gate the walk cannot decide. MSBuild
/// writes the gate `false` and never imports the file; the walk cannot tell,
/// so the whole evaluation is uncertain from the point: the file's items and
/// property writes, and every value bound before it.
#[test]
fn an_undecided_gate_over_a_contributing_file_withdraws_what_it_contributes() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Directory.Build.targets", &contributing("Dbt"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n    <Before>1</Before>\n{NAMES_THE_FILE}    \
             <ImportDirectoryBuildTargets Condition=\"{UNDECIDABLE}\">false</ImportDirectoryBuildTargets>\n  \
             </PropertyGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_std(&project);
    assert!(parsed.items_uncertain);
    assert!(parsed.project_references_uncertain);
    assert!(
        untrusted(&parsed, "FromDbt"),
        "{:?}",
        property(&parsed, "FromDbt")
    );
    assert!(untrusted(&parsed, "Before"));
}

/// What a doubted file imports is doubted too: here the file names its child
/// through a property it writes itself. Doubting the file must not lose the
/// child, whose write would otherwise leave an earlier value trusted.
#[test]
fn a_doubted_file_s_own_imports_are_doubted_with_it() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(
        tmp.path(),
        "Directory.Build.targets",
        "<Project>\n  <PropertyGroup><ChildPath>$(MSBuildThisFileDirectory)child.props</ChildPath></PropertyGroup>\n  \
         <Import Project=\"$(ChildPath)\" />\n</Project>\n",
    );
    write_at(
        tmp.path(),
        "child.props",
        "<Project><PropertyGroup><LangVersion>preview</LangVersion></PropertyGroup></Project>",
    );
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n    <LangVersion>8.0</LangVersion>\n{NAMES_THE_FILE}    \
             <ImportDirectoryBuildTargets Condition=\"{UNDECIDABLE}\">false</ImportDirectoryBuildTargets>\n  \
             </PropertyGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_std(&project);
    assert!(
        untrusted(&parsed, "LangVersion"),
        "the doubted file's child may write it: {:?}",
        property(&parsed, "LangVersion")
    );
    assert!(untrusted(&parsed, "ChildPath"));
}

/// A doubted file is one MSBuild may not have imported, so a later import of
/// it is not certainly a duplicate: here MSBuild skips the point and makes
/// the later import, whose write lands after the SDK's own. The later import
/// names the file by a literal path: the path property is unpinned by the
/// fallback, and an import through it is skipped as hidden content (whose
/// stale values the property reader trusts, #792).
#[test]
fn a_later_import_of_a_doubted_file_is_doubted_too() {
    let tmp = tempfile::tempdir().unwrap();
    let false_to_msbuild = "$([System.String]::IsNullOrWhiteSpace('no'))";
    let block = COMMON_TARGETS_BLOCK.replace(
        "Condition=\"'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')\"",
        &format!("Condition=\"{false_to_msbuild} and exists('$(DirectoryBuildTargetsPath)')\""),
    );
    assert_ne!(block, COMMON_TARGETS_BLOCK);
    let resolver = custom_sdk(
        tmp.path(),
        "<Project />\n",
        &format!(
            "<Project>\n{block}  <PropertyGroup><LangVersion>8.0</LangVersion></PropertyGroup>\n  \
             <Import Project=\"$(MSBuildProjectDirectory)/Directory.Build.targets\" />\n</Project>\n"
        ),
        &[],
    );
    write_at(
        tmp.path(),
        "Directory.Build.targets",
        "<Project><PropertyGroup><LangVersion>preview</LangVersion></PropertyGroup></Project>",
    );
    let project = write_at(tmp.path(), "p.fsproj", "<Project Sdk=\"Custom\" />\n");
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        untrusted(&parsed, "LangVersion"),
        "MSBuild makes the later import and ends with `preview`; the walk published {:?}",
        property(&parsed, "LangVersion")
    );
}

/// The same through a child: the doubted file's own import is one MSBuild may
/// not have made either, so walking the file again walks the child again.
#[test]
fn a_later_import_of_a_doubted_file_doubts_its_children_again() {
    let tmp = tempfile::tempdir().unwrap();
    let false_to_msbuild = "$([System.String]::IsNullOrWhiteSpace('no'))";
    let block = COMMON_TARGETS_BLOCK.replace(
        "Condition=\"'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')\"",
        &format!("Condition=\"{false_to_msbuild} and exists('$(DirectoryBuildTargetsPath)')\""),
    );
    let resolver = custom_sdk(
        tmp.path(),
        "<Project />\n",
        &format!(
            "<Project>\n{block}  <PropertyGroup><LangVersion>8.0</LangVersion></PropertyGroup>\n  \
             <Import Project=\"$(MSBuildProjectDirectory)/Directory.Build.targets\" />\n</Project>\n"
        ),
        &[],
    );
    write_at(
        tmp.path(),
        "Directory.Build.targets",
        "<Project><Import Project=\"$(MSBuildThisFileDirectory)child.props\" /></Project>",
    );
    write_at(
        tmp.path(),
        "child.props",
        "<Project><PropertyGroup><LangVersion>preview</LangVersion></PropertyGroup></Project>",
    );
    let project = write_at(tmp.path(), "p.fsproj", "<Project Sdk=\"Custom\" />\n");
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        untrusted(&parsed, "LangVersion"),
        "MSBuild imports the child at the later import and ends with `preview`; the walk \
         published {:?}",
        property(&parsed, "LangVersion")
    );
}

/// Walking a doubted file again ends, though the file and its child import
/// each other: within the walk that walks it again, the cycle's back edge is
/// a duplicate as MSBuild's is.
#[test]
fn walking_a_doubted_cycle_again_ends() {
    let tmp = tempfile::tempdir().unwrap();
    let false_to_msbuild = "$([System.String]::IsNullOrWhiteSpace('no'))";
    let block = COMMON_TARGETS_BLOCK.replace(
        "Condition=\"'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')\"",
        &format!("Condition=\"{false_to_msbuild} and exists('$(DirectoryBuildTargetsPath)')\""),
    );
    let resolver = custom_sdk(
        tmp.path(),
        "<Project />\n",
        &format!(
            "<Project>\n{block}  <Import Project=\"$(MSBuildProjectDirectory)/Directory.Build.targets\" />\n</Project>\n"
        ),
        &[],
    );
    write_at(
        tmp.path(),
        "Directory.Build.targets",
        "<Project><Import Project=\"$(MSBuildThisFileDirectory)child.props\" /></Project>",
    );
    write_at(
        tmp.path(),
        "child.props",
        "<Project><PropertyGroup><LangVersion>preview</LangVersion></PropertyGroup>\
         <Import Project=\"$(MSBuildThisFileDirectory)Directory.Build.targets\" /></Project>",
    );
    let project = write_at(tmp.path(), "p.fsproj", "<Project Sdk=\"Custom\" />\n");
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        !parsed.diagnostics.iter().any(|d| matches!(
            d.kind,
            DiagnosticKind::ImportFailed {
                reason: ImportFailReason::DepthLimit { .. },
                ..
            }
        )),
        "{:?}",
        parsed.diagnostics
    );
    assert!(untrusted(&parsed, "LangVersion"));
}

/// An import point decided on an undefined `TargetFramework` read is as exact
/// as the walk's reads of it are: on the walk that reads it exactly (a
/// project that builds its own framework), the point is decided.
#[test]
fn a_point_behind_an_exact_target_framework_read_is_decided() {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = custom_sdk(
        tmp.path(),
        "<Project>\n  <Import Project=\"$(MSBuildThisFileDirectory)Common.props\" \
         Condition=\"'$(TargetFramework)' == ''\" />\n</Project>\n",
        "<Project />\n",
        &[(
            "Common.props",
            &format!("<Project>\n{COMMON_PROPS_BLOCK}</Project>\n"),
        )],
    );
    write_at(tmp.path(), "Directory.Build.props", &contributing("Dbp"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Custom\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  \
         <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        !parsed.items_uncertain,
        "{:?}",
        parsed.compile_item_uncertainties
    );
    let dir = canon(tmp.path());
    assert_eq!(
        paths_of(&parsed.items),
        vec![dir.join("Dbp.fs"), dir.join("A.fs")]
    );
}

/// With no path of its own, the same gate decides whether the SDK's discovery
/// runs, so the path it computes rests on the gate too, and the walk, which
/// tells a path's doubt from a gate's only by its trust, treats the file's
/// identity as uncertain: a conservative decline, even over an empty file.
#[test]
fn an_undecided_gate_reaches_the_path_through_the_sdk_discovery() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Directory.Build.targets", EMPTY);
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n    \
             <ImportDirectoryBuildTargets Condition=\"{UNDECIDABLE}\">false</ImportDirectoryBuildTargets>\n  \
             </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_std(&project);
    assert!(parsed.items_uncertain);
}

/// A path the walk cannot pin down may name any file, so it cannot withdraw
/// only what the default file contributes, even when that file is empty: the
/// whole evaluation from the import point is uncertain.
#[test]
fn an_undecided_path_makes_the_whole_evaluation_uncertain() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Directory.Build.targets", EMPTY);
    write_at(tmp.path(), "other.targets", &contributing("Other"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n    <Before>1</Before>\n    \
             <DirectoryBuildTargetsPath Condition=\"{UNDECIDABLE}\">$(MSBuildProjectDirectory)/other.targets</DirectoryBuildTargetsPath>\n  \
             </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_std(&project);
    assert!(parsed.items_uncertain);
    assert!(parsed.project_references_uncertain);
    assert!(parsed.define_constants_uncertain);
    assert!(
        untrusted(&parsed, "Before"),
        "a file the path may name can overwrite `Before`"
    );
}

/// Lay out the SDK `Custom` under `dir` from its two files' text, and return a
/// resolver for it.
fn custom_sdk(
    dir: &Path,
    props: &str,
    targets: &str,
    extra: &[(&str, &str)],
) -> impl Fn(&str) -> Result<SdkResolution, SdkResolveError> + use<> {
    let root = dir.join("custom-sdk");
    let paths = SdkPaths {
        props: write_at(&root, "Sdk.props", props),
        targets: write_at(&root, "Sdk.targets", targets),
        root: root.clone(),
    };
    for (name, text) in extra {
        write_at(&root, name, text);
    }
    move |name: &str| {
        if name == "Custom" {
            Ok(SdkResolution::from(paths.clone()))
        } else {
            Err(SdkResolveError::NotFound)
        }
    }
}

/// A write that a stale value let run is stale itself, as one its own
/// condition let run is: here the SDK's discovery computes the path under a
/// gate copied from a value hidden content redefines. MSBuild reads the gate
/// `false`, never computes the path, and imports nothing; the walk reads it
/// `true`, and must not take the path its discovery computed as certain, even
/// at a point whose own condition does not read the gate.
#[test]
fn a_path_a_stale_gate_let_the_discovery_compute_is_stale() {
    let tmp = tempfile::tempdir().unwrap();
    // Without the `CustomBefore`/`CustomAfter` hooks, whose gates read a name
    // no file binds and so latch opacity again after the path is computed,
    // which would leave the path stale by that route.
    let block: String = COMMON_TARGETS_BLOCK
        .replace(
            "Condition=\"'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')\"",
            "Condition=\"exists('$(DirectoryBuildTargetsPath)')\"",
        )
        .lines()
        .filter(|line| !line.contains("CustomBeforeDirectoryBuildTargets") && !line.contains("CustomAfterDirectoryBuildTargets"))
        .map(|line| format!("{line}\n"))
        .collect();
    assert!(block.contains("Condition=\"exists('$(DirectoryBuildTargetsPath)')\""));
    assert!(!block.contains("Custom"));
    let resolver = custom_sdk(
        tmp.path(),
        &format!(
            "<Project>\n  <PropertyGroup><Gate>true</Gate></PropertyGroup>\n  \
             <Import Project=\"$(MSBuildThisFileDirectory)Hidden.props\" Condition=\"{UNDECIDABLE}\" />\n</Project>\n"
        ),
        &format!(
            "<Project>\n  <PropertyGroup><ImportDirectoryBuildTargets>$(Gate)</ImportDirectoryBuildTargets></PropertyGroup>\n{block}</Project>\n"
        ),
        &[(
            "Hidden.props",
            "<Project><PropertyGroup><Gate>false</Gate></PropertyGroup></Project>",
        )],
    );
    write_at(tmp.path(), "Directory.Build.targets", &contributing("Dbt"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Custom\">\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.items_uncertain,
        "MSBuild imports no Directory.Build.targets; the walk published {:?}",
        paths_of(&parsed.items)
    );
}

/// Under opacity, a point that names the file through an alias stands beside
/// the SDK's own import of it, which the hidden content holds: MSBuild imports
/// the file twice, once by each spelling. The walk sees only the alias's
/// import, so it has not accounted for the SDK's, and declines.
#[test]
fn a_point_naming_an_alias_leaves_the_sdks_own_import_to_the_fallback() {
    let tmp = tempfile::tempdir().unwrap();
    let hidden = format!("<Project>\n{COMMON_PROPS_BLOCK}</Project>\n");
    let resolver = custom_sdk(
        tmp.path(),
        &format!(
            "<Project>\n  <Import Project=\"$(MSBuildThisFileDirectory)Hidden.props\" Condition=\"{UNDECIDABLE}\" />\n  \
             <PropertyGroup><DirectoryBuildPropsPath>$(MSBuildProjectDirectory)/alias.props</DirectoryBuildPropsPath></PropertyGroup>\n  \
             <Import Project=\"$(DirectoryBuildPropsPath)\" Condition=\"exists('$(DirectoryBuildPropsPath)')\" />\n</Project>\n"
        ),
        "<Project />\n",
        &[("Hidden.props", &hidden)],
    );
    write_at(tmp.path(), "Directory.Build.props", &contributing("Dbp"));
    write_at(tmp.path(), "alias.props", &contributing("Dbp"));
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Custom\">\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.items_uncertain,
        "MSBuild may import Directory.Build.props as well; the walk published {:?}",
        paths_of(&parsed.items)
    );
}

/// A path whose value is a wildcard or a list names no one file, yet MSBuild
/// imports every file it matches: an undecided point over it may import them
/// all, so what they write declines.
fn a_point_over_a_spec_of(spec: &str, files: &[&str]) {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = custom_sdk(
        tmp.path(),
        "<Project />\n",
        &format!(
            "<Project>\n  <Import Project=\"$(DirectoryBuildTargetsPath)\" \
             Condition=\"{UNDECIDABLE} Or Exists('$(DirectoryBuildTargetsPath)')\" />\n</Project>\n"
        ),
        &[],
    );
    for file in files {
        write_at(
            &tmp.path().join("imports"),
            file,
            "<Project><PropertyGroup><FromSpec>1</FromSpec></PropertyGroup></Project>",
        );
    }
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Custom\">\n  <PropertyGroup>\n    \
             <DirectoryBuildTargetsPath>{spec}</DirectoryBuildTargetsPath>\n  \
             </PropertyGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        !parsed.property("FromSpec").is_exact(),
        "MSBuild imports the files {spec} names and defines `FromSpec`; the walk read {:?}",
        parsed.property("FromSpec")
    );
}

#[test]
fn an_undecided_point_over_a_wildcard_path_declines_what_its_files_write() {
    a_point_over_a_spec_of(
        "$(MSBuildProjectDirectory)/imports/*.targets",
        &["a.targets"],
    );
}

#[test]
fn an_undecided_point_over_a_path_list_declines_what_its_files_write() {
    a_point_over_a_spec_of(
        "$(MSBuildProjectDirectory)/imports/a.targets;$(MSBuildProjectDirectory)/imports/b.targets",
        &["a.targets", "b.targets"],
    );
}

/// The SDK's props import `Directory.Build.props` behind a condition MSBuild
/// takes and the walk cannot decide, and its targets import the file again
/// through a point the walk could decide (import-graph soak seed 112233, case
/// 9706). MSBuild skips the second import as a duplicate, so the file's
/// Compile item comes before the body's. The walk cannot see the first import,
/// so it must not commit the order its own import of the file would give.
#[test]
fn a_point_after_a_hidden_import_of_its_file_commits_no_order() {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = custom_sdk(
        tmp.path(),
        &format!(
            "<Project>\n  <Import Project=\"$(MSBuildProjectDirectory)/Directory.Build.props\" \
             Condition=\"{UNDECIDABLE}\" />\n</Project>\n"
        ),
        "<Project>\n  <PropertyGroup>\n    \
         <DirectoryBuildPropsPath>$(MSBuildProjectDirectory)/Directory.Build.props</DirectoryBuildPropsPath>\n  \
         </PropertyGroup>\n  <Import Project=\"$(DirectoryBuildPropsPath)\" \
         Condition=\"exists('$(DirectoryBuildPropsPath)')\" />\n</Project>\n",
        &[],
    );
    write_at(
        tmp.path(),
        "Directory.Build.props",
        "<Project><ItemGroup><Compile Include=\"before.fs\" /></ItemGroup></Project>",
    );
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Custom\">\n  <ItemGroup>\n    <Compile Include=\"body.fs\" />\n  </ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.items_uncertain
            || paths_of(&parsed.items)
                == [tmp.path().join("before.fs"), tmp.path().join("body.fs")],
        "MSBuild orders the file's item first; the walk published {:?}",
        paths_of(&parsed.items)
    );
}

/// The same shape through a plain `<Import>` rather than a `Directory.Build`
/// point: once the walk has passed content it could not see, any import may
/// be a duplicate of one that content made.
#[test]
#[ignore = "#819: a certain import after opacity may be a duplicate MSBuild skips"]
fn a_plain_import_after_a_hidden_import_of_its_file_commits_no_order() {
    let tmp = tempfile::tempdir().unwrap();
    let resolver = custom_sdk(
        tmp.path(),
        &format!(
            "<Project>\n  <Import Project=\"$(MSBuildProjectDirectory)/shared.props\" \
             Condition=\"{UNDECIDABLE}\" />\n</Project>\n"
        ),
        "<Project />\n",
        &[],
    );
    write_at(
        tmp.path(),
        "shared.props",
        "<Project><PropertyGroup><Order>$(Order);shared</Order></PropertyGroup>\
         <ItemGroup><Compile Include=\"before.fs\" /></ItemGroup></Project>",
    );
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        "<Project Sdk=\"Custom\">\n  <PropertyGroup>\n    <Order>$(Order);body</Order>\n  </PropertyGroup>\n  \
         <ItemGroup>\n    <Compile Include=\"body.fs\" />\n  </ItemGroup>\n  \
         <Import Project=\"$(MSBuildProjectDirectory)/shared.props\" />\n</Project>\n",
    );
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.items_uncertain
            || paths_of(&parsed.items)
                == [tmp.path().join("before.fs"), tmp.path().join("body.fs")],
        "MSBuild orders the file's item first; the walk published {:?}",
        paths_of(&parsed.items)
    );
    assert!(
        !parsed.property("Order").is_exact()
            || parsed.property("Order").value() == Some(";shared;body"),
        "MSBuild runs `shared.props` once, first; the walk read {:?}",
        parsed.property("Order")
    );
}

/// Undecided points nested in a chain of files, each importing the next
/// twice: walking every doubted import again would take work exponential in
/// the chain's length. The doubted walks an evaluation makes are bounded, and
/// past the bound a file is content the walk could not see, so the walk ends
/// promptly and what the chain writes declines.
#[test]
fn nested_undecided_points_take_bounded_work() {
    const FILES: usize = 17;
    let tmp = tempfile::tempdir().unwrap();
    let point = |next: usize| {
        format!(
            "  <PropertyGroup><DirectoryBuildTargetsPath>$(MSBuildThisFileDirectory)f{next}.targets</DirectoryBuildTargetsPath></PropertyGroup>\n  \
             <Import Project=\"$(DirectoryBuildTargetsPath)\" \
             Condition=\"{UNDECIDABLE} and exists('$(DirectoryBuildTargetsPath)')\" />\n"
        )
    };
    let extra: Vec<(String, String)> = (1..=FILES)
        .map(|i| {
            let imports = if i < FILES {
                format!("{}{}", point(i + 1), point(i + 1))
            } else {
                String::new()
            };
            (
                format!("f{i}.targets"),
                format!(
                    "<Project>\n  <PropertyGroup><Chain>$(Chain);{i}</Chain></PropertyGroup>\n{imports}</Project>\n"
                ),
            )
        })
        .collect();
    let extra_refs: Vec<(&str, &str)> = extra
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect();
    let resolver = custom_sdk(
        tmp.path(),
        "<Project />\n",
        &format!("<Project>\n{}</Project>\n", point(1)),
        &extra_refs,
    );
    let project = write_at(tmp.path(), "p.fsproj", "<Project Sdk=\"Custom\" />\n");
    let started = std::time::Instant::now();
    let parsed = parse_file_with_sdk_resolution(&project, resolver);
    assert!(
        parsed.diagnostics.len() < 10_000,
        "{} diagnostics after {:?}",
        parsed.diagnostics.len(),
        started.elapsed()
    );
    assert!(!parsed.property("Chain").is_exact());
}
