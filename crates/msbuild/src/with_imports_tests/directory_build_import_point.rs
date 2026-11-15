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
    project.property_provenance_untrusted(name)
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

/// An import point reached under a gate the walk cannot decide, over a file
/// whose identity is certain and which writes nothing: whether MSBuild imports
/// it changes nothing, so nothing is withdrawn.
#[test]
fn an_undecided_gate_over_an_empty_file_marks_nothing() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(tmp.path(), "Directory.Build.targets", EMPTY);
    let project = write_at(
        tmp.path(),
        "p.fsproj",
        &format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n{NAMES_THE_FILE}    \
             <ImportDirectoryBuildTargets Condition=\"{UNDECIDABLE}\">false</ImportDirectoryBuildTargets>\n  \
             </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"A.fs\" />\n  </ItemGroup>\n</Project>\n"
        ),
    );
    let parsed = parse_file_std(&project);
    assert!(
        !parsed.items_uncertain,
        "{:?}",
        parsed.compile_item_uncertainties
    );
    assert_eq!(
        paths_of(&parsed.items),
        vec![canon(tmp.path()).join("A.fs")]
    );
    assert!(!parsed.project_references_uncertain);
}

/// #781: the same gate over a file that contributes. MSBuild writes the gate
/// `false` and never imports the file; the walk cannot tell, so every product
/// of the file is uncertain — its items and its property writes alike.
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
    // The file's identity is certain, so what it does not write stands.
    assert!(!untrusted(&parsed, "Before"));
    assert_eq!(property(&parsed, "Before"), Some("1"));
}

/// A doubted file changes the `<ProjectReference>` list only through its own
/// items: one that declares none leaves the body's list certain, unless a body
/// item reads what the file writes, which is a doubted value.
#[test]
fn a_doubted_file_without_references_leaves_the_reference_list_alone() {
    let tmp = tempfile::tempdir().unwrap();
    write_at(
        tmp.path(),
        "Directory.Build.targets",
        "<Project>\n  <PropertyGroup><FromDbt>1</FromDbt></PropertyGroup>\n  \
         <ItemGroup><Compile Include=\"Dbt.fs\" /></ItemGroup>\n</Project>\n",
    );
    let body = |reference: &str| {
        format!(
            "<Project Sdk=\"Std\">\n  <PropertyGroup>\n{NAMES_THE_FILE}    \
             <ImportDirectoryBuildTargets Condition=\"{UNDECIDABLE}\">false</ImportDirectoryBuildTargets>\n  \
             </PropertyGroup>\n  <ItemGroup>\n    {reference}\n  </ItemGroup>\n</Project>\n"
        )
    };
    let plain = write_at(
        tmp.path(),
        "plain/p.fsproj",
        &body("<ProjectReference Include=\"B.fsproj\" />"),
    );
    write_at(
        tmp.path(),
        "plain/Directory.Build.targets",
        "<Project>\n  <PropertyGroup><FromDbt>1</FromDbt></PropertyGroup>\n  \
         <ItemGroup><Compile Include=\"Dbt.fs\" /></ItemGroup>\n</Project>\n",
    );
    let parsed = parse_file_std(&plain);
    assert!(parsed.items_uncertain);
    assert!(
        !parsed.project_references_uncertain,
        "the doubted file declares no reference"
    );
    assert_eq!(parsed.project_references.len(), 1);

    let reading = write_at(
        tmp.path(),
        "reading/p.fsproj",
        &body("<ProjectReference Include=\"B.fsproj\" Condition=\"'$(FromDbt)' == ''\" />"),
    );
    write_at(
        tmp.path(),
        "reading/Directory.Build.targets",
        "<Project>\n  <PropertyGroup><FromDbt>1</FromDbt></PropertyGroup>\n</Project>\n",
    );
    let parsed = parse_file_std(&reading);
    assert!(
        parsed.project_references_uncertain || parsed.project_references.is_empty(),
        "the reference reads a value the doubted file writes: {:?}",
        parsed.project_references
    );
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
