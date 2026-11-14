//! [`ParsedProject::foreign_definitions`]: what the documents outside the entry
//! .NET SDK's version directory define, read off their text whatever the
//! conditions around each definition say, and
//! [`ParsedProject::hidden_content`], which says whether that list can be
//! complete.

use super::*;
use std::collections::BTreeSet;
use tempfile::TempDir;

/// A canonical-layout SDK under `tmp/dotnet/sdk/10.0.100`, whose `Sdk.props`
/// and `Sdk.targets` are `props` and `targets`, with `files` written relative
/// to the version directory; and its resolver.
fn canonical_sdk(
    tmp: &Path,
    props: &str,
    targets: &str,
    files: &[(&str, &str)],
) -> impl Fn(&str) -> Result<SdkResolution, SdkResolveError> + use<> {
    let version_dir = tmp.join("dotnet").join("sdk").join("10.0.100");
    let root = version_dir.join("Sdks").join("MySdk").join("Sdk");
    let props = write_at(&root, "Sdk.props", props);
    let targets = write_at(&root, "Sdk.targets", targets);
    for (name, text) in files {
        write_at(&version_dir, name, text);
    }
    move |name: &str| {
        if name == "MySdk" {
            Ok(SdkResolution::from(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    }
}

fn names(table: &BTreeMap<String, BTreeSet<PathBuf>>) -> Vec<&str> {
    table.keys().map(String::as_str).collect()
}

fn files_of<'a>(table: &'a BTreeMap<String, BTreeSet<PathBuf>>, name: &str) -> Vec<&'a str> {
    table[name]
        .iter()
        .map(|p| p.file_name().unwrap().to_str().unwrap())
        .collect()
}

#[test]
fn every_definition_outside_the_sdk_is_recorded_whatever_its_condition() {
    let tmp = TempDir::new().unwrap();
    let resolver = canonical_sdk(
        tmp.path(),
        r#"<Project>
  <PropertyGroup><FscToolPath>/sdk</FscToolPath></PropertyGroup>
  <Import Project="$(MSBuildThisFileDirectory)../../../FSharp/F.props" />
</Project>"#,
        r#"<Project>
  <Target Name="SdkTarget"><PropertyGroup><SdkInTarget>1</SdkInTarget></PropertyGroup></Target>
  <Import Project="$(MSBuildProjectDirectory)/user.targets" />
</Project>"#,
        &[(
            "FSharp/F.props",
            r#"<Project><PropertyGroup Condition="'$(Nope)' == 'x'"><DotnetFscCompilerPath>x</DotnetFscCompilerPath></PropertyGroup></Project>"#,
        )],
    );
    write_at(
        tmp.path(),
        "user.targets",
        r#"<Project>
  <Target Name="CoreCompile">
    <PropertyGroup><FscToolExe>other</FscToolExe></PropertyGroup>
    <CreateProperty Value="v"><Output TaskParameter="Value" PropertyName="Picked" /></CreateProperty>
    <CreateItem Include="a"><Output TaskParameter="Include" ItemName="NotAProperty" /></CreateItem>
  </Target>
</Project>"#,
    );
    write_at(
        tmp.path(),
        "Directory.Build.props",
        "<Project><PropertyGroup><FromDirectoryBuild>1</FromDirectoryBuild></PropertyGroup></Project>",
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="MySdk">
  <PropertyGroup Condition="'$([System.Guid]::NewGuid())' == ''"><Skipped>1</Skipped></PropertyGroup>
  <PropertyGroup Condition="'false' == 'true'"><Decided>1</Decided></PropertyGroup>
  <Choose>
    <When Condition="'$(Undecided)' == 'y'"><PropertyGroup><InChoose>1</InChoose></PropertyGroup></When>
  </Choose>
  <UsingTask TaskName="Fsc" AssemblyFile="/opt/My.Build.dll" />
  <ItemGroup><Compile Include="a.fs" /></ItemGroup>
</Project>"#,
    );
    let result = parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
    assert_eq!(result.hidden_content, None);
    let foreign = &result.foreign_definitions;
    assert_eq!(
        names(&foreign.properties),
        [
            "decided",
            "fromdirectorybuild",
            "fsctoolexe",
            "inchoose",
            "picked",
            "skipped"
        ],
        "the SDK's own writes are not foreign, every other is, whatever its condition"
    );
    assert_eq!(
        files_of(&foreign.properties, "fsctoolexe"),
        ["user.targets"]
    );
    assert_eq!(
        files_of(&foreign.properties, "fromdirectorybuild"),
        ["Directory.Build.props"]
    );
    assert_eq!(files_of(&foreign.properties, "skipped"), ["Demo.fsproj"]);
    assert_eq!(
        names(&foreign.build_time_properties),
        ["fsctoolexe", "picked"],
        "a target's writes run at build time"
    );
    assert!(foreign.writes_property_at_build_time("FscToolExe"));
    assert!(!foreign.writes_property_at_build_time("Skipped"));
    assert_eq!(names(&foreign.targets), ["corecompile"]);
    assert_eq!(names(&foreign.tasks), ["fsc"]);
}

#[test]
fn content_behind_an_undecidable_import_is_hidden() {
    let tmp = TempDir::new().unwrap();
    let resolver = canonical_sdk(tmp.path(), "<Project/>", "<Project/>", &[]);
    write_at(tmp.path(), "other.props", "<Project/>");
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="MySdk">
  <Import Project="other.props" Condition="'$([System.Guid]::NewGuid())' == ''" />
</Project>"#,
    );
    let result = parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
    assert!(
        result.hidden_content.is_some(),
        "{:?}",
        result.hidden_content
    );
}

#[test]
fn an_sdk_outside_the_canonical_layout_is_foreign_throughout() {
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        "<Project><PropertyGroup><FscToolPath>/sdk</FscToolPath></PropertyGroup></Project>",
        "<Project/>",
    );
    let project_path = write_at(tmp.path(), "Demo.fsproj", r#"<Project Sdk="MySdk" />"#);
    let result = parse_file_with_sdk(&project_path, |_| {
        Ok(SdkPaths {
            root: root.clone(),
            props: props.clone(),
            targets: targets.clone(),
        })
    });
    assert_eq!(
        names(&result.foreign_definitions.properties),
        ["fsctoolpath"]
    );
}

/// A name the build computes may be any name, and a task registration
/// answers to its short name under any namespace.
#[test]
fn the_queries_match_computed_names_and_short_task_names() {
    let parse = |text: &str| {
        let doc = roxmltree::Document::parse(text).unwrap();
        let mut foreign = ForeignDefinitions::default();
        foreign.record_document(doc.root_element(), Path::new("/w/x.targets"));
        foreign
    };
    let plain = parse(
        r#"<Project><UsingTask TaskName="My.Ns.Fsc" AssemblyFile="a.dll" /><Target Name="T"><PropertyGroup><A>1</A></PropertyGroup></Target></Project>"#,
    );
    assert!(plain.defines_task("Fsc"));
    assert!(plain.defines_task("fsc"));
    assert!(!plain.defines_task("Csc"));
    assert!(!plain.defines_task("Ns.Fsc.Other"));
    assert!(plain.defines_property("A") && !plain.defines_property("B"));
    assert!(plain.defines_target("t") && !plain.defines_target("CoreCompile"));
    let computed = parse(
        r#"<Project><Target Name="T"><CreateProperty Value="v"><Output TaskParameter="Value" PropertyName="$(Selector)" /></CreateProperty></Target><UsingTask TaskName="$(Task)" AssemblyFile="a.dll" /></Project>"#,
    );
    assert!(computed.defines_property("DotnetFscCompilerPath"));
    assert!(computed.writes_property_at_build_time("LangVersion"));
    assert!(computed.defines_task("Fsc"));
    assert!(!computed.defines_target("CoreCompile"));
}
