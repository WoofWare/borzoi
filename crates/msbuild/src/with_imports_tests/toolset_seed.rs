//! The toolset's product version, seeded as `VisualStudioVersion` and as
//! `MSBuildAssemblyVersion` when an SDK in the canonical .NET layout
//! (`…/sdk/<version>/Sdks/<name>/Sdk`) resolves. MSBuild defines both before
//! evaluation starts. The environment, a caller global or any earlier write
//! displaces `VisualStudioVersion`, so its seed must defer to all of them, and
//! to content the walk could not see before the SDK resolved.
//! `MSBuildAssemblyVersion` is reserved, so nothing displaces it.

use super::*;
use tempfile::TempDir;

/// A canonical-layout SDK under `tmp/dotnet/sdk/<version>`, and its resolver.
fn canonical_sdk(
    tmp: &Path,
    version: &str,
) -> impl Fn(&str) -> Result<SdkResolution, SdkResolveError> + use<> {
    let root = tmp
        .join("dotnet")
        .join("sdk")
        .join(version)
        .join("Sdks")
        .join("MySdk")
        .join("Sdk");
    let props = write_at(&root, "Sdk.props", "<Project/>");
    let targets = write_at(&root, "Sdk.targets", "<Project/>");
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

/// `Seen`, the body's copy of `$(VisualStudioVersion)`, when committed.
fn committed_seen(result: &ParsedProject) -> Option<&str> {
    let value = result.properties.get("Seen")?;
    (!result.property("Seen").untrusted_cause().is_some()).then_some(value.as_str())
}

const COPY: &str = "<PropertyGroup><Seen>$(VisualStudioVersion)</Seen></PropertyGroup>";

#[test]
fn a_release_sdk_seeds_its_toolset_visual_studio_version() {
    for (version, expected) in [("10.0.100", Some("18.0")), ("9.0.300", Some("17.0"))] {
        let tmp = TempDir::new().unwrap();
        let resolver = canonical_sdk(tmp.path(), version);
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(r#"<Project Sdk="MySdk">{COPY}</Project>"#),
        );
        let result =
            parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
        assert_eq!(committed_seen(&result), expected, "SDK {version}");
    }
}

#[test]
fn a_prerelease_sdk_seeds_nothing() {
    let tmp = TempDir::new().unwrap();
    let resolver = canonical_sdk(tmp.path(), "10.0.100-preview.3.25201.16");
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        &format!(r#"<Project Sdk="MySdk">{COPY}</Project>"#),
    );
    let result = parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
    assert_eq!(committed_seen(&result), None);
}

#[test]
fn the_environment_and_a_global_displace_the_seed() {
    let tmp = TempDir::new().unwrap();
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        &format!(r#"<Project Sdk="MySdk">{COPY}</Project>"#),
    );
    let env = HashMap::from([("VisualStudioVersion".to_string(), "16.0".to_string())]);
    let result = parse_file_with_sdk_env(
        &project_path,
        canonical_sdk(tmp.path(), "10.0.100"),
        HashMap::new(),
        env,
    );
    assert_eq!(committed_seen(&result), Some("16.0"));

    let globals = HashMap::from([("VisualStudioVersion".to_string(), "15.0".to_string())]);
    let result = parse_file_with_sdk_env(
        &project_path,
        canonical_sdk(tmp.path(), "10.0.100"),
        globals,
        HashMap::new(),
    );
    assert_eq!(committed_seen(&result), Some("15.0"));
}

/// An import the walk cannot decide may have written `VisualStudioVersion`
/// before the SDK resolves; the hidden write leaves no trust record, so only
/// the walk's opacity says the slot may be taken.
#[test]
fn an_undecided_import_before_the_sdk_withholds_the_seed() {
    let tmp = TempDir::new().unwrap();
    write_at(
        tmp.path(),
        "hidden.props",
        "<Project><PropertyGroup><VisualStudioVersion>99.0</VisualStudioVersion></PropertyGroup></Project>",
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        &format!(
            r#"<Project>
  <Import Project="hidden.props" Condition="'É' == 'é'" />
  <Import Sdk="MySdk" Project="Sdk.props" />
  {COPY}
</Project>"#
        ),
    );
    let result = parse_file_with_sdk_env(
        &project_path,
        canonical_sdk(tmp.path(), "10.0.100"),
        HashMap::new(),
        HashMap::new(),
    );
    assert_eq!(
        committed_seen(&result),
        None,
        "diagnostics: {:?}",
        result.diagnostics
    );
}

/// `Seen`, the body's copy of `$(MSBuildAssemblyVersion)`.
const COPY_ASSEMBLY_VERSION: &str =
    "<PropertyGroup><Seen>$(MSBuildAssemblyVersion)</Seen></PropertyGroup>";

#[test]
fn a_release_sdk_seeds_its_toolset_assembly_version() {
    for (version, expected) in [
        ("10.0.100", Some("18.0")),
        ("9.0.300", Some("17.0")),
        ("10.0.100-preview.3.25201.16", None),
        ("7.0.410", None),
    ] {
        let tmp = TempDir::new().unwrap();
        let resolver = canonical_sdk(tmp.path(), version);
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(r#"<Project Sdk="MySdk">{COPY_ASSEMBLY_VERSION}</Project>"#),
        );
        let result =
            parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
        assert_eq!(committed_seen(&result), expected, "SDK {version}");
    }
}

/// The name is reserved: MSBuild ignores an environment variable of it.
#[test]
fn the_environment_does_not_displace_the_assembly_version() {
    let tmp = TempDir::new().unwrap();
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        &format!(r#"<Project Sdk="MySdk">{COPY_ASSEMBLY_VERSION}</Project>"#),
    );
    let env = HashMap::from([("MSBuildAssemblyVersion".to_string(), "9.9".to_string())]);
    let result = parse_file_with_sdk_env(
        &project_path,
        canonical_sdk(tmp.path(), "10.0.100"),
        HashMap::new(),
        env,
    );
    assert_eq!(committed_seen(&result), Some("18.0"));
}

/// MSBuild refuses a write to the name wherever it sits, so content the walk
/// could not see before the SDK resolved cannot have taken the slot.
#[test]
fn an_undecided_import_before_the_sdk_keeps_the_assembly_version() {
    let tmp = TempDir::new().unwrap();
    write_at(tmp.path(), "hidden.props", "<Project />");
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        &format!(
            r#"<Project>
  <Import Project="hidden.props" Condition="'É' == 'é'" />
  <Import Sdk="MySdk" Project="Sdk.props" />
  {COPY_ASSEMBLY_VERSION}
</Project>"#
        ),
    );
    let result = parse_file_with_sdk_env(
        &project_path,
        canonical_sdk(tmp.path(), "10.0.100"),
        HashMap::new(),
        HashMap::new(),
    );
    assert_eq!(
        result.property("MSBuildAssemblyVersion").value(),
        Some("18.0"),
        "diagnostics: {:?}",
        result.diagnostics
    );
}

/// The toolset is the first SDK's. Where that one's product version is not
/// probed, a later SDK from a probed version directory seeds nothing.
#[test]
fn a_later_sdk_does_not_seed_the_assembly_version_the_first_declined() {
    for (first, later, expected) in [
        ("10.0.100-preview.3.25201.16", "10.0.100", None),
        ("9.0.300", "10.0.100", Some("17.0")),
    ] {
        let tmp = TempDir::new().unwrap();
        let sdk_root = |version: &str, name: &str| {
            let root = tmp
                .path()
                .join("dotnet")
                .join("sdk")
                .join(version)
                .join("Sdks")
                .join(name)
                .join("Sdk");
            let props = write_at(&root, "Sdk.props", "<Project/>");
            let targets = write_at(&root, "Sdk.targets", "<Project/>");
            SdkPaths {
                root,
                props,
                targets,
            }
        };
        let first_sdk = sdk_root(first, "First");
        let later_sdk = sdk_root(later, "Later");
        let resolver = move |name: &str| match name {
            "First" => Ok(SdkResolution::from(first_sdk.clone())),
            "Later" => Ok(SdkResolution::from(later_sdk.clone())),
            _ => Err(SdkResolveError::NotFound),
        };
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(
                r#"<Project Sdk="First">
  <Import Sdk="Later" Project="Sdk.props" />
  {COPY_ASSEMBLY_VERSION}
</Project>"#
            ),
        );
        let result =
            parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
        assert_eq!(committed_seen(&result), expected, "first SDK {first}");
    }
}
