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

/// A toolset seed filling a slot a refused write emptied is no rewrite: the
/// project's `String.Copy('1.0')` to `MSBuildExtensionsPath32` is refused,
/// the SDK then seeds its own path there, and the second walk, which sets a
/// rewrite's refusal aside, must not read the seed as the build's value. The
/// build holds `1.0`, so the metadatum's gate holds, and its `$(P[9])` on
/// `P`'s final `z` rejects the project (MSB4184; #1153).
#[test]
fn a_seed_in_a_refused_slot_is_no_rewrite() {
    // The seed as it stands, and the seed copied into its own slot after the
    // SDK, which reads the refused name.
    // The seeded name gating a metadatum, and as the operand before the throw
    // in one condition, which MSBuild reaches on its `1.0`.
    let items = [
        "<I Include=\"x\"><M Condition=\"'$(MSBuildExtensionsPath32)' == '1.0'\">$(P[9])</M></I>",
        "<I Include=\"x\" Condition=\"'$(MSBuildExtensionsPath32)' == '1.0' And '$(P[9])' != ''\" />",
    ];
    for (copy, item) in [
        "",
        "<PropertyGroup><MSBuildExtensionsPath32>$(MSBuildExtensionsPath32)</MSBuildExtensionsPath32></PropertyGroup>",
    ]
    .into_iter()
    .flat_map(|copy| items.map(|item| (copy, item)))
    {
        let tmp = TempDir::new().unwrap();
        let resolver = canonical_sdk(tmp.path(), "10.0.100");
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(
                "<Project>\
         <Choose><When Condition=\"'É' == 'é'\"><PropertyGroup><P>abcdefghijkl</P></PropertyGroup>\
         <ItemGroup>{item}</ItemGroup></When></Choose>\
         <PropertyGroup><MSBuildExtensionsPath32>$([System.String]::Copy('1.0'))</MSBuildExtensionsPath32>\
         <P>@(J)</P><P>z</P></PropertyGroup>\
         <Import Project=\"Sdk.props\" Sdk=\"MySdk\" />{copy}\
         <PropertyGroup><After>ok</After></PropertyGroup></Project>"
            ),
        );
        let result =
            parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
        assert!(
            result.rejection.is_some(),
            "{copy} {item}: {:#?}",
            result.diagnostics
        );
    }
}

/// Nor does another name's rewrite make the seed the build's value: the
/// project rewrites `P` after a refusal, so the second walk runs (`K`'s text,
/// whose throws the two walks name apart, adopts `$(P[9])`), but it holds
/// `MSBuildExtensionsPath32`, whose refused slot the SDK seeded, as doubtful
/// as the first does. So in `I`'s text it names the certain `$(S[9])`, as
/// the first walk does, never `VersionEquals` on the seed's directory, where
/// the build compares its `1.0` and evaluates true (#1153).
#[test]
fn another_names_rewrite_leaves_a_seed_doubted() {
    // The seed as it stands, and copied into its own slot after the SDK.
    for copy in [
        "",
        "<PropertyGroup><MSBuildExtensionsPath32>$(MSBuildExtensionsPath32)</MSBuildExtensionsPath32></PropertyGroup>",
    ] {
        let tmp = TempDir::new().unwrap();
        let resolver = canonical_sdk(tmp.path(), "10.0.100");
        let project_path = write_at(
            tmp.path(),
            "Demo.fsproj",
            &format!(
                "<Project>\
         <PropertyGroup><MSBuildExtensionsPath32>1.0</MSBuildExtensionsPath32>\
         <MSBuildExtensionsPath32>$([System.String]::Copy('1.0'))</MSBuildExtensionsPath32>\
         <P>@(J)</P><P>z</P><S>a</S></PropertyGroup>\
         <Import Project=\"Sdk.props\" Sdk=\"MySdk\" />{copy}\
         <ItemGroup><I Include=\"$([MSBuild]::VersionEquals('$(MSBuildExtensionsPath32)', '1.0'))$(S[9])\" />\
         <K Include=\"$(P[9])$(S[9])\" /></ItemGroup>\
         <PropertyGroup><After>ok</After></PropertyGroup></Project>"
            ),
        );
        let result =
            parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
        assert_eq!(
            noted_causes(&result),
            ["$(S[9])", "$(S[9])", "$(P[9])"],
            "{copy}: {:#?}",
            result.diagnostics
        );
    }
}

/// A rewrite that held is undone by a later write that copies a seed: `P`
/// is refused, rewritten to `z`, then given the seeded
/// `MSBuildExtensionsPath32`, and the second walk holds it as doubtful as the
/// first does. So in `I`'s text each walk names the certain `$(S[9])`, never
/// `VersionEquals('$(P)', '1.0')` on the seed's directory, which the build,
/// holding the project's `1.0` there, evaluates true (#1153).
#[test]
fn a_seed_copied_over_a_rewrite_undoes_it() {
    let tmp = TempDir::new().unwrap();
    let resolver = canonical_sdk(tmp.path(), "10.0.100");
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        "<Project>\
         <PropertyGroup><MSBuildExtensionsPath32>$([System.String]::Copy('1.0'))</MSBuildExtensionsPath32>\
         <P>@(J)</P><P>z</P><S>a</S></PropertyGroup>\
         <Import Project=\"Sdk.props\" Sdk=\"MySdk\" />\
         <PropertyGroup><P>$(MSBuildExtensionsPath32)</P><After>ok</After></PropertyGroup>\
         <ItemGroup><I Include=\"$([MSBuild]::VersionEquals('$(P)', '1.0'))$(S[9])\" /></ItemGroup></Project>",
    );
    let result = parse_file_with_sdk_env(&project_path, resolver, HashMap::new(), HashMap::new());
    assert_eq!(
        noted_causes(&result),
        ["$(S[9])"],
        "{:#?}",
        result.diagnostics
    );
}

/// The expression each rejection site `result` notes throws on, in order.
fn noted_causes(result: &ParsedProject) -> Vec<String> {
    result
        .diagnostics
        .iter()
        .filter_map(|d| match &d.kind {
            DiagnosticKind::Rejected {
                cause: RejectionCause::ThrowingExpression { expression },
            }
            | DiagnosticKind::MayBeRejected {
                cause: RejectionCause::ThrowingExpression { expression },
            } => Some(expression.clone()),
            _ => None,
        })
        .collect()
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
