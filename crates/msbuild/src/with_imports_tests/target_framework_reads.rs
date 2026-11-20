//! An undefined `$(TargetFramework)` read made before the project body defines
//! the property — the Web SDK's `Sdk.props` gates `Sdk.Server.props` on
//! `GetTargetPlatformIdentifier($(TargetFramework))` there. The read is exactly
//! `""` in MSBuild, whatever the body later writes, unless a global supplies
//! the name: a cross-targeting outer evaluation reads it unset as well. It is
//! trusted by the rule any undefined read is (`undefined_read_is_exact`):
//! unless content the walk could not see came first, or the environment or a
//! refused write may define it.

use super::*;
use tempfile::TempDir;

/// The import gate the SDK's props evaluate before the body runs.
const GATES: &[&str] = &[
    "'$([MSBuild]::GetTargetPlatformIdentifier($(TargetFramework)))' != 'browser'",
    "'$(TargetFramework)' != 'net8.0'",
];

/// One body shape, under which the gate's read must be trusted.
struct Body {
    name: &'static str,
    property_group: &'static str,
    globals: &'static [(&'static str, &'static str)],
}

const BODIES: &[Body] = &[
    Body {
        name: "single TFM",
        property_group: "<TargetFramework>net10.0</TargetFramework>",
        globals: &[],
    },
    // `TargetFramework` wins over `TargetFrameworks`: MSBuild's
    // `IsCrossTargetingBuild` is false, so this evaluation is still the build.
    Body {
        name: "both singular and plural",
        property_group: "<TargetFrameworks>net8.0;net10.0</TargetFrameworks>\
                         <TargetFramework>net10.0</TargetFramework>",
        globals: &[],
    },
    Body {
        name: "cross-targeting",
        property_group: "<TargetFrameworks>net8.0;net10.0</TargetFrameworks>",
        globals: &[],
    },
    // Written, then cleared, after the read.
    Body {
        name: "written then cleared",
        property_group: "<TargetFrameworks>net8.0;net10.0</TargetFrameworks>\
                         <TargetFramework>net10.0</TargetFramework>\
                         <TargetFramework></TargetFramework>",
        globals: &[],
    },
    // Written only under a gate the walk cannot decide, after the read: the
    // read sees it unset either way.
    Body {
        name: "written under an undecided gate",
        property_group: "<TargetFrameworks>net8.0;net10.0</TargetFrameworks>\
                         <TargetFramework Condition=\"'É' == 'é'\">net10.0</TargetFramework>",
        globals: &[],
    },
    Body {
        name: "no TFM at all",
        property_group: "",
        globals: &[],
    },
    // An inner build: the global is defined at the gate, so nothing is read
    // undefined in the first place.
    Body {
        name: "TargetFramework global",
        property_group: "<TargetFrameworks>net8.0;net10.0</TargetFrameworks>",
        globals: &[("TargetFramework", "net10.0")],
    },
];

#[test]
fn a_pre_body_target_framework_read_is_trusted_whatever_the_body_writes() {
    for gate in GATES {
        for body in BODIES {
            let tmp = TempDir::new().unwrap();
            let (root, props, targets) = write_synthetic_sdk(
                tmp.path(),
                "MySdk",
                &format!(
                    r#"<Project><Import Project="server.props" Condition="{gate}" /></Project>"#
                ),
                "<Project/>",
            );
            write_at(
                &root,
                "server.props",
                r#"<Project><ItemGroup><FrameworkReference Include="Microsoft.AspNetCore.App" /></ItemGroup></Project>"#,
            );
            let source = format!(
                r#"<Project Sdk="MySdk"><PropertyGroup>{}</PropertyGroup></Project>"#,
                body.property_group
            );
            let project_path = write_at(tmp.path(), "Demo.fsproj", &source);
            let resolver = |name: &str, _observer: &crate::observed::Observer| {
                if name == "MySdk" {
                    Ok(SdkResolution::from(SdkPaths {
                        root: root.clone(),
                        props: props.clone(),
                        targets: targets.clone(),
                    }))
                } else {
                    Err(SdkResolveError::NotFound)
                }
            };
            let globals: HashMap<String, String> = body
                .globals
                .iter()
                .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
                .collect();
            let result = parse_fsproj_with_imports(
                &crate::ProjectFile::buffer(&canon(&project_path), &source)
                    .expect("a project path spelt as its full path"),
                &globals,
                &HashMap::new(),
                Some(&resolver),
                None,
            )
            .expect("well-formed XML parses");
            let context = format!(
                "gate {gate} / body {:?}; causes: {:#?}",
                body.name, result.package_reference_uncertainties
            );
            assert!(!result.package_references_uncertain, "{context}");
            let names: Vec<&str> = result
                .framework_references
                .iter()
                .map(|f| f.name.as_str())
                .collect();
            // Every TFM the bodies name passes both gates.
            assert_eq!(names, ["Microsoft.AspNetCore.App"], "{context}");
        }
    }
}

/// The same read after content the walk could not see, which may define
/// `TargetFramework` first: not exact, so the gate is not decided.
#[test]
fn a_pre_body_target_framework_read_after_hidden_content_is_not_trusted() {
    let tmp = TempDir::new().unwrap();
    let (root, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "MySdk",
        r#"<Project>
  <PropertyGroup><UndecidedX>abc</UndecidedX></PropertyGroup>
  <Import Project="hidden.props" Condition="'$(UndecidedX)É' == '$(UndecidedX)é'" />
  <Import Project="server.props" Condition="'$(TargetFramework)' != 'net8.0'" />
</Project>"#,
        "<Project/>",
    );
    write_at(
        &root,
        "hidden.props",
        "<Project><PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup></Project>",
    );
    write_at(
        &root,
        "server.props",
        r#"<Project><ItemGroup><FrameworkReference Include="Microsoft.AspNetCore.App" /></ItemGroup></Project>"#,
    );
    let source = r#"<Project Sdk="MySdk"><PropertyGroup><TargetFrameworks>net8.0;net10.0</TargetFrameworks></PropertyGroup></Project>"#;
    let project_path = write_at(tmp.path(), "Demo.fsproj", source);
    let resolver = |name: &str, _observer: &crate::observed::Observer| {
        if name == "MySdk" {
            Ok(SdkResolution::from(SdkPaths {
                root: root.clone(),
                props: props.clone(),
                targets: targets.clone(),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let result = parse_fsproj_with_imports(
        &crate::ProjectFile::buffer(&canon(&project_path), source)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &HashMap::new(),
        Some(&resolver),
        None,
    )
    .expect("well-formed XML parses");
    assert!(
        result.package_references_uncertain,
        "MSBuild reads `TargetFramework` as `net8.0` and skips `server.props`; we published {:?}",
        result.framework_references
    );
}
