//! The toolset seeds' provenance rule, which is **two** rules that look like
//! one omission.
//!
//! `State::seed_toolset_properties` fills MSBuild's toolset properties once an
//! SDK resolves to the canonical dotnet layout. It handles two groups
//! differently, and the difference is deliberate even though the second reads
//! like a missing call:
//!
//! - **Reserved** (`MSBuildToolsPath`, `MSBuildBinPath`, `MSBuildToolsVersion`,
//!   `MSBuildRuntimeType`, `MSBuildAssemblyVersion`) — seeded *over* whatever the walk stored, and their
//!   provenance is scrubbed. Real MSBuild rejects a project write to these
//!   outright, so any value or taint the walk accumulated describes something
//!   no real evaluation ever sees.
//! - **Overridable** (`MSBuildSDKsPath`, `MSBuildExtensionsPath32`,
//!   `MSBuildExtensionsPath`) — seeded only into an empty slot, and their
//!   provenance is **left alone**. Real MSBuild honours a project write here,
//!   so a write the walker *refused* may really have set the property in the
//!   real build. The seed is then a fallback rather than the answer, and the
//!   mark saying so is correct. A write the walker never *saw* (behind an
//!   import it could not follow or decide) leaves no mark at all, so there the
//!   seed is withheld outright.
//!
//! Ground truth (dotnet 10.0.301, probed 2026-08-02, plain `<Project>` writing
//! each name and reading it back with `-getProperty`):
//!
//! ```text
//! <MSBuildToolsPath>/SPOOFED</…>         → error MSB4004: … reserved, and cannot be modified
//! <MSBuildSDKsPath>/SPOOFED</…>          → "/SPOOFED"
//! <MSBuildExtensionsPath32>/SPOOFED32</…> → "/SPOOFED32"
//! ```
//!
//! Without this test the asymmetry is prose, and the natural "tidy-up" —
//! giving the overridable seeds the same `apply_property_provenance(Clear)`
//! call the reserved ones get — silently converts a correct decline into a
//! wrong commit: the walker would publish its own fallback path as certain
//! while the real build used the project's value.

mod common;

use std::collections::HashMap;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::{
    LoadTimeError, ParsedProject, RejectionCause, RejectionCertainty, resolve_sdk, workloads,
};
use tempfile::TempDir;

/// Parse `body` with the real SDK resolver, so `seed_toolset_properties` runs.
fn parse_with_real_sdk(body: &str) -> ParsedProject {
    let tmp = TempDir::new().unwrap();
    let project_path = tmp.path().join("Demo.fsproj");
    std::fs::write(&project_path, body).expect("write project");
    parse_at_with_real_sdk(body, &project_path)
}

/// [`parse_with_real_sdk`] for a project already written at `project_path`,
/// beside whatever files it imports.
fn parse_at_with_real_sdk(body: &str, project_path: &std::path::Path) -> ParsedProject {
    let dotnet_root = common::dotnet_root_from_env();
    let (user_dotnet_root, overrides_present) = common::workload_env_from_process();
    let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        resolve_sdk(
            &dotnet_root,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present,
                resolver_switched_off: common::workload_resolver_switched_off_from_process(),
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(project_path, body)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        Some(&resolver as &borzoi_msbuild::SdkResolver<'_>),
        None,
    )
    .expect("well-formed XML parses")
}

/// A document whose body writes `name` under a condition the walker cannot
/// decide, *before* any SDK resolves — so the refused write lands before
/// `seed_toolset_properties` and the seed meets a name that is unset but
/// marked.
///
/// The entry deliberately has no `Sdk` attribute: with one, the SDK resolves
/// (and seeds) before the body is ever walked, and the ordering this test is
/// about cannot arise.
///
/// `'$(X)É' == '$(X)é'` is ordinary MSBuild that this crate does not
/// model (case folding outside ASCII), and MSBuild evaluates it **true**,
/// throwing on nothing — so the real build performs the write.
fn refused_write_before_the_sdk(name: &str) -> String {
    format!(
        r#"<Project>
  <PropertyGroup>
    <X>abc</X>
    <{name} Condition="'$(X)É' == '$(X)é'">/SPOOFED</{name}>
  </PropertyGroup>
  <Import Sdk="Microsoft.NET.Sdk" Project="Sdk.props" />
</Project>"#
    )
}

#[test]
fn an_overridable_toolset_seed_keeps_a_refused_writes_uncertainty() {
    // MSBuild would have taken `/SPOOFED`. We could not decide the condition,
    // so we hold our own computed path — which is only a guess. The seed must
    // not launder it into a certainty.
    for name in ["MSBuildSDKsPath", "MSBuildExtensionsPath32"] {
        let parsed = parse_with_real_sdk(&refused_write_before_the_sdk(name));
        assert!(
            parsed.property(name).untrusted_cause().is_some(),
            "{name} takes a project write in the real build, so a refused write \
             to it must leave the toolset seed untrusted",
        );
    }
}

#[test]
fn a_write_to_a_reserved_toolset_name_rejects_the_project() {
    // The mirror. MSBuild refuses a file that writes a reserved name, whatever
    // the write's condition holds (MSB4004, #888), so the project has no
    // evaluation and the seed is withdrawn with everything else.
    let parsed = parse_with_real_sdk(&refused_write_before_the_sdk("MSBuildToolsPath"));
    let rejection = parsed
        .rejection
        .as_ref()
        .expect("MSB4004 rejects the project");
    assert_eq!(rejection.certainty, RejectionCertainty::Certain);
    assert!(
        matches!(
            &rejection.cause,
            RejectionCause::LoadTime(LoadTimeError::ReservedProperty { name })
                if name == "MSBuildToolsPath"
        ),
        "{rejection:#?}"
    );
    assert!(!parsed.property("MSBuildToolsPath").is_exact());
}

/// The other way a slot can be taken before the first SDK resolves: an import
/// whose gate the walker cannot decide, so the write inside it is one the walk
/// never saw and left no mark for. Real MSBuild decides the gate, performs the
/// write and keeps it, so an overridable seed there is a wrong commit unless
/// it is withheld.
///
/// Withholding is not the end of it: the name then reads as undefined, and the
/// SDK's `Condition="'$(Name)' == ''"` default idiom must not take that absence
/// as a fact either, since the real build holds a value (the hidden one, or the
/// toolset's own when the hidden import writes nothing). So the grid crosses
/// what the hidden import holds with how the body reads the name.
///
/// Graded against MSBuild, and the fixture's own claim (that the real build
/// reads the hidden value) is pinned too, so a gate MSBuild happened to
/// decide false cannot make the case pass vacuously.
///
/// `MSBuildExtensionsPath` is left out here: steering it at a decoy breaks the
/// real `Sdk.props` import, so MSBuild rejects the document and grades
/// nothing. `nuget_props_chain.rs` covers it against a decoy toolset tree.
#[test]
fn an_overridable_toolset_seed_is_withheld_behind_an_undecided_import() {
    let mut oracle = common::Oracle::spawn();
    // `Microsoft.Common.CurrentVersion.targets` compares `VisualStudioVersion`
    // numerically, so its spoof must be a number or MSBuild rejects the
    // document (MSB4086).
    for (name, spoof) in [
        ("MSBuildSDKsPath", "/SPOOFED"),
        ("MSBuildExtensionsPath32", "/SPOOFED"),
        ("VisualStudioVersion", "99.0"),
    ] {
        for hidden_writes in [true, false] {
            for default_fill in [false, true] {
                let tmp = TempDir::new().unwrap();
                let hidden = if hidden_writes {
                    format!("<PropertyGroup><{name}>{spoof}</{name}></PropertyGroup>")
                } else {
                    String::new()
                };
                std::fs::write(
                    tmp.path().join("hidden.props"),
                    format!("<Project>{hidden}</Project>"),
                )
                .expect("write hidden import");
                let fill = if default_fill {
                    format!("<{name} Condition=\"'$({name})' == ''\">/FALLBACK</{name}>")
                } else {
                    String::new()
                };
                let project_path = tmp.path().join("Demo.fsproj");
                let body = format!(
                    r#"<Project>
  <PropertyGroup>
    <X>abc</X>
    <TargetFramework>net10.0</TargetFramework>
  </PropertyGroup>
  <Import Project="hidden.props" Condition="'$(X)É' == '$(X)é'" />
  <Import Sdk="Microsoft.NET.Sdk" Project="Sdk.props" />
  <PropertyGroup>
    {fill}
    <Probe>$({name})</Probe>
  </PropertyGroup>
  <Import Sdk="Microsoft.NET.Sdk" Project="Sdk.targets" />
</Project>"#
                );
                std::fs::write(&project_path, &body).expect("write project");
                let case =
                    format!("{name}, hidden write {hidden_writes}, default fill {default_fill}");
                let parsed = parse_at_with_real_sdk(&body, &project_path);
                let theirs = oracle
                    .project(&body, &["Probe".to_string()], Some(&project_path), &[])
                    .unwrap_or_else(|| panic!("{case}: MSBuild rejects the fixture"));
                let theirs = theirs.get("Probe").map(String::as_str);
                if hidden_writes {
                    assert_eq!(
                        theirs,
                        Some(spoof),
                        "{case}: the fixture rests on the real build performing the hidden write",
                    );
                } else {
                    assert_ne!(
                        theirs,
                        Some("/FALLBACK"),
                        "{case}: the fixture rests on the real build holding the toolset's value",
                    );
                }
                let ours = parsed.properties.get("Probe").map(String::as_str);
                assert!(
                    parsed.property("Probe").untrusted_cause().is_some() || ours == theirs,
                    "certain-implies-exact violated for {case}: we committed {ours:?}, \
                     MSBuild reads {theirs:?}",
                );
            }
        }
    }
}
