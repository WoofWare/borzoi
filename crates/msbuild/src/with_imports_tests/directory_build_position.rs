//! Where `Directory.Build.targets` lands relative to the entry SDK's
//! `Sdk.targets`.
//!
//! `Microsoft.Common.targets` imports this file, and the SDK's `Sdk.targets`
//! chain reaches that import *after*
//! `Microsoft.NET.TargetFrameworkInference.targets` has computed
//! `TargetFrameworkIdentifier` / `TargetFrameworkVersion`. So the walker lets
//! the chain place the import; a chain with no import point imports nothing,
//! and the walk walks the file itself only as an uncertain fallback for a
//! point it could not decide (`directory_build_import_point`).
//!
//! The tests here are about **the gate**, not about MSBuild's semantics: they
//! use synthetic SDKs, which the differential
//! (`tests/fsproj_derived_tfm_diff.rs`) structurally cannot reach — the oracle
//! has no resolver hook and would fail to resolve the name. Anything that is a
//! claim about *MSBuild* belongs there, where MSBuild adjudicates it; anything
//! that is a claim about *our* fallback belongs here.

use super::*;
use tempfile::TempDir;

/// A `Directory.Build.targets` that **appends** a record of what it could see
/// when it ran, in the style of the real gates this ordering feeds. Appending
/// rather than assigning is what makes a second walk visible.
const TRACE: &str = r#"<Project>
  <PropertyGroup>
    <Trace>$(Trace);dbt=[$(FromSdkTargets)]</Trace>
  </PropertyGroup>
</Project>"#;

#[test]
fn the_sdk_chains_own_import_places_the_file_once_after_what_sdk_targets_wrote() {
    // `Sdk.targets` writes a property and *then* imports
    // `Directory.Build.targets`, the shape `Microsoft.Common.targets` has.
    //
    // The trace **appends**, so it pins position and multiplicity in one
    // assertion, and both halves are load-bearing. Asserting only the final
    // witness value would pass for a walk that imported the file twice: the
    // second import, at the chain's position, would overwrite the first with
    // the right answer. Position is only really pinned once "exactly once" is
    // pinned with it.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "Chain.Sdk",
        "<Project></Project>",
        &format!(
            r#"<Project>
  <PropertyGroup>
    <FromSdkTargets>written</FromSdkTargets>
  </PropertyGroup>
  <Import Project="{}/Directory.Build.targets" />
</Project>"#,
            tmp.path().display()
        ),
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="Chain.Sdk">
  <PropertyGroup>
    <Trace>body</Trace>
  </PropertyGroup>
</Project>"#,
    );
    write_at(tmp.path(), "Directory.Build.targets", TRACE);

    let result = parse_file_with_sdk(&project_path, |_name| {
        Ok(SdkPaths {
            root: sdk_dir.clone(),
            props: props.clone(),
            targets: targets.clone(),
        })
    });
    assert_eq!(
        result.properties.get("Trace").map(String::as_str),
        Some("body;dbt=[written]"),
        "the chain imported the file itself, so it must run exactly once, at \
         the chain's position, seeing what `Sdk.targets` had already written"
    );
}

#[test]
fn an_sdk_that_never_imports_the_file_imports_none_of_it() {
    // An SDK whose targets do not reach `Microsoft.Common.targets` has no
    // import point, and the walk decided every gate it met, so MSBuild never
    // reads `Directory.Build.targets` either.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "Inert.Sdk",
        "<Project></Project>",
        r#"<Project>
  <PropertyGroup>
    <FromSdkTargets>written</FromSdkTargets>
  </PropertyGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="Inert.Sdk">
  <PropertyGroup>
    <Trace>body</Trace>
  </PropertyGroup>
</Project>"#,
    );
    write_at(tmp.path(), "Directory.Build.targets", TRACE);

    let result = parse_file_with_sdk(&project_path, |_name| {
        Ok(SdkPaths {
            root: sdk_dir.clone(),
            props: props.clone(),
            targets: targets.clone(),
        })
    });
    assert_eq!(
        result.properties.get("Trace").map(String::as_str),
        Some("body"),
        "no file of the chain imports it"
    );
    assert!(result.property("Trace").is_exact());
}

#[test]
fn an_sdkless_project_imports_no_targets_file() {
    // No SDK at all: nothing imports `Directory.Build.targets` into a bare
    // `<Project>` (#676).
    let tmp = TempDir::new().unwrap();
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project>
  <PropertyGroup>
    <Trace>body</Trace>
    <FromSdkTargets>from-body</FromSdkTargets>
  </PropertyGroup>
</Project>"#,
    );
    write_at(tmp.path(), "Directory.Build.targets", TRACE);

    let result = parse_file(&project_path);
    assert_eq!(
        result.properties.get("Trace").map(String::as_str),
        Some("body")
    );
    assert!(result.property("Trace").is_exact());
}

#[test]
fn a_gate_the_sdk_flips_after_its_import_point_does_not_reopen_the_fallback() {
    // `ImportDirectoryBuildTargets=false` in the body, flipped back to `true`
    // by `Sdk.targets` *after* the position `Microsoft.Common.targets` would
    // have imported the file. MSBuild never retries an import it has already
    // passed, so the file stays unimported — and the fallback must not read the
    // flipped-back value and import it.
    let tmp = TempDir::new().unwrap();
    let (sdk_dir, props, targets) = write_synthetic_sdk(
        tmp.path(),
        "Flip.Sdk",
        "<Project></Project>",
        r#"<Project>
  <PropertyGroup>
    <FromSdkTargets>written</FromSdkTargets>
    <ImportDirectoryBuildTargets>true</ImportDirectoryBuildTargets>
  </PropertyGroup>
</Project>"#,
    );
    let project_path = write_at(
        tmp.path(),
        "Demo.fsproj",
        r#"<Project Sdk="Flip.Sdk">
  <PropertyGroup>
    <Trace>body</Trace>
    <ImportDirectoryBuildTargets>false</ImportDirectoryBuildTargets>
  </PropertyGroup>
</Project>"#,
    );
    write_at(tmp.path(), "Directory.Build.targets", TRACE);

    let result = parse_file_with_sdk(&project_path, |_name| {
        Ok(SdkPaths {
            root: sdk_dir.clone(),
            props: props.clone(),
            targets: targets.clone(),
        })
    });
    assert_eq!(
        result.properties.get("Trace").map(String::as_str),
        Some("body"),
        "the body opted out, so the file must not be imported — a gate the SDK \
         flips after the import point has already gone past cannot revive it"
    );
}
