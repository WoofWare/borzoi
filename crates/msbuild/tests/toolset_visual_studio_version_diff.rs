//! The `VisualStudioVersion` the walk seeds for an SDK, held to what that
//! SDK's MSBuild defines.
//!
//! The walk seeds the toolset's `VisualStudioVersion` from the host SDK's
//! version (`toolset_visual_studio_version`), because MSBuild compiles it in
//! and a read of it decides imports and writes on every SDK chain. This test
//! asks `dotnet msbuild -getProperty:VisualStudioVersion` of every SDK in the
//! devshell's corpus root (`BORZOI_DOTNET_ROOT_SDK11`), with none in the
//! environment, and requires the seed to be exactly that value: a seed that
//! differs is a wrong commit, and a missing one leaves every SDK chain read of
//! the name declining. So adding an SDK to the devshell fails here until its
//! value is probed and recorded.

mod common;

use std::path::PathBuf;
use std::process::Command;

use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::observed::host_fs::HostPath as _;
use borzoi_msbuild::test_support;
use borzoi_oracle_harness::BoundedCommand;

const SDK11_ROOT_VAR: &str = "BORZOI_DOTNET_ROOT_SDK11";

#[test]
fn every_installed_sdk_seeds_its_msbuild_s_visual_studio_version() {
    let root = std::env::var_os(SDK11_ROOT_VAR)
        .map(PathBuf::from)
        .unwrap_or_else(|| panic!("{SDK11_ROOT_VAR} is not set; run under nix develop"));
    let mut sdks: Vec<PathBuf> = host_fs::read_dir(root.join("sdk"))
        .expect("the corpus root has an sdk directory")
        .map(|entry| entry.expect("sdk directory entry").path())
        .filter(|path| path.join("MSBuild.dll").host_is_file())
        .collect();
    sdks.sort();
    assert!(!sdks.is_empty(), "no SDK under {}", root.display());
    let mut environment = common::oracle_environment();
    environment.remove("VisualStudioVersion");
    environment.insert(
        "DOTNET_ROOT".to_owned(),
        root.to_string_lossy().into_owned(),
    );
    for sdk in sdks {
        let version = sdk.file_name().unwrap().to_str().unwrap().to_owned();
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(
            dir.path().join("global.json"),
            format!(
                r#"{{"sdk":{{"version":"{version}","rollForward":"disable","allowPrerelease":true}}}}"#
            ),
        )
        .unwrap();
        std::fs::write(
            dir.path().join("p.proj"),
            r#"<Project><Target Name="Nothing" /></Project>"#,
        )
        .unwrap();
        let mut cmd = Command::new(root.join("dotnet"));
        cmd.current_dir(dir.path())
            .env_clear()
            .envs(&environment)
            .args([
                "msbuild",
                "-nologo",
                "-getProperty:VisualStudioVersion",
                "p.proj",
            ]);
        let out = BoundedCommand::new(cmd)
            .timeout(std::time::Duration::from_secs(600))
            .run_ok(format_args!("dotnet msbuild under SDK {version}"));
        let theirs = String::from_utf8(out.stdout).expect("UTF-8 output");
        let theirs = theirs.trim();
        assert!(
            !theirs.is_empty(),
            "SDK {version}'s MSBuild defines VisualStudioVersion"
        );
        assert_eq!(
            test_support::toolset_visual_studio_version(&sdk),
            Some(theirs),
            "SDK {version}: the seed must be what its MSBuild defines"
        );
    }
}
