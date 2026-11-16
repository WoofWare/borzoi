//! A name resolved across `global.json` `sdk.paths` roots, held to
//! `dotnet msbuild` (#912).
//!
//! hostfxr runs the SDK from the first root holding a version the `sdk` block
//! admits (`borzoi-msbuild`'s `sdk_paths_root_choice_diff` measures the root
//! it picks), and MSBuild serves a name from that SDK or fails: it never
//! consults a later root's copy. So where the first root's SDK lacks the name
//! and a later root's has it, the build fails (MSB4236), and
//! `SdkDiscovery::resolve` must say `NotFound` rather than resolve the later
//! copy.
//!
//! Each root is a runnable copy of the devshell's install: every SDK
//! version's `dotnet.dll` copied (the directory MSBuild reports is where it
//! loads from), its `Sdks` a directory of links, and everything else linked.
//! A copy may hold `Contoso.Sdk`, whose `Sdk.props` names its root, or hold
//! only an SDK version the pin does not admit, or no SDK at all.
#![cfg(unix)]

use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::common;
use crate::common::host_fs;
use borzoi::sdk_discovery::SdkDiscovery;
use borzoi_msbuild::observed::Observer;
use borzoi_msbuild::{SdkResolution, SdkResolveError, SdkVersion};
use borzoi_spawn::BoundedCommand;

const SDK: &str = "Contoso.Sdk";

/// What a root holds.
#[derive(Clone, Copy, Debug)]
enum Root {
    /// The install, its highest SDK holding `Contoso.Sdk`.
    WithName,
    /// The install, without `Contoso.Sdk`.
    WithoutName,
    /// Only an SDK version below the pin (which cannot run).
    BelowThePin,
    /// No `sdk` directory.
    Empty,
}

/// The highest installed SDK version directory's name under `real`.
fn highest_version(real: &Path) -> String {
    host_fs::read_dir(real.join("sdk"))
        .unwrap()
        .filter_map(|e| e.ok())
        .filter_map(|e| {
            let name = e.file_name().to_str()?.to_owned();
            Some((SdkVersion::parse(&name)?, name))
        })
        .max()
        .expect("an installed SDK")
        .1
}

/// Write a root at `at` holding `what`, from the install `real`.
fn write_root(real: &Path, at: &Path, what: Root, label: &str) {
    std::fs::create_dir_all(at).unwrap();
    match what {
        Root::Empty => return,
        Root::BelowThePin => {
            let dir = at.join("sdk").join("1.0.100");
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join("dotnet.dll"), "").unwrap();
            return;
        }
        Root::WithName | Root::WithoutName => {}
    }
    for entry in host_fs::read_dir(real).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() != "sdk" {
            symlink(entry.path(), at.join(entry.file_name())).unwrap();
        }
    }
    let version = highest_version(real);
    let ours = at.join("sdk").join(&version);
    std::fs::create_dir_all(ours.join("Sdks")).unwrap();
    for entry in host_fs::read_dir(real.join("sdk").join(&version)).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == "dotnet.dll" {
            std::fs::copy(entry.path(), ours.join(&name)).unwrap();
        } else if name != "Sdks" {
            symlink(entry.path(), ours.join(&name)).unwrap();
        }
    }
    for sdk in host_fs::read_dir(real.join("sdk").join(&version).join("Sdks")).unwrap() {
        let sdk = sdk.unwrap();
        symlink(sdk.path(), ours.join("Sdks").join(sdk.file_name())).unwrap();
    }
    if matches!(what, Root::WithName) {
        let dir = ours.join("Sdks").join(SDK).join("Sdk");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("Sdk.props"),
            format!("<Project><PropertyGroup><Picked>{label}</Picked></PropertyGroup></Project>"),
        )
        .unwrap();
        std::fs::write(dir.join("Sdk.targets"), "<Project />").unwrap();
    }
}

/// The real build's `Picked`, or `None` when it fails.
fn built(dotnet: &Path, project: &Path) -> Option<String> {
    let mut cmd = Command::new(dotnet);
    cmd.current_dir(project.parent().unwrap())
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("HOME", std::env::var_os("HOME").unwrap_or_default())
        .env("DOTNET_CLI_TELEMETRY_OPTOUT", "1")
        .env("DOTNET_NOLOGO", "1")
        .env("MSBuildEnableWorkloadResolver", "false")
        .args(["msbuild", "-nologo", "-getProperty:Picked"])
        .arg(project);
    let out = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(300))
        .run()
        .expect("dotnet msbuild runs");
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

#[test]
fn a_name_resolves_only_from_the_root_hostfxr_runs() {
    let real = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    );
    let dotnet = real.join("dotnet");
    let version = highest_version(&real);
    let scratch = tempfile::TempDir::new().unwrap();
    let base = host_fs::canonicalize(scratch.path()).unwrap();
    let nuget = base.join("nuget");
    std::fs::create_dir_all(&nuget).unwrap();
    let cases = [
        // #912: the first root runs an SDK without the name.
        (Root::WithoutName, Root::WithName),
        (Root::WithName, Root::WithoutName),
        (Root::WithName, Root::WithName),
        (Root::Empty, Root::WithName),
        (Root::BelowThePin, Root::WithName),
        (Root::BelowThePin, Root::WithoutName),
    ];
    let mut failures = Vec::new();
    for (index, (first, second)) in cases.iter().enumerate() {
        let case = base.join(format!("case{index}"));
        write_root(&real, &case.join("first"), *first, "first");
        write_root(&real, &case.join("second"), *second, "second");
        let project_dir = case.join("project");
        std::fs::create_dir_all(&project_dir).unwrap();
        std::fs::write(
            project_dir.join("global.json"),
            format!(
                "{{\"sdk\": {{\"paths\": [\"../first\", \"../second\"], \"version\": \
                 \"{version}\", \"rollForward\": \"latestFeature\"}}}}"
            ),
        )
        .unwrap();
        let project = project_dir.join("p.proj");
        std::fs::write(&project, format!("<Project Sdk=\"{SDK}\"></Project>")).unwrap();

        let env = common::sdk_oracle_discovery_env(&nuget, real.clone());
        let ours = SdkDiscovery::for_project(&project, &env, &Observer::new())
            .expect("discovery")
            .resolve(SDK, &Observer::new());
        let ours = match ours {
            Ok(SdkResolution::Single(paths)) => Some(Some({
                // The root is joined to `..`, which the file system collapses.
                let root = host_fs::canonicalize(&paths.root).unwrap();
                if root.starts_with(case.join("first")) {
                    "first"
                } else if root.starts_with(case.join("second")) {
                    "second"
                } else {
                    "elsewhere"
                }
                .to_owned()
            })),
            Err(SdkResolveError::NotFound | SdkResolveError::VersionNotSatisfied { .. }) => {
                Some(None)
            }
            // A decline makes no claim.
            other => {
                println!("{first:?}, {second:?}: we decline: {other:?}");
                None
            }
        };
        let theirs = built(&dotnet, &project);
        println!("{first:?}, {second:?}: ours {ours:?}, MSBuild {theirs:?}");
        if let Some(ours) = ours
            && ours != theirs
        {
            failures.push(format!(
                "{first:?}, {second:?}: we resolve {ours:?}, MSBuild {theirs:?}"
            ));
        }
        let _ = std::fs::remove_dir_all(&case);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
