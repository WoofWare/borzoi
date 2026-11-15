//! The one way a test here builds a [`Workspace`], which refuses an
//! environment that would evaluate a real SDK's import chain opaquely.
//!
//! `Microsoft.Common.props` gates its user-extension imports on
//! `MSBuildUserExtensionsPath`, a property MSBuild computes for itself. The
//! server supplies it in [`SdkDiscoveryEnv::build_environment`]
//! ([`SdkDiscoveryEnv::from_process_env`]); a hand-built environment
//! (`SdkDiscoveryEnv { dotnet_root, ..SdkDiscoveryEnv::default() }`) has an
//! empty one. Over a real SDK the undefined read latches the walk opaque at the
//! top of every SDK chain, which withdraws the Compile set and the reference
//! list, so the test grades a degraded evaluation the server never serves. A
//! test that asserts only what survives that decline stays green, so nothing
//! else would say so.
//!
//! [`workspaces_are_built_here`] holds every case group to these constructors,
//! and [`missing_msbuild_environment`] is what they check.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use borzoi::sdk_discovery::SdkDiscoveryEnv;
use borzoi::workspace::Workspace;

use super::host_fs;

/// The property MSBuild computes and the user-extension gates read.
const USER_EXTENSIONS: &str = "MSBuildUserExtensionsPath";

/// A [`Workspace`] over `env`. Panics if `env` reaches a real SDK without the
/// property environment the server computes ([`missing_msbuild_environment`]).
pub fn workspace(env: SdkDiscoveryEnv) -> Workspace {
    workspace_with_build_properties(env, HashMap::new())
}

/// [`workspace`], with `extra` as MSBuild global properties
/// ([`Workspace::with_env_and_extra_build_properties`]).
pub fn workspace_with_build_properties(
    env: SdkDiscoveryEnv,
    extra: HashMap<String, String>,
) -> Workspace {
    if let Some(why) = missing_msbuild_environment(&env) {
        panic!("{why}");
    }
    Workspace::with_env_and_extra_build_properties(env, extra)
}

/// Why `env` would evaluate a real SDK's import chain opaquely, or `None`.
///
/// `env` reaches a real SDK when its `dotnet_root` holds an SDK whose
/// `Microsoft.Common.props` reads `MSBuildUserExtensionsPath`, or when it has
/// no `dotnet_root` and searches a `PATH`, where discovery may find the host's.
/// It then needs that property in its `build_environment`, under any case, as
/// MSBuild reads property names. A stub SDK without that file is not a real
/// one: nothing in it reads the property. An SDK a project's `global.json`
/// names by path is not seen here.
pub fn missing_msbuild_environment(env: &SdkDiscoveryEnv) -> Option<String> {
    let carried = env
        .build_environment
        .keys()
        .any(|name| name.eq_ignore_ascii_case(USER_EXTENSIONS));
    if carried {
        return None;
    }
    let reached = match &env.dotnet_root {
        Some(root) => sdks_reading_user_extensions(root).into_iter().next(),
        None => env
            .search_path
            .as_ref()
            .map(|_| PathBuf::from("the dotnet on its PATH")),
    }?;
    Some(format!(
        "this environment reaches a real SDK ({}) with no {USER_EXTENSIONS} in its \
         build_environment, so every SDK project would evaluate opaquely, without \
         its Compile set or reference list. Build it from \
         `SdkDiscoveryEnv::from_process_env()`, which computes the property as the \
         server does, or point `dotnet_root` at a stub SDK",
        reached.display()
    ))
}

/// The `Microsoft.Common.props` of each SDK under `dotnet_root` that reads
/// `MSBuildUserExtensionsPath`.
fn sdks_reading_user_extensions(dotnet_root: &Path) -> Vec<PathBuf> {
    let Ok(sdks) = host_fs::read_dir(dotnet_root.join("sdk")) else {
        return Vec::new();
    };
    sdks.filter_map(Result::ok)
        .map(|sdk| sdk.path().join("Current").join("Microsoft.Common.props"))
        .filter(|props| {
            host_fs::read_to_string(props).is_ok_and(|text| text.contains(USER_EXTENSIONS))
        })
        .collect()
}

/// The devshell's `$DOTNET_ROOT`: a real SDK install.
fn real_dotnet_root() -> PathBuf {
    std::env::var_os("DOTNET_ROOT")
        .map(PathBuf::from)
        .expect("DOTNET_ROOT unset (run under `nix develop`)")
}

/// The check recognises the devshell's SDK as real, so it is not vacuous: if
/// the SDK layout moved `Microsoft.Common.props`, or stopped gating on the
/// property, this fails rather than the check going quiet.
#[test]
fn a_real_sdk_without_the_property_environment_is_refused() {
    let root = real_dotnet_root();
    assert!(
        !sdks_reading_user_extensions(&root).is_empty(),
        "no SDK under {} has a Microsoft.Common.props reading {USER_EXTENSIONS}",
        root.display()
    );
    let bare = SdkDiscoveryEnv {
        dotnet_root: Some(root.clone()),
        ..SdkDiscoveryEnv::default()
    };
    assert!(missing_msbuild_environment(&bare).is_some());
    let searching = SdkDiscoveryEnv {
        search_path: std::env::var_os("PATH"),
        ..SdkDiscoveryEnv::default()
    };
    assert!(missing_msbuild_environment(&searching).is_some());
    let served = SdkDiscoveryEnv {
        dotnet_root: Some(root),
        ..SdkDiscoveryEnv::from_process_env()
    };
    assert_eq!(missing_msbuild_environment(&served), None);
}

/// An environment that finds no SDK, or only a stub, needs no property
/// environment.
#[test]
fn an_environment_without_a_real_sdk_is_accepted() {
    let tmp = tempfile::TempDir::new().unwrap();
    assert_eq!(
        missing_msbuild_environment(&SdkDiscoveryEnv::default()),
        None
    );
    let stub = tmp.path().join("dotnet");
    let sdk = stub.join("sdk/10.0.100/Sdks/Microsoft.NET.Sdk/Sdk");
    std::fs::create_dir_all(&sdk).unwrap();
    std::fs::write(sdk.join("Sdk.props"), "<Project/>").unwrap();
    let env = SdkDiscoveryEnv {
        dotnet_root: Some(stub),
        ..SdkDiscoveryEnv::default()
    };
    assert_eq!(missing_msbuild_environment(&env), None);
}

/// Every case group builds its workspaces through [`workspace`] or
/// [`workspace_with_build_properties`], so each is checked. A call to one of
/// `Workspace`'s own constructors that take an environment, outside this
/// module, fails here naming its line. `Workspace::new` reads the process
/// environment as the server does, so it stays allowed.
#[test]
fn workspaces_are_built_here() {
    let all = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("all");
    let this = all.join("common").join("workspace.rs");
    // Spelled in pieces so this file's own source does not match.
    let constructors = [
        "with_env(",
        "with_env_and_extra_build_properties(",
        "default()",
    ]
    .map(|tail| format!("Workspace::{tail}"));
    let mut found = Vec::new();
    let mut pending = vec![all.clone()];
    while let Some(dir) = pending.pop() {
        for entry in host_fs::read_dir(&dir).unwrap().filter_map(Result::ok) {
            let path = entry.path();
            if host_fs::metadata(&path).unwrap().is_dir() {
                pending.push(path);
                continue;
            }
            if path.extension().is_none_or(|ext| ext != "rs") || path == this {
                continue;
            }
            let text = host_fs::read_to_string(&path).unwrap();
            for (index, line) in text.lines().enumerate() {
                if line.trim_start().starts_with("//") {
                    continue;
                }
                if constructors.iter().any(|c| line.contains(c.as_str())) {
                    found.push(format!(
                        "{}:{}: {}",
                        path.strip_prefix(&all).unwrap().display(),
                        index + 1,
                        line.trim()
                    ));
                }
            }
        }
    }
    found.sort();
    assert!(
        found.is_empty(),
        "build test workspaces with `common::workspace` (or \
         `workspace_with_build_properties`), which refuses an environment that \
         reaches a real SDK without the server's property environment:\n{}",
        found.join("\n")
    );
}
