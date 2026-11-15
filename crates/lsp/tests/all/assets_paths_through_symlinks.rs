//! The project paths an assets file records are relative to the project's
//! directory as MSBuild spells it (#829). A symlink on the way to the assets
//! file must not move where they resolve.
//!
//! The layout: the entry `P` is reached through a symlinked directory
//! (`ws/P` → `vault/P`) and references `Q` (`ws/Q/Q.fsproj`, naming its
//! output `Q`) and `R` (`ws/R/R.fsproj`, a symlink to `vault/Q/Q.fsproj`,
//! naming no output, so its output name is the one the assets file records).
//! `R`'s `bin` holds its output `R.dll` and a stale `Q.dll` from before a
//! rename. The assets file records `Q` at `../Q/Q.fsproj` and `R` at
//! `../R/R.fsproj`, as NuGet writes them from `ws/P`. Resolved from
//! `vault/P` instead, `Q`'s entry lands on `vault/Q/Q.fsproj`, which is `R`'s
//! file, and `R`'s own entry on a path that does not exist, so `R` takes
//! `Q`'s recorded name.
//!
//! What MSBuild builds against is `R.dll`; the test asserts the env names it
//! and not the stale `Q.dll`, with the plain layout (`ws/P` a real directory)
//! as the control.

use std::path::{Path, PathBuf};

use borzoi::sdk_discovery::SdkDiscoveryEnv;
use borzoi::semantic::SemanticState;
use borzoi::workspace::Workspace;
use tempfile::TempDir;

use crate::common::host_fs;

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// Lay the layout down under `root`, the entry's directory a symlink when
/// `linked`; the entry project's path.
fn lay_down(root: &Path, linked: bool) -> PathBuf {
    let ws = root.join("ws");
    let vault = root.join("vault");
    let nuget = root.join("nuget");
    std::fs::create_dir_all(&nuget).unwrap();
    write(
        &ws.join("Q/Q.fsproj"),
        "<Project><PropertyGroup><TargetFramework>net8.0</TargetFramework><TargetName>Q</TargetName></PropertyGroup></Project>\n",
    );
    write(&ws.join("Q/bin/Debug/net8.0/Q.dll"), "dll");
    write(
        &vault.join("Q/Q.fsproj"),
        "<Project><PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup></Project>\n",
    );
    std::fs::create_dir_all(ws.join("R")).unwrap();
    std::os::unix::fs::symlink(vault.join("Q/Q.fsproj"), ws.join("R/R.fsproj")).unwrap();
    // Beside the link and beside its target (the env looks for a project's
    // output beside its canonical path): the output, and a stale `Q.dll`.
    for bin in [ws.join("R/bin"), vault.join("Q/bin")] {
        write(&bin.join("Debug/net8.0/R.dll"), "dll");
        write(&bin.join("Debug/net8.0/Q.dll"), "stale dll");
    }
    let p = if linked { vault.join("P") } else { ws.join("P") };
    write(
        &p.join("P.fsproj"),
        "<Project><PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup><ItemGroup><ProjectReference Include=\"../Q/Q.fsproj\" /><ProjectReference Include=\"../R/R.fsproj\" /></ItemGroup></Project>\n",
    );
    let project = |name: &str| {
        serde_json::json!({
            "type": "project",
            "framework": ".NETCoreApp,Version=v8.0",
            "compile": { format!("bin/placeholder/{name}.dll"): {} },
        })
    };
    let library = |name: &str| {
        serde_json::json!({
            "type": "project",
            "path": format!("../{name}/{name}.fsproj"),
            "msbuildProject": format!("../{name}/{name}.fsproj"),
        })
    };
    let assets = serde_json::json!({
        "version": 3,
        "targets": { "net8.0": { "Q/1.0.0": project("Q"), "R/1.0.0": project("R") } },
        "libraries": { "Q/1.0.0": library("Q"), "R/1.0.0": library("R") },
        "packageFolders": { nuget.to_str().unwrap(): {} },
        "project": { "frameworks": { "net8.0": {} } },
    });
    write(
        &p.join("obj/project.assets.json"),
        &serde_json::to_string(&assets).unwrap(),
    );
    if linked {
        std::os::unix::fs::symlink(&p, ws.join("P")).unwrap();
    }
    ws.join("P/P.fsproj")
}

/// The reference DLLs the env resolves for the layout, relative to its root.
fn reference_dlls(linked: bool) -> Vec<PathBuf> {
    let tmp = TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    let entry = lay_down(&root, linked);
    let dotnet = root.join("dotnet");
    std::fs::create_dir_all(&dotnet).unwrap();
    let mut ws = Workspace::with_env(SdkDiscoveryEnv {
        dotnet_root: Some(root.join("no-dotnet")),
        ..SdkDiscoveryEnv::default()
    });
    let tfm = ws.served_tfm_for_project(&entry);
    let mut semantic = SemanticState::new();
    let (dlls, _) = semantic.reference_resolution_for_project(&entry, Some(&dotnet), &tfm, &ws);
    dlls.iter()
        .map(|dll| dll.strip_prefix(&root).unwrap_or(dll).to_path_buf())
        .collect()
}

#[test]
fn a_symlinked_entry_directory_resolves_the_assets_project_paths_as_msbuild_spells_them() {
    let names = |dlls: &[PathBuf], dir: &str, file: &str| {
        dlls.iter()
            .any(|dll| dll.starts_with(dir) && dll.ends_with(file))
    };
    let plain = reference_dlls(false);
    assert!(
        names(&plain, "vault/Q", "R.dll") && !names(&plain, "vault/Q", "Q.dll"),
        "control: the plain layout names R's output: {plain:?}"
    );
    let linked = reference_dlls(true);
    assert!(
        !names(&linked, "vault/Q", "Q.dll"),
        "the symlinked layout names the stale Q.dll in R's bin as R's output: {linked:?}"
    );
    assert_eq!(linked, plain);
}
