//! Which `global.json` `sdk.paths` root hostfxr runs an SDK from, held to
//! hostfxr's own choice (#912).
//!
//! hostfxr tries the roots in order and runs from the first whose `sdk`
//! directory holds a version the `sdk` block admits (its best there), looking
//! at no later root (`sdk_resolver::resolve_sdk_path_and_version`). MSBuild's
//! default resolver then serves a name from that SDK or fails; it does not
//! consult another root. So the LSP's resolution across roots must stop at
//! that root, which [`running_sdk_dir`] decides root by root: hostfxr's pick
//! is the first root where it is `Ok`.
//!
//! The sweep writes two roots of fake SDKs (a version directory holding an
//! empty `dotnet.dll`, all hostfxr looks for) from a table of version sets,
//! in both orders, beside the devshell's own install as `$host$`, under each
//! `rollForward` policy and with no version at all, runs `dotnet --version`
//! with `COREHOST_TRACE`, and reads hostfxr's pick from the trace ("SDK path
//! resolved to [...]"). A fake SDK cannot run, so only the trace counts.
//!
//! Unix only, like the other host harnesses.
#![cfg(unix)]

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::{SdkPathEntry, parse_global_json, running_sdk_dir};
use borzoi_oracle_harness::BoundedCommand;

/// The SDK directory hostfxr resolved, from its trace, running `dotnet
/// --version` in `project`.
fn hostfxr_pick(dotnet: &Path, project: &Path, trace: &Path) -> Option<PathBuf> {
    let mut cmd = Command::new(dotnet);
    cmd.current_dir(project)
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("HOME", std::env::var_os("HOME").unwrap_or_default())
        .env("DOTNET_CLI_TELEMETRY_OPTOUT", "1")
        .env("DOTNET_NOLOGO", "1")
        .env("COREHOST_TRACE", "1")
        .env("COREHOST_TRACEFILE", trace)
        .arg("--version");
    let _ = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(120))
        .run();
    let text = host_fs::read_to_string(trace).expect("hostfxr writes its trace");
    std::fs::remove_file(trace).unwrap();
    text.lines().find_map(|line| {
        line.strip_prefix("SDK path resolved to [")
            .and_then(|rest| rest.strip_suffix(']'))
            .map(PathBuf::from)
    })
}

/// A root of fake SDKs at `root`: `None` writes no `sdk` directory at all.
fn write_root(root: &Path, versions: Option<&[&str]>) {
    std::fs::create_dir_all(root).unwrap();
    let Some(versions) = versions else {
        return;
    };
    std::fs::create_dir_all(root.join("sdk")).unwrap();
    for version in versions {
        let dir = root.join("sdk").join(version);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("dotnet.dll"), "").unwrap();
    }
}

/// `pick`, a resolved SDK directory, as `{root label}:{version}`.
fn label(pick: &Path, roots: &[(&str, PathBuf)], host: &Path) -> String {
    let version = pick
        .file_name()
        .map(|v| v.to_string_lossy().into_owned())
        .unwrap_or_default();
    let canon = |p: &Path| host_fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let parent = canon(pick.parent().and_then(Path::parent).unwrap_or(pick));
    for (name, root) in roots {
        if parent == canon(root) {
            return format!("{name}:{version}");
        }
    }
    if parent == canon(host) {
        return format!("host:{version}");
    }
    format!("elsewhere {}", pick.display())
}

#[test]
fn hostfxr_runs_from_the_first_root_holding_an_admitted_sdk() {
    let real = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    );
    let dotnet = real.join("dotnet");
    let host = host_fs::canonicalize(&real).unwrap();
    // The version sets a fake root holds: none, an empty `sdk`, one version
    // below, at, a patch above, a feature band above, a minor and a major
    // above the pin, and two in one root.
    let sets: &[Option<&[&str]>] = &[
        None,
        Some(&[]),
        Some(&["9.0.100"]),
        Some(&["10.0.100"]),
        Some(&["10.0.105"]),
        Some(&["10.0.200"]),
        Some(&["10.1.100"]),
        Some(&["11.0.100"]),
        Some(&["10.0.103", "10.0.300"]),
    ];
    let policies = [
        None,
        Some("latestPatch"),
        Some("patch"),
        Some("feature"),
        Some("latestFeature"),
        Some("minor"),
        Some("latestMinor"),
        Some("major"),
        Some("latestMajor"),
        Some("disable"),
    ];
    let scratch = tempfile::TempDir::new().unwrap();
    let base = host_fs::canonicalize(scratch.path()).unwrap();
    let trace = base.join("trace.txt");
    let mut failures = Vec::new();
    let (mut cases, mut picked, mut picked_second, mut picked_none, mut picked_host) =
        (0usize, 0, 0, 0, 0);
    let mut case_index = 0usize;
    let mut run = |paths: &[&str],
                   version: Option<&str>,
                   policy: Option<&str>,
                   a: Option<&[&str]>,
                   b: Option<&[&str]>| {
        case_index += 1;
        let case = base.join(format!("case{case_index}"));
        let project = case.join("project");
        std::fs::create_dir_all(&project).unwrap();
        let roots = vec![("a", case.join("a")), ("b", case.join("b"))];
        write_root(&roots[0].1, a);
        write_root(&roots[1].1, b);
        let entries: Vec<String> = paths
            .iter()
            .map(|p| match *p {
                "a" | "b" => format!("{:?}", case.join(p).display().to_string()),
                "./a" => "\"../a\"".to_owned(),
                other => format!("{other:?}"),
            })
            .collect();
        let mut sdk = vec![format!("\"paths\": [{}]", entries.join(", "))];
        if let Some(version) = version {
            sdk.push(format!("\"version\": \"{version}\""));
        }
        if let Some(policy) = policy {
            sdk.push(format!("\"rollForward\": \"{policy}\""));
        }
        let text = format!("{{ \"sdk\": {{ {} }} }}", sdk.join(", "));
        std::fs::write(project.join("global.json"), &text).unwrap();

        // Ours: the first root where `running_sdk_dir` is `Ok`.
        let settings = parse_global_json(&text)
            .expect("the sweep writes valid global.json")
            .sdk
            .expect("with an sdk block");
        let ordered: Vec<PathBuf> = settings
            .paths
            .clone()
            .unwrap_or_default()
            .into_iter()
            .map(|entry| match entry {
                SdkPathEntry::Host => host.clone(),
                SdkPathEntry::Relative(path) => project.join(path),
            })
            .collect();
        let spec = settings.into_spec(true);
        let observer = Observer::new();
        let ours = ordered
            .iter()
            .find_map(|root| running_sdk_dir(root, Some(&spec), &observer).ok())
            .map(|dir| label(&dir, &roots, &host));
        let theirs = hostfxr_pick(&dotnet, &project, &trace).map(|dir| label(&dir, &roots, &host));
        cases += 1;
        match theirs.as_deref() {
            None => picked_none += 1,
            Some(t) if t.starts_with("host:") => picked_host += 1,
            Some(t) if t.starts_with("b:") && paths.first() == Some(&"a") => picked_second += 1,
            Some(_) => picked += 1,
        }
        if ours != theirs {
            failures.push(format!(
                "{text} with a={a:?}, b={b:?}: ours {ours:?}, hostfxr {theirs:?}"
            ));
        }
        let _ = std::fs::remove_dir_all(&case);
    };
    // Two fake roots, each version set against each, in order, under each
    // policy against a `10.0.100` pin, and with no version.
    for a in sets {
        for b in sets {
            for policy in policies {
                run(&["a", "b"], Some("10.0.100"), policy, *a, *b);
            }
            run(&["a", "b"], None, None, *a, *b);
        }
    }
    // The host install among them, in either place, and a relative path.
    for a in sets {
        run(
            &["a", "$host$"],
            Some("10.0.100"),
            Some("latestMajor"),
            *a,
            None,
        );
        run(
            &["$host$", "a"],
            Some("10.0.100"),
            Some("latestMajor"),
            *a,
            None,
        );
        run(&["a", "$host$"], None, None, *a, None);
        run(
            &["./a", "b"],
            Some("10.0.100"),
            Some("latestFeature"),
            *a,
            Some(&["10.0.200"]),
        );
    }
    println!(
        "sdk.paths root choice: {cases} cases; hostfxr ran from the first root {picked}, the \
         second {picked_second}, the host {picked_host}, none {picked_none}"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Anti-vacuity: each kind of pick occurs.
    assert!(
        picked > 50 && picked_second > 50 && picked_host > 4 && picked_none > 50,
        "picks: first {picked}, second {picked_second}, host {picked_host}, none {picked_none}"
    );
}
