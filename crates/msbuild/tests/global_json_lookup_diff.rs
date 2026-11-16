//! The `global.json` that governs a project directory, held to hostfxr's
//! choice.
//!
//! hostfxr walks up from the working directory for a `global.json` and picks
//! the SDK by it, natively (`stat`, not CLR `File.Exists`). Its trace
//! (`COREHOST_TRACE`) names the file it found ("Found global.json [path]"),
//! so this asks `dotnet --version` from a project directory with one shape at
//! the project's `global.json` and a regular one (or none) a level up, and
//! holds `find_global_json` to the trace: a file we name must be the one
//! hostfxr found, and finding none must be hostfxr finding none. Where we
//! decline ([`UndecidedGlobalJson`]) we make no claim; the test prints what
//! hostfxr did, which is the measurement the decline rests on.
//!
//! A FIFO is not handed to hostfxr, whose read of it never returns; our side
//! alone is held to a decline there.
//!
//! Unix only: the shapes are links and special files.
#![cfg(unix)]

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::{UndecidedGlobalJson, find_global_json};
use borzoi_oracle_harness::BoundedCommand;
use common::odd_entry::{self, Odd};

/// What hostfxr's trace says it found walking up from `dir`.
fn hostfxr_found(dotnet: &Path, dir: &Path, trace: &Path) -> Option<PathBuf> {
    let mut cmd = Command::new(dotnet);
    cmd.current_dir(dir)
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("HOME", std::env::var_os("HOME").unwrap_or_default())
        .env("DOTNET_CLI_TELEMETRY_OPTOUT", "1")
        .env("DOTNET_NOLOGO", "1")
        .env("COREHOST_TRACE", "1")
        .env("COREHOST_TRACEFILE", trace)
        .arg("--version");
    // The CLI itself may fail on what hostfxr accepted; only the trace counts.
    let _ = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(120))
        .run();
    let text = host_fs::read_to_string(trace).expect("hostfxr writes its trace");
    std::fs::remove_file(trace).unwrap();
    text.lines().find_map(|line| {
        line.strip_prefix("Found global.json [")
            .and_then(|rest| rest.strip_suffix(']'))
            .map(PathBuf::from)
    })
}

/// What a case puts at the project's own `global.json`.
#[derive(Clone, Copy, Debug)]
enum Near {
    Absent,
    Regular,
    Odd(Odd),
}

#[test]
fn find_global_json_names_the_file_hostfxr_finds() {
    let dotnet = PathBuf::from(
        std::env::var_os("DOTNET_ROOT").expect("DOTNET_ROOT is set; run under nix develop"),
    )
    .join("dotnet");
    let scratch = tempfile::TempDir::new().unwrap();
    let base = host_fs::canonicalize(scratch.path()).unwrap();
    let aside = base.join("aside");
    let trace = base.join("trace.txt");
    let mut nears = vec![Near::Absent, Near::Regular];
    nears.extend(Odd::ALL.iter().map(|&odd| Near::Odd(odd)));
    let mut failures = Vec::new();
    let mut committed = 0;
    for (index, near) in nears.iter().enumerate() {
        for outer_present in [true, false] {
            let outer = base.join(format!("case{index}-{outer_present}"));
            let project = outer.join("project");
            std::fs::create_dir_all(&project).unwrap();
            if outer_present {
                std::fs::write(outer.join("global.json"), "{}").unwrap();
            }
            let near_path = project.join("global.json");
            match near {
                Near::Absent => {}
                Near::Regular => std::fs::write(&near_path, "{}").unwrap(),
                Near::Odd(odd) => odd_entry::place(*odd, &near_path, "{}", &aside),
            }
            let case = format!("{near:?} with an outer global.json: {outer_present}");
            let ours = find_global_json(&project, &Observer::new());
            if matches!(near, Near::Odd(Odd::Fifo)) {
                assert!(
                    ours.is_err(),
                    "{case}: hostfxr's read of a FIFO never returns, so we must decline: {ours:?}"
                );
                continue;
            }
            let theirs = hostfxr_found(&dotnet, &project, &trace);
            println!("{case}: ours {ours:?}, hostfxr found {theirs:?}");
            match ours {
                Ok(ours) => {
                    committed += 1;
                    // Above the scratch directory both walks meet the same
                    // ancestors; within it, the files must agree.
                    let theirs_here = theirs.filter(|p| p.starts_with(&base));
                    let ours_here = ours.filter(|p| p.starts_with(&base));
                    if ours_here != theirs_here {
                        failures.push(format!(
                            "{case}: we find {ours_here:?}, hostfxr {theirs_here:?}"
                        ));
                    }
                }
                Err(UndecidedGlobalJson { .. }) => {}
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(
        committed >= 6,
        "the sweep committed only {committed} answers"
    );
}
