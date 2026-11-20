//! The typed reading of fsc's arguments
//! ([`borzoi_oracle_harness::fsc_args::FscArguments`]) held to fsc itself on
//! the lines whose reading turns on fsc's option table: a `/`-led line that is
//! no switch (another `/` in it), `/X:/path`, which fsc takes as an option
//! only when one of its options named `X` accepts that argument, and as a
//! positional argument otherwise.
//!
//! For every letter and every installed SDK's `fsc.dll`, a response file holds
//! the one line, naming a file that does not exist. A line the reading takes
//! for a source must draw fsc's "source file could not be found" (FS0225)
//! naming it; a line it takes for an option must not.

mod common;

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use borzoi_msbuild::observed::host_fs;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::fsc_args::FscArguments;

/// Every `fsc.dll` of an SDK installed under the devshell's dotnet root.
fn compilers() -> Vec<std::path::PathBuf> {
    let sdks = common::dotnet_root_from_env().join("sdk");
    let mut found: Vec<_> = host_fs::read_dir(&sdks)
        .unwrap_or_else(|e| panic!("listing {}: {e}", sdks.display()))
        .flatten()
        .map(|entry| entry.path().join("FSharp").join("fsc.dll"))
        .filter(|fsc| fsc.host_is_file())
        .collect();
    found.sort();
    assert!(!found.is_empty(), "no fsc.dll under {}", sdks.display());
    found
}

/// What fsc reports for the response file `rsp`, stdout and stderr together.
fn run_fsc(fsc: &Path, rsp: &Path) -> String {
    let mut cmd = Command::new("dotnet");
    cmd.arg(fsc).arg(format!("@{}", rsp.display()));
    let out = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(120))
        .run()
        .unwrap_or_else(|e| panic!("{}: {e}", fsc.display()));
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

use borzoi_msbuild::observed::host_fs::HostPath;

#[test]
fn slash_led_lines_read_as_fsc_reads_them() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = host_fs::canonicalize(tmp.path()).unwrap();
    let mut failures = Vec::new();
    for fsc in compilers() {
        for letter in ('a'..='z').chain('A'..='Z') {
            let missing = format!("/nonexistent/borzoi/F{letter}.fs");
            let line = format!("/{letter}:{missing}");
            let rsp_text = format!("--target:library\n-o:{}/Out.dll\n{line}\n", dir.display());
            let rsp = dir.join(format!("{letter}.rsp"));
            std::fs::write(&rsp, &rsp_text).unwrap();
            let ours = FscArguments::parse(&rsp_text)
                .map(|args| args.sources.contains(&line))
                .unwrap_or_else(|e| panic!("{line}: {e:?}"));
            let report = run_fsc(&fsc, &rsp);
            let theirs = report
                .lines()
                .any(|l| l.contains("FS0225") && l.contains(&line));
            if ours != theirs {
                failures.push(format!(
                    "{}: {line}: we read {}, fsc {}:\n{report}",
                    fsc.display(),
                    if ours { "a source" } else { "an option" },
                    if theirs {
                        "looked for it as a source"
                    } else {
                        "did not"
                    }
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
