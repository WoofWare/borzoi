//! The driver for `tools/workload-oracle`: build it once (marker-gated), then
//! drive it as a long-lived JSONL request/response child on one SDK's workload
//! resolver.
//!
//! The process plumbing is [`BatchChild`]; this module knows the JSON
//! protocol, how to build the tool, and which runtime each SDK's resolver
//! needs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::Duration;

use crate::{BatchChild, BoundedCommand};

/// Budget for the one `dotnet build` this driver runs (see the NuGet oracle's
/// `BUILD_TIMEOUT` for why it sits far above a request's).
const BUILD_TIMEOUT: Duration = Duration::from_secs(1800);

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ parent")
        .parent()
        .expect("workspace root parent")
        .to_path_buf()
}

/// Build `tools/workload-oracle` (unless `BORZOI_WORKLOAD_ORACLE` points at a
/// prebuilt binary) and return the apphost path. The marker file's contents are
/// the source fingerprint of the apphost on disk, as for the NuGet oracle.
fn ensure_oracle_built() -> &'static Path {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT
        .get_or_init(|| {
            if let Some(bin) = std::env::var_os("BORZOI_WORKLOAD_ORACLE") {
                return PathBuf::from(bin);
            }
            let project = workspace_root().join("tools").join("workload-oracle");
            let bin = project.join("bin");
            let apphost = bin.join("Release").join("net10.0").join("workload-oracle");
            let marker = bin.join(".workload-oracle-built");
            let want = format!("{:016x}", source_fingerprint(&project));
            let fresh = apphost.exists()
                && std::fs::read_to_string(&marker)
                    .map(|recorded| recorded.trim() == want)
                    .unwrap_or(false);
            if !fresh {
                let mut cmd = Command::new("dotnet");
                cmd.args(["build", "-c", "Release", "--nologo"])
                    .arg(&project);
                BoundedCommand::new(cmd)
                    .timeout(BUILD_TIMEOUT)
                    .run_ok("dotnet build workload-oracle");
                assert!(
                    apphost.exists(),
                    "dotnet build workload-oracle produced no apphost at {apphost:?}"
                );
                let tmp = bin.join(format!(".workload-oracle-built.tmp-{}", std::process::id()));
                if std::fs::write(&tmp, &want).is_ok() && std::fs::rename(&tmp, &marker).is_err() {
                    let _ = std::fs::remove_file(&tmp);
                }
            }
            apphost
        })
        .as_path()
}

/// Hash the tool's sources and the flake lock (which pins the SDKs).
fn source_fingerprint(project: &Path) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut sources: Vec<PathBuf> = std::fs::read_dir(project)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            matches!(
                p.extension().and_then(|s| s.to_str()),
                Some("fs" | "fsproj")
            )
        })
        .collect();
    sources.sort();
    sources.push(workspace_root().join("flake.lock"));
    let mut h = DefaultHasher::new();
    for p in &sources {
        p.file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .hash(&mut h);
        std::fs::read(p).unwrap_or_default().hash(&mut h);
    }
    h.finish()
}

/// The workload environment variables the resolver reads. The oracle child
/// runs with none of them set, as the differentials grade the resolver
/// without overrides.
const WORKLOAD_VARIABLES: &[&str] = &[
    "DOTNETSDK_WORKLOAD_MANIFEST_ROOTS",
    "DOTNETSDK_WORKLOAD_MANIFEST_IGNORE_DEFAULT_ROOTS",
    "DOTNETSDK_WORKLOAD_PACK_ROOTS",
    "MSBuildEnableWorkloadResolver",
];

/// A long-lived `workload-oracle` child on one SDK's resolver, driven in
/// lock-step. The protocol is stateless (every request builds a fresh
/// resolver), so a respawned child answers identically.
pub struct Oracle {
    child: BatchChild,
}

impl Oracle {
    /// Spawn the oracle on the resolver of the SDK in `sdk` (a
    /// `<dotnet-root>/sdk/<version>` directory), on the runtime of
    /// `<dotnet-root>`. A resolver built for a newer runtime than the tool's
    /// own (net10.0) is run on the newest runtime there.
    pub fn spawn_on(sdk: &Path) -> Oracle {
        let dotnet_root = sdk
            .parent()
            .and_then(Path::parent)
            .expect("an SDK directory sits at <dotnet-root>/sdk/<version>");
        let major: u32 = sdk
            .file_name()
            .and_then(|n| n.to_str())
            .and_then(|n| n.split('.').next())
            .and_then(|m| m.parse().ok())
            .expect("an SDK directory is named by its version");
        let mut process: Vec<(String, Option<String>)> = vec![(
            "DOTNET_ROOT".to_owned(),
            Some(dotnet_root.to_string_lossy().into_owned()),
        )];
        if major > 10 {
            process.push((
                "DOTNET_ROLL_FORWARD".to_owned(),
                Some("LatestMajor".to_owned()),
            ));
            process.push((
                "DOTNET_ROLL_FORWARD_TO_PRERELEASE".to_owned(),
                Some("1".to_owned()),
            ));
        }
        process.extend(WORKLOAD_VARIABLES.iter().map(|v| ((*v).to_owned(), None)));
        let sdk = sdk.to_str().expect("SDK directory is UTF-8");
        Oracle {
            child: BatchChild::spawn_with_environment(
                ensure_oracle_built(),
                &["--sdk", sdk],
                &process,
            ),
        }
    }

    /// One request/response round-trip. Panics on an `{"error": ..}`
    /// response, which means the harness or the tool is broken, never a
    /// resolver verdict.
    pub fn request(&mut self, req: &serde_json::Value) -> serde_json::Value {
        let line = serde_json::to_string(req).expect("serialise request");
        let response = self.child.request(&line);
        let value: serde_json::Value =
            serde_json::from_str(&response).expect("workload-oracle response is JSON");
        if let Some(err) = value.get("error") {
            panic!("workload-oracle errored on {line}: {err}");
        }
        value
    }
}
