//! A driver for `tools/msbuild-condition-oracle`'s `fscArgs` op, for crates
//! other than `borzoi-msbuild` (whose own tests drive every op through
//! `tests/common`): build the tool once (marker-gated, with the marker and
//! fingerprint `borzoi-msbuild`'s tests use, so the two never rebuild over
//! each other), drive it as a long-lived JSONL child, and parse the answer
//! into an [`FscInvocation`] at the boundary.
//!
//! `fscArgs` restores the project, runs a real `Build`'s targets through
//! `Compile` with the compiler's run skipped, and reports what the `Fsc` task
//! hands fsc. See the op's entry in `tools/msbuild-condition-oracle/Program.fs`
//! for what it declines; `borzoi-msbuild`'s `fsc_args_oracle_calibration`
//! holds it to real compiling builds.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::Duration;

use crate::fsc_args::{FscArgsError, FscArguments};
use crate::{BatchChild, BoundedCommand, default_timeout};

/// Budget for the one `dotnet build` this driver runs: far above a cold
/// build, there to stop a stalled one.
const BUILD_TIMEOUT: Duration = Duration::from_secs(1800);

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ parent")
        .parent()
        .expect("workspace root parent")
        .to_path_buf()
}

/// Build `tools/msbuild-condition-oracle` (unless
/// `BORZOI_MSBUILD_CONDITION_ORACLE` points at a prebuilt binary) and return
/// the apphost path. The marker holds the fingerprint of the sources the
/// apphost was built from, so a stale oracle never answers for other sources.
pub fn apphost() -> &'static Path {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT
        .get_or_init(|| {
            if let Some(bin) = std::env::var_os("BORZOI_MSBUILD_CONDITION_ORACLE") {
                return PathBuf::from(bin);
            }
            let project = workspace_root()
                .join("tools")
                .join("msbuild-condition-oracle");
            let bin = project.join("bin");
            let apphost = bin
                .join("Release")
                .join("net10.0")
                .join("msbuild-condition-oracle");
            let marker = bin.join(".msbuild-condition-oracle-built");
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
                    .run_ok("dotnet build msbuild-condition-oracle");
                assert!(
                    apphost.exists(),
                    "dotnet build msbuild-condition-oracle produced no apphost at {apphost:?}"
                );
                let tmp = bin.join(format!(
                    ".msbuild-condition-oracle-built.tmp-{}",
                    std::process::id()
                ));
                if std::fs::write(&tmp, &want).is_ok() && std::fs::rename(&tmp, &marker).is_err() {
                    let _ = std::fs::remove_file(&tmp);
                }
            }
            apphost
        })
        .as_path()
}

/// The tool's sources and the flake lock (which pins the SDK, and so the
/// MSBuild the oracle loads), hashed.
pub fn source_fingerprint(project: &Path) -> u64 {
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

/// The environment the oracle child runs under: the runtime essentials and
/// the `DOTNET_*`/`NUGET_*` variables, nothing else, since MSBuild reads every
/// variable as a property. An evaluation compared with the oracle's must see
/// the same set.
pub fn scrubbed_environment() -> Vec<(String, String)> {
    std::env::vars()
        .filter(|(key, _)| {
            matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR")
                || key.starts_with("DOTNET_")
                || key.starts_with("NUGET_")
        })
        .collect()
}

/// One compile as the `fscArgs` op reports it.
#[derive(Debug, Clone)]
pub struct FscInvocation {
    /// Each argument the `Fsc` task passed, in order, as it wrote it (the
    /// items' escaped spelling).
    pub args: Vec<String>,
    /// The response file the task hands fsc, as it wrote it: [`Self::args`]
    /// one per line, with `--refout:` and `--refonly` among them, and each
    /// `\` as written (the items behind `args` turn it into `/` off Windows).
    /// What fsc reads, so what [`Self::arguments`] parses.
    pub response_file: String,
    /// The file of the task assembly whose `Fsc` ran.
    pub task_assembly: String,
    /// The task's `ToolPath`, `ToolExe` and `DotnetFscCompilerPath` as it was
    /// handed them: what chooses the program the arguments go to.
    pub compiler: BTreeMap<String, String>,
}

impl FscInvocation {
    /// The response file, parsed as fsc reads it.
    pub fn arguments(&self) -> Result<FscArguments, FscArgsError> {
        FscArguments::parse(&self.response_file)
    }
}

/// The `fscArgs` request for the project on disk at `path` under the global
/// properties `globals`.
pub fn fsc_args_request(path: &Path, globals: &[(String, String)]) -> serde_json::Value {
    let globals: serde_json::Map<String, serde_json::Value> = globals
        .iter()
        .map(|(k, v)| (k.clone(), serde_json::Value::String(v.clone())))
        .collect();
    serde_json::json!({
        "op": "fscArgs",
        "path": path.to_str().expect("UTF-8 project path"),
        "globals": if globals.is_empty() { serde_json::Value::Null } else { globals.into() },
    })
}

/// The `fscArgs` answer: the invocation, or why there is none (its first
/// entry is "MSBuild rejects the project", "the restore failed" or "the build
/// failed" when MSBuild built nothing).
pub fn parse_fsc_args_response(resp: &serde_json::Value) -> Result<FscInvocation, Vec<String>> {
    let strings = |value: &serde_json::Value, what: &str| -> Vec<String> {
        value
            .as_array()
            .unwrap_or_else(|| panic!("fscArgs response carries a `{what}` array: {resp}"))
            .iter()
            .map(|v| v.as_str().expect("each entry is a string").to_string())
            .collect()
    };
    if resp["ok"].as_bool() != Some(true) {
        return Err(strings(&resp["errors"], "errors"));
    }
    Ok(FscInvocation {
        args: strings(&resp["args"], "args"),
        response_file: resp["responseFile"]
            .as_str()
            .expect("fscArgs response carries the response file")
            .to_string(),
        task_assembly: resp["taskAssembly"]
            .as_str()
            .expect("fscArgs response names the task assembly")
            .to_string(),
        compiler: resp["compiler"]
            .as_object()
            .expect("fscArgs response carries a `compiler` object")
            .iter()
            .map(|(k, v)| (k.clone(), v.as_str().unwrap_or_default().to_string()))
            .collect(),
    })
}

/// A resident `msbuild-condition-oracle` child for `fscArgs` requests.
pub struct Oracle {
    child: BatchChild,
}

impl Oracle {
    /// An oracle running the MSBuild `dotnet` resolves from `working_dir`,
    /// in [`scrubbed_environment`] plus `env`.
    pub fn spawn_in_dir_with_env(working_dir: &Path, env: &[(String, String)]) -> Oracle {
        let bin = apphost().to_path_buf();
        let working_dir = working_dir.to_path_buf();
        let env = env.to_vec();
        let factory = move || {
            let mut cmd = Command::new(&bin);
            cmd.current_dir(&working_dir).env_clear();
            cmd.envs(scrubbed_environment());
            cmd.envs(env.iter().map(|(name, value)| (name, value)));
            cmd
        };
        Oracle {
            child: BatchChild::with_factory(
                Box::new(factory),
                "msbuild-condition-oracle",
                default_timeout(),
                2,
            ),
        }
    }

    /// What the `Fsc` task hands fsc for the project on disk at `path` under
    /// `globals` ([`parse_fsc_args_response`]).
    pub fn fsc_args(
        &mut self,
        path: &Path,
        globals: &[(String, String)],
    ) -> Result<FscInvocation, Vec<String>> {
        let line = serde_json::to_string(&fsc_args_request(path, globals)).expect("serialise");
        let response = self.child.request(&line);
        let value: serde_json::Value =
            serde_json::from_str(&response).expect("oracle response is JSON");
        if let Some(err) = value.get("error") {
            panic!("oracle errored on {line}: {err}");
        }
        parse_fsc_args_response(&value)
    }
}
