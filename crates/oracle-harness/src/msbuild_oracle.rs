//! What the F# compiler is handed for a project, read off a **real build**:
//! [`fsc_args`] runs `dotnet msbuild -restore -t:Build` on it with
//! `tools/msbuild-condition-oracle`'s `FscArgsLogger` attached, and parses
//! each `Fsc` invocation's response file into an [`FscArguments`] at the
//! boundary.
//!
//! It runs the build rather than imitating one: the restore, the targets,
//! the project references and the compiler are the CLI's own, so what it
//! reports is what fsc is handed, and "MSBuild built nothing" means the build
//! never started `Fsc`. The one setting it adds is `NonExistentFile` (which
//! design-time builds also set), naming a file that does not exist among
//! `CoreCompile`'s outputs, so an already-built project compiles again rather
//! than skipping the target.
//!
//! The tool is built once (marker-gated, with the marker and fingerprint
//! `borzoi-msbuild`'s tests use, so the two never rebuild over each other).
//! `borzoi-msbuild`'s `fsc_args_oracle_calibration` holds the reading to the
//! files fsc writes and to the arguments MSBuild reports.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::Duration;

use crate::BoundedCommand;
use crate::fsc_args::{FscArgsError, FscArguments};

/// Budget for the one `dotnet build` of the tool: far above a cold build,
/// there to stop a stalled one.
const BUILD_TIMEOUT: Duration = Duration::from_secs(1800);

/// Budget for one real build of a project: a restore and a compile, with its
/// references.
const FSC_ARGS_TIMEOUT: Duration = Duration::from_secs(900);

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

/// The environment [`fsc_args`]'s build runs under: the runtime essentials,
/// the `DOTNET_*`/`NUGET_*` variables, `RestoreSources` (the devshell's
/// offline feed, so the restore is hermetic), and `MSBUILDLOGTASKINPUTS`, so
/// the task's parameters are logged; nothing else, since MSBuild reads every
/// variable as a property. An evaluation compared with the build must see the
/// same set.
pub fn build_environment() -> Vec<(String, String)> {
    let mut env: Vec<(String, String)> = std::env::vars()
        .filter(|(key, _)| {
            matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR" | "RestoreSources")
                || key.starts_with("DOTNET_")
                || key.starts_with("NUGET_")
        })
        .collect();
    env.push(("MSBUILDLOGTASKINPUTS".into(), "1".into()));
    env
}

/// One `Fsc` invocation of the build.
#[derive(Debug, Clone)]
pub struct FscInvocation {
    /// The project file it ran for.
    pub project: PathBuf,
    /// The global properties that project instance was built under (a
    /// multi-targeted project's inner builds differ by `TargetFramework`).
    pub globals: BTreeMap<String, String>,
    /// The response file the task handed fsc, as it wrote it: its arguments
    /// one per line, `--refout:` among them, each `\` and `%` as written.
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

/// A real build of a project, as far as fsc is concerned.
#[derive(Debug, Clone)]
pub struct FscBuild {
    /// Whether the whole build succeeded (it may fail after fsc ran: a
    /// compile error, or a later target).
    pub succeeded: bool,
    /// Every `Fsc` invocation for the project itself, in the order they
    /// started: one per inner build (a single-targeted project has one).
    pub invocations: Vec<FscInvocation>,
}

/// Why [`fsc_args`] gives no [`FscBuild`], with MSBuild's messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FscArgsDecline {
    /// The build failed before starting `Fsc` for the project, so fsc is
    /// handed nothing.
    NoBuild(Vec<String>),
    /// fsc may be handed arguments that cannot be reported: the build
    /// succeeded without starting `Fsc` for the project (a replaced
    /// `CoreCompile`, say), or an invocation's command line could not be read.
    Unanswered(Vec<String>),
}

/// What fsc is handed for the project at `project` (on disk) in a real
/// `dotnet msbuild -restore -t:Build` under the global properties `globals`,
/// in [`build_environment`] plus `env`. A global's value may not hold `;` or
/// `"`, which the command line would split or strip.
pub fn fsc_args(
    project: &Path,
    globals: &[(String, String)],
    env: &[(String, String)],
) -> Result<FscBuild, FscArgsDecline> {
    let project = std::fs::canonicalize(project)
        .unwrap_or_else(|e| panic!("canonicalise {}: {e}", project.display()));
    let dir = project.parent().expect("a project file has a directory");
    let scratch = std::env::temp_dir().join(format!(
        "borzoi-fsc-args-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or_default()
    ));
    std::fs::create_dir_all(&scratch).expect("create the scratch directory");
    let out = scratch.join("fsc-args.json");
    let logger = apphost().with_extension("dll");

    let mut cmd = Command::new("dotnet");
    cmd.current_dir(dir)
        .args([
            "msbuild",
            "-nologo",
            "-nodeReuse:false",
            "-restore",
            "-t:Build",
        ])
        .arg(format!(
            "-p:NonExistentFile={}",
            scratch.join("__NonExistentFile__").display()
        ))
        .arg(format!(
            "-logger:MsBuildConditionOracle.Program+FscArgsLogger,{};{}",
            logger.display(),
            out.display()
        ));
    for (name, value) in globals {
        assert!(
            !value.contains([';', '"']),
            "global {name}={value:?} cannot be passed on the command line verbatim"
        );
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(&project).env_clear();
    cmd.envs(build_environment());
    cmd.envs(env.iter().map(|(name, value)| (name, value)));
    let output = BoundedCommand::new(cmd)
        .timeout(FSC_ARGS_TIMEOUT)
        .run()
        .unwrap_or_else(|e| panic!("dotnet msbuild of {}: {e}", project.display()));
    let json = std::fs::read_to_string(&out).unwrap_or_else(|e| {
        panic!(
            "dotnet msbuild of {} wrote no fsc arguments ({e}):\n{}\n{}",
            project.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    let _ = std::fs::remove_dir_all(&scratch);
    parse_logger_output(&project, &json)
}

/// [`fsc_args`]'s reading of what `FscArgsLogger` wrote for `project`.
fn parse_logger_output(project: &Path, json: &str) -> Result<FscBuild, FscArgsDecline> {
    let value: serde_json::Value = serde_json::from_str(json).expect("FscArgsLogger writes JSON");
    let strings = |v: &serde_json::Value| -> BTreeMap<String, String> {
        v.as_object()
            .map(|o| {
                o.iter()
                    .map(|(k, v)| (k.clone(), v.as_str().unwrap_or_default().to_string()))
                    .collect()
            })
            .unwrap_or_default()
    };
    let errors: Vec<String> = value["errors"]
        .as_array()
        .expect("FscArgsLogger writes its errors")
        .iter()
        .map(|e| e.as_str().unwrap_or_default().to_string())
        .collect();
    let succeeded = value["succeeded"].as_bool() == Some(true);
    let canonical = |p: &str| std::fs::canonicalize(p).unwrap_or_else(|_| PathBuf::from(p));
    let mut invocations = Vec::new();
    for run in value["invocations"]
        .as_array()
        .expect("FscArgsLogger writes its invocations")
    {
        let run_project = canonical(run["project"].as_str().unwrap_or_default());
        if run_project != project {
            continue;
        }
        let Some(response_file) = run["responseFile"].as_str() else {
            return Err(FscArgsDecline::Unanswered(vec![format!(
                "an Fsc invocation's command line could not be read: {}",
                run["problem"]
            )]));
        };
        invocations.push(FscInvocation {
            project: run_project,
            globals: strings(&run["globals"]),
            response_file: response_file.to_string(),
            task_assembly: run["taskAssembly"].as_str().unwrap_or_default().to_string(),
            compiler: strings(&run["compiler"]),
        });
    }
    match (invocations.is_empty(), succeeded) {
        (false, _) => Ok(FscBuild {
            succeeded,
            invocations,
        }),
        (true, false) => Err(FscArgsDecline::NoBuild(errors)),
        (true, true) => Err(FscArgsDecline::Unanswered(vec![
            "the build succeeded without starting Fsc for the project".to_string(),
        ])),
    }
}
