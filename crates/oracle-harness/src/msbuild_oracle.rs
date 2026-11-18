//! What the F# compiler is handed for a project, read off a **real build**:
//! [`fsc_args`] runs `dotnet msbuild -restore -t:Build` on it with
//! `tools/msbuild-condition-oracle`'s `FscArgsLogger` attached, and parses
//! each `Fsc` invocation's response file into an [`FscArguments`] at the
//! boundary.
//!
//! It runs the build rather than imitating one, and adds nothing to it the
//! build can read, only loggers: the restore, the targets, the project
//! references, the global properties and the compiler are the CLI's own. The
//! arguments are MSBuild's account of what the `Fsc` task handed fsc; that
//! fsc ran on them is fsc's own account (its diagnostics, or the output it
//! wrote), so an invocation that logged a command line and ran no compiler is
//! not reported. A project already built is up to date, so its build runs no
//! compiler, and the driver says it cannot answer rather than forcing one;
//! the fixtures it serves are built fresh.
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
/// offline feed, so the restore is hermetic); nothing else, since MSBuild
/// reads every variable as a property. An evaluation compared with the build
/// must see the same set.
pub fn build_environment() -> Vec<(String, String)> {
    std::env::vars()
        .filter(|(key, _)| {
            matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR" | "RestoreSources")
                || key.starts_with("DOTNET_")
                || key.starts_with("NUGET_")
        })
        .collect()
}

/// `path` with its `.` and `..` components folded away lexically, as MSBuild
/// names a project it is handed, without resolving links.
fn lexically_normal(path: &Path) -> PathBuf {
    use std::path::Component;
    let mut normal = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normal.pop();
            }
            other => normal.push(other),
        }
    }
    normal
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
    /// Every `Fsc` invocation for the project itself that ran fsc, in the
    /// order they started: one per inner build (a single-targeted project
    /// has one). That fsc ran is fsc's own evidence: it reported diagnostics,
    /// or the output its arguments name was written during the build. An
    /// invocation that logged its command line but ran no compiler (one told
    /// to skip it, or one whose compiler could not start) is not here.
    pub invocations: Vec<FscInvocation>,
}

/// Why [`fsc_args`] gives no [`FscBuild`], with MSBuild's messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FscArgsDecline {
    /// The `dotnet` host refused the build before MSBuild ran (no installed
    /// SDK satisfies the project's `global.json`), so fsc is handed nothing.
    NoBuild(Vec<String>),
    /// No fsc run of the project's can be reported: the build ran none that
    /// left evidence (it failed first, the project was up to date, or a
    /// replaced `CoreCompile` compiles some other way), or one ran on
    /// arguments the driver cannot read. With the build's errors.
    Unanswered(Vec<String>),
}

/// What fsc is handed for the project at `project` (on disk) in a real
/// `dotnet msbuild -restore -t:Build` under the global properties `globals`,
/// in [`build_environment`] plus `env`. The project is built by the path
/// given, made absolute and lexically normal but not resolved through links
/// (MSBuild names the project after the path it is handed). A global's value may not hold `;`,
/// `,` or `"`, which the command line would split or strip.
pub fn fsc_args(
    project: &Path,
    globals: &[(String, String)],
    env: &[(String, String)],
) -> Result<FscBuild, FscArgsDecline> {
    let project = lexically_normal(
        &std::path::absolute(project)
            .unwrap_or_else(|e| panic!("absolute path of {}: {e}", project.display())),
    );
    let dir = project.parent().expect("a project file has a directory");
    let scratch = ScratchDir::new();
    let out = scratch.0.join("fsc-args.json");
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
            "-logger:MsBuildConditionOracle.Program+FscArgsLogger,{};{}",
            logger.display(),
            out.display()
        ))
        // A diagnostic file log makes MSBuild log every task's inputs, which
        // is how the logger learns the `Fsc` task's compiler parameters; it
        // sets nothing the build can read (`MSBUILDLOGTASKINPUTS` and `-bl`
        // each set a property). It goes to the call's scratch directory.
        .arg(format!(
            "-flp:v=diag;logfile={}",
            scratch.0.join("build.log").display()
        ));
    for (name, value) in globals {
        assert!(
            !value.contains([';', ',', '"']),
            "global {name}={value:?} cannot be passed on the command line verbatim"
        );
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(&project).env_clear();
    cmd.envs(build_environment());
    cmd.envs(env.iter().map(|(name, value)| (name, value)));
    let started = std::time::SystemTime::now();
    let output = BoundedCommand::new(cmd)
        .timeout(FSC_ARGS_TIMEOUT)
        .run()
        .unwrap_or_else(|e| panic!("dotnet msbuild of {}: {e}", project.display()));
    let json = std::fs::read_to_string(&out);
    let report = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    match json {
        Ok(json) => parse_logger_output(&project, &json, started),
        // MSBuild's own command-line errors (`MSB1xxx`: a switch it rejects,
        // a logger it cannot load) are this driver's fault, and loud.
        Err(e) if report.contains("error MSB1") || output.status.success() => panic!(
            "dotnet msbuild of {} wrote no fsc arguments ({e}):\n{report}",
            project.display()
        ),
        // The `dotnet` host refused to select an SDK, before MSBuild ran.
        Err(_) if HOST_SDK_FAILURES.iter().any(|m| report.contains(m)) => {
            Err(FscArgsDecline::NoBuild(vec![report]))
        }
        // Anything else that left no report (the build killed, say) may have
        // run fsc: the answer is unknown.
        Err(e) => Err(FscArgsDecline::Unanswered(vec![format!(
            "the build left no report ({e}):\n{report}"
        )])),
    }
}

/// What the `dotnet` host prints when no installed SDK satisfies the
/// project's `global.json`, which it does before MSBuild starts.
const HOST_SDK_FAILURES: &[&str] = &[
    "A compatible .NET SDK was not found",
    "A compatible installed .NET SDK for global.json version",
];

/// A directory of [`fsc_args`]'s own for one call, which no other call in
/// any process shares: named for this process and a process-wide counter,
/// and made with `create_dir`, which fails rather than adopt one that already
/// exists (left by an earlier process of the same id, say), in which case the
/// next name is tried. Concurrent calls each write their logger's output into
/// their own directory and remove only it.
fn scratch_dir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let temp = std::env::temp_dir();
    loop {
        let dir = temp.join(format!(
            "borzoi-fsc-args-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&dir) {
            Ok(()) => return dir,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => panic!("create {}: {e}", dir.display()),
        }
    }
}

/// A [`scratch_dir`], removed when dropped, on every path out of
/// [`fsc_args`], a panic among them.
struct ScratchDir(PathBuf);

impl ScratchDir {
    fn new() -> ScratchDir {
        ScratchDir(scratch_dir())
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// [`fsc_args`]'s reading of what `FscArgsLogger` wrote for `project`.
fn parse_logger_output(
    project: &Path,
    json: &str,
    started: std::time::SystemTime,
) -> Result<FscBuild, FscArgsDecline> {
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
    let mut invocations = Vec::new();
    for run in value["invocations"]
        .as_array()
        .expect("FscArgsLogger writes its invocations")
    {
        let run_project = lexically_normal(Path::new(run["project"].as_str().unwrap_or_default()));
        if run_project != project {
            continue;
        }
        // A command line that cannot be read may be one fsc ran on.
        let Some(response_file) = run["responseFile"].as_str() else {
            return Err(FscArgsDecline::Unanswered(vec![format!(
                "an Fsc command line could not be read: {}",
                run["problem"]
            )]));
        };
        let compiler_spoke = run["compilerDiagnostics"]
            .as_array()
            .is_some_and(|diagnostics| !diagnostics.is_empty());
        // fsc writes its output relative to the project's directory.
        let wrote_output = FscArguments::parse(response_file)
            .ok()
            .and_then(|args| args.output)
            .and_then(|output| {
                let path = project.parent()?.join(output);
                std::fs::metadata(path).ok()?.modified().ok()
            })
            .is_some_and(|modified| modified >= started);
        if !compiler_spoke && !wrote_output {
            continue;
        }
        invocations.push(FscInvocation {
            project: run_project,
            globals: strings(&run["globals"]),
            response_file: response_file.to_string(),
            task_assembly: run["taskAssembly"].as_str().unwrap_or_default().to_string(),
            compiler: strings(&run["compiler"]),
        });
    }
    if invocations.is_empty() {
        let mut why = vec![format!(
            "the build {} and left no evidence fsc ran for the project",
            if succeeded { "succeeded" } else { "failed" }
        )];
        why.extend(errors);
        Err(FscArgsDecline::Unanswered(why))
    } else {
        Ok(FscBuild {
            succeeded,
            invocations,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{fsc_args, scratch_dir};
    use std::collections::BTreeSet;

    #[test]
    fn scratch_directories_are_never_shared() {
        let dirs: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..16)
                .map(|_| scope.spawn(|| (0..32).map(|_| scratch_dir()).collect::<Vec<_>>()))
                .collect();
            handles
                .into_iter()
                .flat_map(|h| h.join().expect("no thread panics"))
                .collect()
        });
        let distinct: BTreeSet<_> = dirs.iter().collect();
        assert_eq!(distinct.len(), dirs.len(), "two calls shared a directory");
        for dir in &dirs {
            assert!(dir.is_dir(), "{} was not made", dir.display());
            std::fs::remove_dir(dir).unwrap();
        }
    }

    /// Several real builds at once, as a parallel differential runs them: each
    /// must read its own logger's output, none removed under it.
    #[test]
    fn concurrent_calls_each_answer() {
        let tmp = tempfile::TempDir::new().unwrap();
        let projects: Vec<_> = (0..6)
            .map(|i| {
                let dir = tmp.path().join(format!("p{i}"));
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(dir.join("A.fs"), "module A\nlet x = 1\n").unwrap();
                let project = dir.join(format!("P{i}.fsproj"));
                std::fs::write(
                    &project,
                    "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
                     <TargetFramework>net10.0</TargetFramework></PropertyGroup>\
                     <ItemGroup><Compile Include=\"A.fs\" /></ItemGroup></Project>",
                )
                .unwrap();
                project
            })
            .collect();
        let answers: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = projects
                .iter()
                .map(|project| scope.spawn(move || fsc_args(project, &[], &[])))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("no fsc_args call panics"))
                .collect()
        });
        for (i, answer) in answers.into_iter().enumerate() {
            let build = answer.unwrap_or_else(|e| panic!("P{i}: {e:?}"));
            let name = build.invocations[0].arguments().unwrap().assembly_name();
            assert_eq!(name.as_deref(), Some(format!("P{i}").as_str()));
        }
    }
}
