//! What the F# compiler is handed for a project, read off a **real build**:
//! [`fsc_args`] runs `dotnet msbuild -nodeReuse:false -restore -t:Build` on
//! the project where it lies, with `tools/msbuild-condition-oracle`'s
//! `FscArgsLogger` attached, and parses each `Fsc` invocation's response file
//! into an [`FscArguments`] at the boundary. The build writes where a build
//! writes, so a caller hands it a tree of its own: a fixture laid out in a
//! directory made for the call.
//!
//! It runs the build rather than imitating one: the restore, the targets, the
//! project references, the global properties and the compiler are the CLI's
//! own. The arguments are MSBuild's account of what the `Fsc` task handed its
//! launcher, so they are answered only when that launcher is the `dotnet`
//! running the build and the compiler is its SDK's own `fsc.dll`; that fsc ran
//! on them is fsc's own account, its banner or a diagnostic in the task's
//! context. Anything less is no answer. A tree already built is up to date, so
//! its build runs no compiler, and the driver says it cannot answer rather
//! than forcing one.
//!
//! **The domain.** The loggers set no property the build can read (a
//! diagnostic file log, not `-bl` or `MSBUILDLOGTASKINPUTS`, makes MSBuild log
//! task inputs), but no observation of a build is invisible to a build that
//! looks for it: a project can read the process's command line
//! (`$([System.Environment]::CommandLine)`), or run a program that does. What
//! is answered are the arguments of a real build **that does not read the
//! process's command line**. The driver does not check that, and no check it
//! could make would close it: a second, uninstrumented build compared against
//! this one sees only what it knows to compare. The callers hold it by
//! construction instead: the trees a differential generates contain no
//! property function and no build code (no target, no task), and the
//! calibration's handwritten fixtures are read for it.
//!
//! The inputs a caller may set are closed: [`BuildInputs`] holds global
//! properties and environment variables by names on a positive list
//! ([`INPUT_NAMES`]), none of which chooses the toolchain, the compiler, the
//! restore or MSBuild's own machinery.
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
                // Absolute here, since the builds run in other directories.
                return std::path::absolute(PathBuf::from(&bin)).unwrap_or_else(|e| {
                    panic!("absolute path of {}: {e}", PathBuf::from(&bin).display())
                });
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

/// The variables of this process [`build_environment`] carries into a build,
/// by exact name: the runtime essentials, the .NET install and NuGet's package
/// folder, `RestoreSources` (the devshell's offline feed, so the restore is
/// hermetic), and the CLI's switches the devshell sets. A closed list, so a
/// machine's other `DOTNET_*` or `NUGET_*` variables (a CI runner's) never
/// reach a build an evaluation is compared with.
pub const BUILD_ENVIRONMENT_NAMES: &[&str] = &[
    "DOTNET_CLI_TELEMETRY_OPTOUT",
    "DOTNET_NOLOGO",
    "DOTNET_NUGET_SIGNATURE_VERIFICATION",
    "DOTNET_ROOT",
    "DOTNET_SKIP_FIRST_TIME_EXPERIENCE",
    "DOTNET_SKIP_WORKLOAD_INTEGRITY_CHECK",
    "HOME",
    "NUGET_PACKAGES",
    "PATH",
    "RestoreSources",
    "TMPDIR",
];

/// The environment [`fsc_args`]'s build runs under: this process's variables
/// of [`BUILD_ENVIRONMENT_NAMES`], nothing else, since MSBuild reads every
/// variable as a property. An evaluation compared with the build must see the
/// same set.
pub fn build_environment() -> Vec<(String, String)> {
    std::env::vars()
        .filter(|(key, _)| BUILD_ENVIRONMENT_NAMES.contains(&key.as_str()))
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
    /// The directory of the MSBuild that ran the build: its SDK's version
    /// directory.
    pub msbuild_directory: PathBuf,
    /// Whether the whole build succeeded (it may fail after fsc ran: a
    /// compile error, or a later target).
    pub succeeded: bool,
    /// Every `Fsc` invocation for the project itself that ran fsc, in the
    /// order they started: one per inner build (a single-targeted project
    /// has one), each launched as the SDK launches its compiler and showing
    /// fsc's own sign of having run (its banner or a diagnostic).
    pub invocations: Vec<FscInvocation>,
}

/// Why [`fsc_args`] gives no [`FscBuild`], with MSBuild's messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FscArgsDecline {
    /// The `dotnet` host refused the build before MSBuild ran (no installed
    /// SDK satisfies the project's `global.json`), so fsc is handed nothing.
    NoBuild(Vec<String>),
    /// No complete answer: the build started no `Fsc` for the project (it
    /// failed first, the tree was up to date, or a replaced `CoreCompile`
    /// compiles some other way), or an invocation launched something other
    /// than the SDK's compiler, left no sign fsc ran, or ran on a command line
    /// the driver cannot read. With the build's errors.
    Unanswered(Vec<String>),
}

/// A name a caller may set for a build, as a global property or an
/// environment variable (which MSBuild also reads as a property): one of
/// [`INPUT_NAMES`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InputName(String);

/// The names a caller may set, compared without case (as MSBuild compares
/// property names): the project properties, the ordinary shell variables and
/// the CLI switches the differentials vary. A positive list, so no caller can
/// reach the toolchain, the compiler, the restore or MSBuild's machinery
/// through a name nobody thought to refuse. `borzoi-msbuild`'s assembly-name
/// grader holds it to the names that derivation admits. A grader of an
/// environment rule sets names on no list through
/// [`BuildInputs::unlisted_env`].
pub const INPUT_NAMES: &[&str] = &[
    "AssemblyName",
    "Authors",
    "Configuration",
    "DebugType",
    "Description",
    "Deterministic",
    "GenerateDocumentationFile",
    "IsPackable",
    "IsTestProject",
    "LangVersion",
    "NoWarn",
    "Nullable",
    "Optimize",
    "OtherFlags",
    "OutputType",
    "Platform",
    "RootNamespace",
    "TargetFramework",
    "TargetFrameworks",
    "TreatWarningsAsErrors",
    "Version",
    "WarnOn",
    "WarningsAsErrors",
    "EDITOR",
    "LANG",
    "LC_ALL",
    "LC_CTYPE",
    "LOGNAME",
    "OLDPWD",
    "PAGER",
    "PWD",
    "SHELL",
    "SHLVL",
    "TERM",
    "TZ",
    "USER",
    "_",
    "DOTNET_CLI_TELEMETRY_OPTOUT",
    "DOTNET_NOLOGO",
    "DOTNET_NUGET_SIGNATURE_VERIFICATION",
    "DOTNET_SKIP_FIRST_TIME_EXPERIENCE",
    "DOTNET_SKIP_WORKLOAD_INTEGRITY_CHECK",
];

impl InputName {
    /// `name`, if it is one a caller may set.
    pub fn new(name: &str) -> Result<InputName, InputError> {
        if INPUT_NAMES.iter().any(|n| n.eq_ignore_ascii_case(name)) {
            Ok(InputName(name.to_string()))
        } else {
            Err(InputError::NotAnInput(name.to_string()))
        }
    }

    /// The name.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Why a [`BuildInputs`] refuses a name or value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputError {
    /// Not one of [`INPUT_NAMES`].
    NotAnInput(String),
    /// Set twice (names compare without case).
    Repeated(String),
    /// A value the command line or the environment cannot carry verbatim: a
    /// global's `;`, `,`, `"` or line break, or a NUL in either.
    Unpassable { name: String, value: String },
    /// A name [`BuildInputs::unlisted_env`] refuses: one of
    /// [`INPUT_NAMES`], one no variable can have, or one of [`MACHINERY`].
    Refused(String),
}

/// The prefixes of the variables [`BuildInputs::unlisted_env`] refuses,
/// compared without case (as a tool on Windows compares names): the host's
/// and the runtime's knobs, NuGet's and MSBuild's switches, and the dynamic
/// loader's, any of which may choose what the build runs. A grader whose
/// subject commits under one, needing it built, has found its failure.
pub const MACHINERY: &[&str] = &[
    "DOTNET_", "COMPLUS_", "CORECLR_", "NUGET_", "MSBUILD", "DYLD_", "LD_",
];

/// What a caller sets for a build beyond the tree: global properties (`-p:`)
/// and environment variables, over [`build_environment`]. Built only through
/// its checked methods.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BuildInputs {
    globals: Vec<(InputName, String)>,
    env: Vec<(InputName, String)>,
    package_source: Option<PathBuf>,
    packages_folder: Option<PathBuf>,
}

impl BuildInputs {
    /// No globals and no variables beyond [`build_environment`].
    pub fn new() -> BuildInputs {
        BuildInputs::default()
    }

    /// With the global property `name` set to `value`.
    pub fn global(mut self, name: &str, value: &str) -> Result<BuildInputs, InputError> {
        let name = self.fresh(name)?;
        if value.contains([';', ',', '"', '\r', '\n', '\0']) {
            return Err(InputError::Unpassable {
                name: name.0,
                value: value.to_string(),
            });
        }
        self.globals.push((name, value.to_string()));
        Ok(self)
    }

    /// With the environment variable `name` set to `value`.
    pub fn env(mut self, name: &str, value: &str) -> Result<BuildInputs, InputError> {
        let name = self.fresh(name)?;
        if value.contains('\0') {
            return Err(InputError::Unpassable {
                name: name.0,
                value: value.to_string(),
            });
        }
        self.env.push((name, value.to_string()));
        Ok(self)
    }

    /// With the environment variable `name` set to `value`, where `name` is on
    /// no list: for a grader of an environment rule, whose subject claims a
    /// variable it does not list is inert, and which must set such names
    /// whatever they are. Refuses one of [`INPUT_NAMES`] (set through
    /// [`Self::env`]), one of [`build_environment`]'s
    /// ([`BUILD_ENVIRONMENT_NAMES`], held fixed), one starting with a
    /// [`MACHINERY`] prefix, and a name no variable can have (empty, or
    /// holding `=` or NUL). Whatever it sets, the build's launch checks still
    /// decide whether fsc's arguments are the SDK compiler's.
    pub fn unlisted_env(mut self, name: &str, value: &str) -> Result<BuildInputs, InputError> {
        let refused = name.is_empty()
            || name.contains(['=', '\0'])
            || INPUT_NAMES.iter().any(|n| n.eq_ignore_ascii_case(name))
            || BUILD_ENVIRONMENT_NAMES
                .iter()
                .any(|n| n.eq_ignore_ascii_case(name))
            || MACHINERY.iter().any(|prefix| {
                name.get(..prefix.len())
                    .is_some_and(|head| head.eq_ignore_ascii_case(prefix))
            });
        if refused {
            return Err(InputError::Refused(name.to_string()));
        }
        if value.contains('\0') {
            return Err(InputError::Unpassable {
                name: name.to_string(),
                value: value.to_string(),
            });
        }
        let taken = self
            .globals
            .iter()
            .chain(&self.env)
            .any(|(n, _)| n.0.eq_ignore_ascii_case(name));
        if taken {
            return Err(InputError::Repeated(name.to_string()));
        }
        self.env
            .push((InputName(name.to_string()), value.to_string()));
        Ok(self)
    }

    /// The global properties, in the order set.
    pub fn globals(&self) -> impl Iterator<Item = (&str, &str)> {
        self.globals.iter().map(|(n, v)| (n.as_str(), v.as_str()))
    }

    /// With the local package folder `dir` added to the restore's sources
    /// (`RestoreSources`, after [`build_environment`]'s own), so a fixture can
    /// reference a package it made.
    pub fn package_source(mut self, dir: &Path) -> BuildInputs {
        self.package_source = Some(dir.to_path_buf());
        self
    }

    /// With the restore extracting into the package folder `dir`
    /// (`NUGET_PACKAGES`) in place of [`build_environment`]'s, so a fixture's
    /// own packages stay out of the shared one.
    pub fn packages_folder(mut self, dir: &Path) -> BuildInputs {
        self.packages_folder = Some(dir.to_path_buf());
        self
    }

    /// The environment variables a build under these inputs sets over
    /// [`build_environment`]: those set by name, in the order set, then the
    /// package source and folder.
    pub fn env_vars(&self) -> Vec<(String, String)> {
        let mut vars: Vec<(String, String)> = self
            .env
            .iter()
            .map(|(n, v)| (n.as_str().to_string(), v.clone()))
            .collect();
        if let Some(dir) = &self.package_source {
            let base = build_environment()
                .into_iter()
                .find(|(name, _)| name == "RestoreSources")
                .map(|(_, value)| value);
            let value = match base {
                Some(base) if !base.is_empty() => format!("{base};{}", dir.display()),
                _ => dir.display().to_string(),
            };
            vars.push(("RestoreSources".to_string(), value));
        }
        if let Some(dir) = &self.packages_folder {
            vars.push(("NUGET_PACKAGES".to_string(), dir.display().to_string()));
        }
        vars
    }

    /// `name`, checked, and set neither as a global nor as a variable, since
    /// a variable is read as a property of the same name.
    fn fresh(&self, name: &str) -> Result<InputName, InputError> {
        let name = InputName::new(name)?;
        let taken = self
            .globals
            .iter()
            .chain(&self.env)
            .any(|(n, _)| n.0.eq_ignore_ascii_case(&name.0));
        if taken {
            return Err(InputError::Repeated(name.0));
        }
        Ok(name)
    }
}

/// One [`fsc_args`] call.
#[derive(Debug, Clone, Copy)]
pub struct FscArgsRequest<'a> {
    /// The project file to build, where it lies. The build writes beside it
    /// (and beside the projects it references), as a build does.
    pub project: &'a Path,
    /// The global properties and environment variables to build under.
    pub inputs: &'a BuildInputs,
}

/// What fsc is handed for `request`'s project in a real build of it (see the
/// module documentation).
pub fn fsc_args(request: &FscArgsRequest) -> Result<FscBuild, FscArgsDecline> {
    let project = lexically_normal(
        &std::path::absolute(request.project)
            .unwrap_or_else(|e| panic!("absolute path of {}: {e}", request.project.display())),
    );
    let scratch = ScratchDir::new();
    instrumented_build(&scratch.0, &project, request.inputs)
}

/// [`fsc_args`]'s build: [`build_command`] with `FscArgsLogger` and a
/// diagnostic file log, which write to `scratch`, and the logger's report
/// read.
fn instrumented_build(
    scratch: &Path,
    project: &Path,
    inputs: &BuildInputs,
) -> Result<FscBuild, FscArgsDecline> {
    // MSBuild splits a logger switch at `,` and `;`, and decodes `%XX`, so a
    // scratch directory spelled with them would put the logs elsewhere
    // (outside the directory, and not removed with it).
    if scratch.to_string_lossy().contains([',', ';', '%']) {
        return Err(FscArgsDecline::NoBuild(vec![format!(
            "the scratch directory {} holds `,`, `;` or `%`, which MSBuild's logger switches split or decode",
            scratch.display()
        )]));
    }
    let out = scratch.join("fsc-args.json");
    let logger = apphost().with_extension("dll");
    // MSBuild splits a logger switch at `,` and `;`, quoted or not.
    assert!(
        !logger.to_string_lossy().contains([',', ';']),
        "MSBuild cannot load the logger from {}, whose path holds a `,` or `;`",
        logger.display()
    );

    let mut cmd = build_command(project, inputs);
    cmd.arg(format!(
        "-logger:MsBuildConditionOracle.Program+FscArgsLogger,{};{}",
        logger.display(),
        out.display()
    ))
    // A diagnostic file log makes MSBuild log every task's inputs, which is
    // how the logger learns the `Fsc` task's compiler parameters; it sets
    // nothing the build can read (`MSBUILDLOGTASKINPUTS` and `-bl` each set a
    // property).
    .arg(format!(
        "-flp:v=diag;logfile={}",
        scratch.join("build.log").display()
    ));
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
        Ok(json) => parse_logger_output(project, &json),
        // The MSBuild the project's SDK selection runs cannot load the
        // logger (an SDK older than the runtime the oracle targets).
        Err(_) if report.contains("error MSB1021") => {
            Err(FscArgsDecline::Unanswered(vec![format!(
                "the build's MSBuild could not load the logger:\n{report}"
            )]))
        }
        // A response file of the tree's own (`Directory.Build.rsp`, a
        // project-local `MSBuild.rsp`) can hand MSBuild a switch it rejects.
        Err(_) if report.contains("error MSB1") && has_response_file(project) => {
            Err(FscArgsDecline::Unanswered(vec![format!(
                "MSBuild rejected a switch, and the project has a response file:\n{report}"
            )]))
        }
        // MSBuild's other command-line errors (`MSB1xxx`: a switch it
        // rejects) are this driver's fault, and loud.
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

/// The build [`fsc_args`] runs, before its loggers: `dotnet msbuild
/// -nodeReuse:false -restore -t:Build` of `project`, in its directory, under
/// `inputs`' globals, in [`build_environment`] plus `inputs`' variables.
/// `-nodeReuse:false` keeps MSBuild from leaving worker nodes behind, which
/// could hold the driver's pipes open; it changes nothing fsc is handed.
fn build_command(project: &Path, inputs: &BuildInputs) -> Command {
    let mut cmd = Command::new("dotnet");
    cmd.current_dir(project.parent().expect("a project file has a directory"))
        .args(["msbuild", "-nodeReuse:false", "-restore", "-t:Build"]);
    for (name, value) in inputs.globals() {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(project).env_clear();
    cmd.envs(build_environment());
    cmd.envs(inputs.env_vars());
    cmd
}

/// Whether `invocation` launched the running SDK's own compiler: its
/// `ToolPath` and `ToolExe` name the program running the build (`host`, the
/// logger's process), and the task assembly that ran and its
/// `DotnetFscCompilerPath` are `FSharp/FSharp.Build.dll` and `FSharp/fsc.dll`
/// under the directory of the MSBuild running the build (`msbuild`, the SDK's
/// own), each compared as canonical paths. A project can choose both the
/// task assembly and the compiler, so neither is held to the other. Each
/// path must be absolute: a relative one is resolved by the process that
/// reads it, whose directory is not this one.
fn sdk_launch(invocation: &FscInvocation, host: Option<&Path>, msbuild: Option<&Path>) -> bool {
    let canonical = |path: &Path| {
        path.is_absolute()
            .then(|| std::fs::canonicalize(path).ok())
            .flatten()
    };
    let compiler = |name: &str| invocation.compiler.get(name).map(String::as_str);
    let (Some(host), Some(msbuild), Some(tool_path), Some(tool_exe), Some(fsc)) = (
        host,
        msbuild,
        compiler("ToolPath"),
        compiler("ToolExe"),
        compiler("DotnetFscCompilerPath")
            .and_then(|quoted| quoted.strip_prefix('"')?.strip_suffix('"')),
    ) else {
        return false;
    };
    let same = |a: Option<PathBuf>, b: Option<PathBuf>| a.is_some() && a == b;
    let fsharp = msbuild.join("FSharp");
    same(
        canonical(&Path::new(tool_path).join(tool_exe)),
        canonical(host),
    ) && same(
        canonical(Path::new(&invocation.task_assembly)),
        canonical(&fsharp.join("FSharp.Build.dll")),
    ) && same(
        canonical(Path::new(fsc)),
        canonical(&fsharp.join("fsc.dll")),
    )
}

/// Whether MSBuild's command line reads a response file for `project`: a
/// `MSBuild.rsp` beside it, or a `Directory.Build.rsp` there or above.
fn has_response_file(project: &Path) -> bool {
    let dir = project.parent().expect("a project file has a directory");
    dir.join("MSBuild.rsp").is_file()
        || dir
            .ancestors()
            .any(|ancestor| ancestor.join("Directory.Build.rsp").is_file())
}

/// What the `dotnet` host prints when no installed SDK satisfies the
/// project's `global.json`, which it does before MSBuild starts.
const HOST_SDK_FAILURES: &[&str] = &[
    "A compatible .NET SDK was not found",
    "A compatible installed .NET SDK for global.json version",
];

/// A directory of [`fsc_args`]'s own for one call, which no other call in
/// any process shares: named for this process and a process-wide counter,
/// and made (owner-only) without its parents, which fails rather than adopt one that already
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
        // Owner-only from the start: the logs hold the caller's globals.
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
        match builder.create(&dir) {
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
    let host = value["processPath"].as_str().map(PathBuf::from);
    let msbuild = value["msbuildDirectory"].as_str().map(PathBuf::from);
    let unanswered = |why: String| {
        let mut all = vec![why];
        all.extend(errors.iter().cloned());
        Err(FscArgsDecline::Unanswered(all))
    };
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
            return unanswered(format!(
                "an Fsc command line could not be read: {}",
                run["problem"]
            ));
        };
        let invocation = FscInvocation {
            project: run_project,
            globals: strings(&run["globals"]),
            response_file: response_file.to_string(),
            task_assembly: run["taskAssembly"].as_str().unwrap_or_default().to_string(),
            compiler: strings(&run["compiler"]),
        };
        // The arguments are what the `Fsc` task handed its launcher; they
        // are fsc's only when the launcher is the program running the build,
        // running its SDK's `fsc.dll`, and not some program that may pass on
        // more.
        if !sdk_launch(&invocation, host.as_deref(), msbuild.as_deref()) {
            return unanswered(format!(
                "Fsc launched something other than the SDK's compiler: {:?}",
                invocation.compiler
            ));
        }
        // That fsc ran is fsc's own evidence, tied to this invocation: an
        // invocation without it may have run silently or not at all, and
        // either way the answer would be incomplete.
        let fsc_spoke = run["compilerOutput"]
            .as_array()
            .is_some_and(|output| !output.is_empty());
        if !fsc_spoke {
            return unanswered(
                "an Fsc invocation left no sign fsc ran (its banner or a diagnostic)".to_string(),
            );
        }
        invocations.push(invocation);
    }
    if invocations.is_empty() {
        unanswered(format!(
            "the build {} without starting Fsc for the project",
            if succeeded { "succeeded" } else { "failed" }
        ))
    } else {
        Ok(FscBuild {
            msbuild_directory: msbuild.unwrap_or_default(),
            succeeded,
            invocations,
        })
    }
}

#[cfg(test)]
mod tests {
    /// A scratch directory the logger switches cannot spell is refused before
    /// MSBuild runs, so no log lands outside it.
    #[test]
    fn an_unrepresentable_scratch_directory_runs_no_build() {
        for scratch in ["/tmp/a;b", "/tmp/a,b", "/tmp/a%3Bb"] {
            let result = super::instrumented_build(
                std::path::Path::new(scratch),
                std::path::Path::new("/nonexistent/Demo.fsproj"),
                &super::BuildInputs::new(),
            );
            assert!(
                matches!(&result, Err(super::FscArgsDecline::NoBuild(why)) if why[0].contains("scratch directory")),
                "{scratch}: {result:?}"
            );
        }
    }

    use super::{BuildInputs, FscArgsRequest, InputError, fsc_args, scratch_dir};
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

    /// What chooses the toolchain, the restore or MSBuild's own machinery
    /// cannot be set, in any case, as a global or a variable.
    #[test]
    fn inputs_refuse_what_chooses_the_toolchain() {
        for name in [
            "DOTNET_HOST_PATH",
            "MSBuildIsRestoring",
            "NUGET_PACKAGES",
            "PATH",
            "RestoreAdditionalProjectSources",
            "FscToolExe",
            "FSharpBuildAssemblyFile",
            "DirectoryBuildTargetsPath",
            "SkipCompilerExecution",
            "",
            "A;B",
        ] {
            let refused = |e: InputError| matches!(e, InputError::NotAnInput(_));
            assert!(
                BuildInputs::new().env(name, "x").is_err_and(refused),
                "{name} as a variable"
            );
            assert!(
                BuildInputs::new().global(name, "x").is_err_and(refused),
                "{name} as a global"
            );
        }
        let repeated = BuildInputs::new()
            .global("AssemblyName", "A")
            .unwrap()
            .env("assemblyname", "B");
        assert_eq!(
            repeated,
            Err(InputError::Repeated("assemblyname".to_string()))
        );
        for value in ["a;b", "a,b", "a\"b", "a\nb", "a\rb"] {
            assert!(
                BuildInputs::new()
                    .global("OtherFlags", value)
                    .is_err_and(|e| matches!(e, InputError::Unpassable { .. })),
                "{value:?}"
            );
        }
        assert!(
            BuildInputs::new()
                .env("OtherFlags", "--out:x\n-o:y")
                .is_ok()
        );
    }

    /// A name on no list can be set, but not one of the listed inputs, one
    /// the build environment holds fixed, one choosing the machinery (in any
    /// case), or one no variable can have.
    #[test]
    fn unlisted_variables_refuse_the_machinery() {
        for name in [
            "BORZOI_X",
            "1FOO",
            "A-B.C D",
            "ProgramFiles(x86)",
            "x\ny",
            "_x",
        ] {
            assert!(
                BuildInputs::new().unlisted_env(name, "v\n--out:x").is_ok(),
                "{name:?}"
            );
        }
        for name in [
            "",
            "A=B",
            "A\0B",
            "AssemblyName",
            "assemblyname",
            "_",
            "PATH",
            "path",
            "HOME",
            "TMPDIR",
            "RestoreSources",
            "DOTNET_ROOT",
            "dotnet_host_path",
            "COMPlus_gcServer",
            "CORECLR_PROFILER",
            "NUGET_PACKAGES",
            "MSBuildSDKsPath",
            "MSBUILDDEBUGONSTART",
            "DYLD_INSERT_LIBRARIES",
            "LD_PRELOAD",
        ] {
            assert!(
                matches!(
                    BuildInputs::new().unlisted_env(name, "v"),
                    Err(InputError::Refused(_))
                ),
                "{name:?}"
            );
        }
        let repeated = BuildInputs::new()
            .unlisted_env("BORZOI_X", "a")
            .unwrap()
            .unlisted_env("borzoi_x", "b");
        assert_eq!(repeated, Err(InputError::Repeated("borzoi_x".to_string())));
        assert!(matches!(
            BuildInputs::new().unlisted_env("BORZOI_X", "a\0b"),
            Err(InputError::Unpassable { .. })
        ));
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
        let inputs = BuildInputs::new();
        let answers: Vec<_> = std::thread::scope(|scope| {
            let handles: Vec<_> = projects
                .iter()
                .map(|project| {
                    let inputs = &inputs;
                    scope.spawn(move || fsc_args(&FscArgsRequest { project, inputs }))
                })
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
