//! What the F# compiler is handed for a project, read off a **real build**:
//! [`fsc_args`] runs `dotnet msbuild -restore -t:Build` on it with
//! `tools/msbuild-condition-oracle`'s `FscArgsLogger` attached, and parses
//! each `Fsc` invocation's response file into an [`FscArguments`] at the
//! boundary.
//!
//! It runs the build rather than imitating one, and adds nothing to it but
//! loggers: the restore, the targets, the project references, the global
//! properties and the compiler are the CLI's own. The arguments are MSBuild's
//! account of what the `Fsc` task handed its launcher, so they are answered
//! only when that launcher is the build's `dotnet` running its SDK's
//! `fsc.dll`; that fsc ran on them is fsc's own account, its banner or a
//! diagnostic in the task's context. Anything less is no answer. A project
//! already built is up to date, so its build runs no compiler, and the driver
//! says it cannot answer rather than forcing one; the fixtures it serves are
//! built fresh.
//!
//! No observation of a build is invisible to a build that looks for it: the
//! loggers set no property, but a project can read the process's command
//! line (`$([System.Environment]::CommandLine)`). So every answer is checked
//! against a plain build of the same tree, with the caller's globals and
//! environment and no other switch. The instrumented build runs first; the
//! files it added under the tree root the caller names (the directory
//! holding the project and its references, which the call owns while it
//! runs) are recorded and removed, and the plain build must then add the
//! same files, byte for byte (but for
//! ResolveAssemblyReference's state cache, `*.AssemblyReference.cache`, which
//! records its references' times: measured, two plain builds of one tree
//! differ in that file alone). Among them must be the output and reference
//! assembly that each reported invocation's `-o:` and `--refout:` name. A
//! build that rewrites or removes a file that was there before it, or starts
//! a project outside the tree root, writes where the check cannot compare,
//! and is not answered either.
//!
//! So a build that reacts to the instrumentation by compiling something else
//! is not answered. What remains is a build that reacts and still writes the
//! same bytes everywhere: its reported arguments may differ from the plain
//! build's (a `--define` the source never tests, say), but only in ways that
//! change nothing a build of it writes. That is the residual: what is
//! reported is exactly what the instrumented build handed fsc, and equivalent
//! to the plain build's in everything fsc writes. A build that is not
//! deterministic fails the comparison, which is sound. Each call builds twice,
//! and leaves the tree as the plain build left it.
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
    /// failed first, the project was up to date, or a replaced `CoreCompile`
    /// compiles some other way), or an invocation launched something other
    /// than the SDK's compiler, left no sign fsc ran, or ran on a command
    /// line the driver cannot read; or the plain build of the tree wrote
    /// other files than the instrumented one, or either wrote where the
    /// comparison cannot see. With the build's errors.
    Unanswered(Vec<String>),
}

/// One [`fsc_args`] call: which project to build, under what, and the tree
/// the call owns while it runs.
#[derive(Debug, Clone, Copy)]
pub struct FscArgsRequest<'a> {
    /// The directory the build's files live in: the project and every project
    /// its build starts (its project references) must lie under it, and it is
    /// what the comparison with a plain build covers. **The call owns it while
    /// it runs**: it removes whatever appears under it between the two builds,
    /// so nothing else may write there (the callers' trees are fixtures they
    /// laid out in directories of their own, one per call).
    pub tree_root: &'a Path,
    /// The project file to build, under [`Self::tree_root`]. It is built by
    /// the path given, made absolute and lexically normal but not resolved
    /// through links (MSBuild names the project after the path it is handed).
    pub project: &'a Path,
    /// Global properties for the build. A value may not hold `;`, `,` or `"`,
    /// which the command line would split or strip.
    pub globals: &'a [(String, String)],
    /// Environment variables for the build, over [`build_environment`].
    pub env: &'a [(String, String)],
}

/// What fsc is handed for `request`'s project in a real `dotnet msbuild
/// -restore -t:Build` under its global properties, in [`build_environment`]
/// plus its environment, checked against a plain build of its tree (see the
/// module documentation).
///
/// # Panics
///
/// If the project is not under the tree root, or a global's value holds `;`,
/// `,` or `"`.
pub fn fsc_args(request: &FscArgsRequest) -> Result<FscBuild, FscArgsDecline> {
    let FscArgsRequest {
        tree_root,
        project,
        globals,
        env,
    } = *request;
    let absolute = |path: &Path| {
        lexically_normal(
            &std::path::absolute(path)
                .unwrap_or_else(|e| panic!("absolute path of {}: {e}", path.display())),
        )
    };
    let (root, project) = (absolute(tree_root), absolute(project));
    assert!(
        project.starts_with(&root),
        "the project {} is not under the tree root {}",
        project.display(),
        root.display()
    );
    let dir = project.parent().expect("a project file has a directory");
    for (name, value) in globals {
        assert!(
            !value.contains([';', ',', '"']),
            "global {name}={value:?} cannot be passed on the command line verbatim"
        );
    }
    let before = Tree::scan(&root);
    let build = instrumented_build(&root, &project, globals, env)?;

    // The observer check: the same tree built again with no instrumentation
    // at all must write what the instrumented build wrote, byte for byte. A
    // build that reacts to the instrumentation (it can read the process's
    // command line) then writes something else, and is not answered.
    let instrumented = before
        .written(&root)
        .map_err(|why| FscArgsDecline::Unanswered(vec![why]))?;
    before.revert(&root);
    let plain_succeeded = plain_build(&project, globals, env);
    let plain = before
        .written(&root)
        .map_err(|why| FscArgsDecline::Unanswered(vec![why]))?;
    if let Some(difference) = first_difference(&instrumented, &plain) {
        return Err(FscArgsDecline::Unanswered(vec![format!(
            "the instrumented build wrote other files than the plain build: {difference}"
        )]));
    }
    if plain_succeeded != build.succeeded {
        return Err(FscArgsDecline::Unanswered(vec![format!(
            "the instrumented build {} and the plain build {}",
            if build.succeeded {
                "succeeded"
            } else {
                "failed"
            },
            if plain_succeeded {
                "succeeded"
            } else {
                "failed"
            },
        )]));
    }
    // What fsc wrote, by the instrumented run's own reading, is what the
    // plain build wrote too.
    for invocation in &build.invocations {
        let args = invocation.arguments().map_err(|e| {
            FscArgsDecline::Unanswered(vec![format!("an Fsc response file fsc rejects: {e:?}")])
        })?;
        let refout = args
            .options
            .iter()
            .filter(|option| option.name == "refout")
            .map(|option| option.argument.clone());
        for path in args.output.into_iter().chain(refout) {
            let path = lexically_normal(&dir.join(path));
            if !plain.contains_key(&path) {
                return Err(FscArgsDecline::Unanswered(vec![format!(
                    "the plain build wrote no {}, which the instrumented build's fsc names",
                    path.display()
                )]));
            }
        }
    }
    Ok(build)
}

/// The files a build writes whose bytes differ between two builds of one
/// tree, so the observer check leaves them out: ResolveAssemblyReference's
/// state cache records its references' modification times. Measured: two
/// plain builds of a project with a project reference, a documentation file
/// and an executable output differ in this file alone.
fn nondeterministic(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".AssemblyReference.cache"))
}

/// The first way two builds' written files differ, but for those
/// [`nondeterministic`] leaves out, or `None`.
fn first_difference(
    a: &BTreeMap<PathBuf, Vec<u8>>,
    b: &BTreeMap<PathBuf, Vec<u8>>,
) -> Option<String> {
    let keys: std::collections::BTreeSet<&PathBuf> = a
        .keys()
        .chain(b.keys())
        .filter(|path| !nondeterministic(path))
        .collect();
    keys.into_iter()
        .find_map(|path| match (a.get(path), b.get(path)) {
            (Some(x), Some(y)) if x == y => None,
            (Some(_), Some(_)) => Some(format!("{} differs", path.display())),
            (Some(_), None) => Some(format!(
                "only the instrumented build wrote {}",
                path.display()
            )),
            (None, _) => Some(format!("only the plain build wrote {}", path.display())),
        })
}

/// A directory tree's entries, as they stand: every entry but a directory
/// (links are not followed) with whether it is a regular file, its length and
/// its modification time, by which a later scan sees it rewritten; and the
/// directories.
struct Tree {
    files: BTreeMap<PathBuf, Stamp>,
    dirs: std::collections::BTreeSet<PathBuf>,
}

/// What [`Tree`] records of an entry.
#[derive(PartialEq, Eq)]
struct Stamp {
    regular: bool,
    len: u64,
    modified: Option<std::time::SystemTime>,
}

impl Tree {
    fn scan(root: &Path) -> Tree {
        let mut tree = Tree {
            files: BTreeMap::new(),
            dirs: std::collections::BTreeSet::new(),
        };
        tree.walk(root);
        tree
    }

    fn walk(&mut self, dir: &Path) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let Ok(meta) = std::fs::symlink_metadata(&path) else {
                continue;
            };
            if meta.is_dir() {
                self.dirs.insert(path.clone());
                self.walk(&path);
            } else {
                let stamp = Stamp {
                    regular: meta.is_file(),
                    len: meta.len(),
                    modified: meta.modified().ok(),
                };
                self.files.insert(path, stamp);
            }
        }
    }

    /// The files under `root` a build wrote since this scan, with their
    /// bytes; `Err` when it rewrote or removed one that was here, which
    /// [`Self::revert`] cannot put back, or added anything but a regular file
    /// (a link or a FIFO, which reading could follow or wait on), or one
    /// cannot be read.
    fn written(&self, root: &Path) -> Result<BTreeMap<PathBuf, Vec<u8>>, String> {
        let now = Tree::scan(root);
        for (path, stamp) in &self.files {
            if now.files.get(path) != Some(stamp) {
                return Err(format!(
                    "the build rewrote or removed {}, which was there before it",
                    path.display()
                ));
            }
        }
        now.files
            .iter()
            .filter(|(path, _)| !self.files.contains_key(*path))
            .map(|(path, stamp)| {
                if !stamp.regular {
                    return Err(format!(
                        "the build left {}, not a regular file",
                        path.display()
                    ));
                }
                std::fs::read(path)
                    .map(|bytes| (path.clone(), bytes))
                    .map_err(|e| format!("reading {}: {e}", path.display()))
            })
            .collect()
    }

    /// Put `root` back as this scan found it: remove every file and directory
    /// a build added since.
    fn revert(&self, root: &Path) {
        let now = Tree::scan(root);
        for path in now.files.keys().filter(|p| !self.files.contains_key(*p)) {
            let _ = std::fs::remove_file(path);
        }
        for dir in now.dirs.iter().rev().filter(|d| !self.dirs.contains(*d)) {
            let _ = std::fs::remove_dir(dir);
        }
    }
}

/// [`fsc_args`]'s instrumented build: the CLI's, with `FscArgsLogger` and a
/// diagnostic file log, and the logger's report read.
fn instrumented_build(
    root: &Path,
    project: &Path,
    globals: &[(String, String)],
    env: &[(String, String)],
) -> Result<FscBuild, FscArgsDecline> {
    let scratch = ScratchDir::new();
    let out = scratch.0.join("fsc-args.json");
    let logger = apphost().with_extension("dll");
    // MSBuild splits a logger switch at `,` and `;`, quoted or not.
    assert!(
        !logger.to_string_lossy().contains([',', ';']),
        "MSBuild cannot load the logger from {}, whose path holds a `,` or `;`",
        logger.display()
    );

    let mut cmd = build_command(project, globals, env);
    cmd.arg(format!(
        "-logger:MsBuildConditionOracle.Program+FscArgsLogger,{};{}",
        logger.display(),
        out.display()
    ))
    // A diagnostic file log makes MSBuild log every task's inputs, which is
    // how the logger learns the `Fsc` task's compiler parameters; it sets
    // nothing the build can read (`MSBUILDLOGTASKINPUTS` and `-bl` each set a
    // property). It goes to the call's scratch directory.
    .arg(format!(
        "-flp:v=diag;logfile={}",
        scratch.0.join("build.log").display()
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
        Ok(json) => parse_logger_output(root, project, &json),
        // The MSBuild the project's SDK selection runs cannot load the
        // logger (an SDK older than the runtime the oracle targets).
        Err(_) if report.contains("error MSB1021") => {
            Err(FscArgsDecline::Unanswered(vec![format!(
                "the build's MSBuild could not load the logger:\n{report}"
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

/// [`fsc_args`]'s plain build: the CLI's, with no switch beyond the caller's
/// globals, and nothing read from it but whether it succeeded and the files
/// it writes.
fn plain_build(project: &Path, globals: &[(String, String)], env: &[(String, String)]) -> bool {
    BoundedCommand::new(build_command(project, globals, env))
        .timeout(FSC_ARGS_TIMEOUT)
        .run()
        .unwrap_or_else(|e| panic!("dotnet msbuild of {}: {e}", project.display()))
        .status
        .success()
}

/// `dotnet msbuild -restore -t:Build` of `project` under `globals`, in its
/// directory, in [`build_environment`] plus `env`.
fn build_command(
    project: &Path,
    globals: &[(String, String)],
    env: &[(String, String)],
) -> Command {
    let mut cmd = Command::new("dotnet");
    cmd.current_dir(project.parent().expect("a project file has a directory"))
        .args([
            "msbuild",
            "-nologo",
            "-nodeReuse:false",
            "-restore",
            "-t:Build",
        ]);
    for (name, value) in globals {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(project).env_clear();
    cmd.envs(build_environment());
    cmd.envs(env.iter().map(|(name, value)| (name, value)));
    cmd
}

/// Whether `invocation` launched the running SDK's own compiler: its
/// `ToolPath` and `ToolExe` name the build's `dotnet` host (`host`, the build
/// process's `DOTNET_HOST_PATH`), and the task assembly that ran and its
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
fn parse_logger_output(
    tree: &Path,
    project: &Path,
    json: &str,
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
    let host = value["dotnetHostPath"].as_str().map(PathBuf::from);
    let msbuild = value["msbuildDirectory"].as_str().map(PathBuf::from);
    let unanswered = |why: String| {
        let mut all = vec![why];
        all.extend(errors.iter().cloned());
        Err(FscArgsDecline::Unanswered(all))
    };
    // The observer check compares what the build wrote under the tree root;
    // a project built outside it writes where the check does not look, and
    // the plain build would then find its outputs already there.
    //
    // `-restore` runs as a build submission of its own, whose first project is
    // started with `MSBuildIsRestoring` set; it starts the SDK's `NuGet.targets`,
    // and writes nothing but each project's restore outputs, in its `obj`.
    let started = value["projects"]
        .as_array()
        .expect("FscArgsLogger writes the projects it saw start");
    let mut restore_submissions = std::collections::BTreeMap::new();
    for entry in started {
        restore_submissions
            .entry(entry["submission"].as_i64())
            .or_insert_with(|| entry["globals"].get("MSBuildIsRestoring").is_some());
    }
    for entry in started {
        if restore_submissions[&entry["submission"].as_i64()] {
            continue;
        }
        let started = lexically_normal(Path::new(entry["project"].as_str().unwrap_or_default()));
        if !started.starts_with(tree) {
            return unanswered(format!(
                "the build started {}, outside {}",
                started.display(),
                tree.display()
            ));
        }
    }
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
        // are fsc's only when the launcher is the build's `dotnet` running
        // its SDK's `fsc.dll`, and not some program that may pass on more.
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
            succeeded,
            invocations,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{FscArgsRequest, fsc_args, scratch_dir};
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
                .map(|project| {
                    let tree_root = project.parent().unwrap();
                    scope.spawn(move || {
                        fsc_args(&FscArgsRequest {
                            tree_root,
                            project,
                            globals: &[],
                            env: &[],
                        })
                    })
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
