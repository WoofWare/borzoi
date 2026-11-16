//! Deterministic per-phase counts for one `.fsproj` evaluation as the server
//! runs it: retired instructions, heap allocations and bytes allocated, each
//! the minimum over `EVAL_COUNTS_REPS` runs (default 5).
//!
//! The phases:
//!
//! - **lsp.evaluate**: what the server pays to evaluate the project again
//!   after its cached evaluation is dropped: SDK discovery, every MSBuild
//!   pass, and building the checks that confirm the result later
//!   (`borzoi::workspace::Workspace::project`).
//! - **lsp.revalidate**: what the server pays in a dispatch-loop generation
//!   for a project whose cached evaluation is still current: confirming its
//!   reads against the disk (`Workspace::begin_generation`, then
//!   `Workspace::project`).
//! - **msbuild.evaluate**: one `parse_fsproj_with_imports` call with the
//!   server's resolvers, the server's first pass alone.
//! - **msbuild.reusing**: the same call through
//!   `parse_fsproj_with_imports_reusing`, keeping the parsed imports of the
//!   previous call, as the server does when it evaluates again.
//! - The parts of that call that do not depend on how the walk is written,
//!   each asked again over the call's own read set, one query per distinct
//!   read: **fs.text** (reading the files it read whole), **xml.parse**
//!   (parsing each as XML), **digest** (each text's `TextDigest`),
//!   **fs.other** (its other queries: `stat`s, listings and
//!   canonicalisations). Its `read_counts` say how many times it asked each
//!   kind, so a file read twice in one evaluation shows as more opens than
//!   distinct texts.
//!
//! The rest of `msbuild.evaluate` is the walk itself: expanding properties,
//! deciding conditions, matching globs and recording reads.
//!
//! Instructions come from the kernel's per-process counter
//! (`proc_pid_rusage`, macOS only; elsewhere the column reads `n/a`) and
//! include kernel mode, so the file-system phases carry the kernel's cost of
//! each call. Allocations come from a counting wrapper around the system
//! allocator. Wall time is not reported.
//!
//! # What MSBuild pays for the same project
//!
//! Then, unless `EVAL_COUNTS_MSBUILD=0`, the same project goes to the real
//! MSBuild, in-process in `tools/msbuild-condition-oracle` (its `bench` op),
//! pinned to the SDK our evaluation resolved and under the server's build
//! properties as global properties:
//!
//! - **oracle.fresh**: one evaluation in a new `ProjectCollection`; compare
//!   with `msbuild.evaluate`, and with `lsp.evaluate` for what the server
//!   does around it.
//! - **oracle.shared**: one evaluation in a `ProjectCollection` kept across
//!   evaluations, as a resident MSBuild host evaluates again; compare with
//!   `msbuild.reusing`. When nothing has changed the server does not evaluate
//!   at all, so `lsp.revalidate` is its cost there.
//! - **oracle.designtime**: what Ionide.ProjInfo, FsAutoComplete's project
//!   loader, runs to load the project: two evaluations and a design-time build
//!   through `CoreCompile`. The server has no counterpart: it reads the
//!   references from `project.assets.json` rather than running targets.
//!
//! Each mode runs in its own new oracle process. Its line gives the
//! instructions of the steady-state run and the managed bytes it allocated (a
//! garbage-collected heap's bytes, not comparable with the allocator's), then
//! **first**, the first run in that process, which pays to JIT MSBuild, and
//! **to-first**, everything the process retired from its start to that first
//! answer: .NET start-up, MSBuild's registration and the first run.
//!
//! The steady state needs care because .NET's tiered JIT recompiles hot code
//! on a background thread for seconds after new work, and how soon it lands
//! depends on the machine's load. A run measured before then pays for that
//! thread and runs unoptimised code, so on a loaded machine back-to-back
//! "warm" runs measured 2.6× apart in two processes. So before each batch of
//! `EVAL_COUNTS_REPS` runs the driver waits until the process is quiet (its
//! `idle` op), and it stops once two batches in a row fail to lower the
//! minimum by 1%; the line says how many batches that took. The count is
//! still the whole process's, kernel mode included.
//!
//! The lines after the three name the MSBuild that ran and compare the
//! `Compile` items of the evaluation each mode measured with ours, as sets
//! (the design-time build's are read before its targets run), which says
//! whether both sides evaluated the same project. The design-time build's intermediate and output directories go
//! to a temporary directory, not the project's, and only its process gets
//! `DOTNET_HOST_PATH`, which the `dotnet` CLI sets for the MSBuild it runs and
//! the `Fsc` task needs.
//!
//! ```sh
//! nix develop -c cargo run --release -p borzoi --example eval_counts
//! ```
//!
//! * `EVAL_COUNTS_PROJECT`: the `.fsproj` to evaluate. Default:
//!   `WoofWare.Incremental` from the whole-project gate's corpus cache.
//! * `EVAL_COUNTS_REPS` (default 5).
//! * `EVAL_COUNTS_LOOP`: run only `lsp.evaluate`, this many times, for a
//!   sampling profiler to attach to.
//! * `EVAL_COUNTS_MSBUILD=0`: skip the MSBuild rows.
//! * `BORZOI_MSBUILD_CONDITION_ORACLE`: a prebuilt oracle apphost; otherwise
//!   the oracle is built with `dotnet build -c Release`.

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::{Duration, SystemTime};

use borzoi::sdk_discovery::{SdkDiscovery, SdkDiscoveryEnv};
use borzoi::vfs::Nanos;
use borzoi::workspace::Workspace;
use borzoi_msbuild::observed::{
    self as msbuild_observed, ImportDocuments, Observation, Observer, TextDigest,
};
use borzoi_msbuild::{
    GlobResolver, ItemKind, ParsedProject, SdkResolution, SdkResolver, parse_fsproj_with_imports,
    parse_fsproj_with_imports_reusing,
};
use borzoi_oracle_harness::{BatchChild, BoundedCommand};
use serde_json::{Value, json};

/// The system allocator, counting calls and requested bytes.
struct Counting;

static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_BYTES: AtomicU64 = AtomicU64::new(0);

// SAFETY: every method forwards to `System` with its arguments unchanged.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(layout.size() as u64, Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(layout.size() as u64, Relaxed);
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(new_size as u64, Relaxed);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// Instructions this process has retired so far, where the platform says.
#[cfg(target_os = "macos")]
fn instructions_retired() -> Option<u64> {
    unsafe extern "C" {
        fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut u64) -> i32;
        fn getpid() -> i32;
    }
    /// `RUSAGE_INFO_V4`, whose struct is a 16-byte UUID followed by `u64`s.
    const RUSAGE_INFO_V4: i32 = 4;
    /// `ri_instructions`'s index among those `u64`s.
    const RI_INSTRUCTIONS: usize = 29;
    let mut buffer = [0u64; 64];
    // SAFETY: `buffer` is larger than `rusage_info_v4` (37 words).
    let rc = unsafe { proc_pid_rusage(getpid(), RUSAGE_INFO_V4, buffer.as_mut_ptr()) };
    (rc == 0).then(|| buffer[2 + RI_INSTRUCTIONS])
}

#[cfg(not(target_os = "macos"))]
fn instructions_retired() -> Option<u64> {
    None
}

/// What one run of a phase cost.
#[derive(Clone, Copy)]
struct Cost {
    instructions: Option<u64>,
    allocations: u64,
    allocated_bytes: u64,
}

impl Cost {
    fn min(self, other: Cost) -> Cost {
        Cost {
            instructions: match (self.instructions, other.instructions) {
                (Some(a), Some(b)) => Some(a.min(b)),
                _ => None,
            },
            allocations: self.allocations.min(other.allocations),
            allocated_bytes: self.allocated_bytes.min(other.allocated_bytes),
        }
    }
}

/// Run `f` `reps` times, print the cheapest run of each count, and return the
/// last result, dropped outside the measured region.
fn phase<T>(label: &str, reps: usize, mut f: impl FnMut() -> T) -> T {
    let mut best: Option<Cost> = None;
    let mut last = None;
    for _ in 0..reps {
        drop(last.take());
        let (a0, b0, i0) = (
            ALLOCATIONS.load(Relaxed),
            ALLOCATED_BYTES.load(Relaxed),
            instructions_retired(),
        );
        let result = std::hint::black_box(f());
        let i1 = instructions_retired();
        let cost = Cost {
            instructions: i0.zip(i1).map(|(i0, i1)| i1 - i0),
            allocations: ALLOCATIONS.load(Relaxed) - a0,
            allocated_bytes: ALLOCATED_BYTES.load(Relaxed) - b0,
        };
        best = Some(best.map_or(cost, |b| b.min(cost)));
        last = Some(result);
    }
    let best = best.expect("at least one rep");
    let instructions = best
        .instructions
        .map_or_else(|| "n/a".to_string(), |i| format!("{:.2} M", i as f64 / 1e6));
    println!(
        "{label:<18} {instructions:>12} {:>10} allocs {:>12} bytes",
        best.allocations, best.allocated_bytes
    );
    last.expect("at least one rep")
}

fn default_project() -> PathBuf {
    let cache = std::env::var_os("BORZOI_PROJECT_CORPUS_CACHE")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(std::env::var_os("HOME").expect("HOME is set"))
                .join(".cache/borzoi/project-corpus")
        });
    cache.join(
        "v2/project-corpus/Smaug123/WoofWare.Incremental/WoofWare.Incremental/WoofWare.Incremental.fsproj",
    )
}

/// The server's first MSBuild pass over `project`, with the server's
/// resolvers and default build properties.
fn evaluate_once(
    project: &Path,
    source: &str,
    env: &SdkDiscoveryEnv,
    extras: &HashMap<String, String>,
) -> ParsedProject {
    let disc = SdkDiscovery::for_project(project, env, &Observer::new())
        .expect("SDK discovery succeeds under nix develop");
    let resolver: &SdkResolver<'_> = &|name, observer| disc.resolve(name, observer);
    let glob_resolver: &GlobResolver<'_> = &borzoi_msbuild::glob_resolver::resolve;
    parse_fsproj_with_imports(
        source,
        project,
        extras,
        &env.build_environment,
        Some(resolver),
        Some(glob_resolver),
    )
    .expect("the project evaluates")
}

/// [`evaluate_once`] through `parse_fsproj_with_imports_reusing`, reusing
/// the imports `documents` holds and leaving this call's in it.
fn evaluate_reusing(
    project: &Path,
    source: &str,
    env: &SdkDiscoveryEnv,
    extras: &HashMap<String, String>,
    documents: &mut ImportDocuments,
) -> ParsedProject {
    let disc = SdkDiscovery::for_project(project, env, &Observer::new())
        .expect("SDK discovery succeeds under nix develop");
    let resolver: &SdkResolver<'_> = &|name, observer| disc.resolve(name, observer);
    let glob_resolver: &GlobResolver<'_> = &borzoi_msbuild::glob_resolver::resolve;
    parse_fsproj_with_imports_reusing(
        source,
        project,
        extras,
        &env.build_environment,
        Some(resolver),
        Some(glob_resolver),
        documents,
    )
    .expect("the project evaluates")
}

fn format_instructions(instructions: Option<u64>) -> String {
    instructions.map_or_else(|| "n/a".to_string(), |i| format!("{:.2} M", i as f64 / 1e6))
}

/// The oracle's apphost: `BORZOI_MSBUILD_CONDITION_ORACLE`, else built from
/// `tools/msbuild-condition-oracle`.
fn oracle_apphost() -> PathBuf {
    if let Some(bin) = std::env::var_os("BORZOI_MSBUILD_CONDITION_ORACLE") {
        // The oracle runs from the project's directory, so a relative path
        // must be resolved against ours first.
        return std::path::absolute(bin).expect("the oracle path resolves");
    }
    let project =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/msbuild-condition-oracle");
    let mut cmd = Command::new("dotnet");
    cmd.args(["build", "-c", "Release", "--nologo"])
        .arg(&project);
    BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(600))
        .run_ok("dotnet build msbuild-condition-oracle");
    project.join("bin/Release/net10.0/msbuild-condition-oracle")
}

/// One oracle process pinned to the SDK at `sdk_dir`, run from the project's
/// directory with this process's environment, which our evaluation reads too,
/// plus `DOTNET_HOST_PATH` when `dotnet_host` is given.
///
/// It runs on the runtime of the SDK's own dotnet root (`DOTNET_ROOT`),
/// rolled forward to its newest major, prereleases included, for an SDK
/// newer than the oracle's net10.0: that SDK's MSBuild needs its runtime.
/// This is how `borzoi_oracle_harness::workload_oracle` runs on SDK 11. Under
/// `nix develop` the root is the environment's own `DOTNET_ROOT` unless that
/// was pointed elsewhere.
/// A request that wedges panics rather than respawning: a respawned process
/// would measure a cold MSBuild as a warm one.
fn spawn_oracle(
    apphost: &Path,
    sdk_dir: &str,
    project_dir: &Path,
    dotnet_host: Option<&Path>,
) -> BatchChild {
    let (apphost, sdk_dir, project_dir, dotnet_host) = (
        apphost.to_path_buf(),
        sdk_dir.to_string(),
        project_dir.to_path_buf(),
        dotnet_host.map(Path::to_path_buf),
    );
    let what = format!("{} --msbuild-sdk {sdk_dir}", apphost.display());
    BatchChild::with_factory(
        Box::new(move || {
            let mut cmd = Command::new(&apphost);
            cmd.args(["--msbuild-sdk", &sdk_dir])
                .current_dir(&project_dir);
            let sdk = Path::new(&sdk_dir);
            let dotnet_root = sdk
                .parent()
                .and_then(Path::parent)
                .expect("an SDK directory sits at <dotnet-root>/sdk/<version>");
            cmd.env("DOTNET_ROOT", dotnet_root);
            let major: u32 = sdk
                .file_name()
                .and_then(|n| n.to_str())
                .and_then(|n| n.split('.').next())
                .and_then(|m| m.parse().ok())
                .expect("an SDK directory is named by its version");
            if major > 10 {
                cmd.env("DOTNET_ROLL_FORWARD", "LatestMajor")
                    .env("DOTNET_ROLL_FORWARD_TO_PRERELEASE", "1");
            }
            if let Some(host) = &dotnet_host {
                cmd.env("DOTNET_HOST_PATH", host);
            }
            cmd
        }),
        what,
        Duration::from_secs(1800),
        1,
    )
}

fn request(oracle: &mut BatchChild, request: &Value) -> Value {
    let answer: Value = serde_json::from_str(&oracle.request(&request.to_string()))
        .expect("the oracle answers JSON");
    assert!(
        answer.get("error").is_none(),
        "the oracle refused {request}: {answer}"
    );
    answer
}

/// Instructions a quiet oracle may retire while it sleeps for
/// [`QUIET_WINDOW_MS`]. A process with no background work retires next to
/// none; one whose tiered JIT is still recompiling retires hundreds of
/// millions.
const QUIET_INSTRUCTIONS: u64 = 10_000_000;
const QUIET_WINDOW_MS: u64 = 500;

/// Wait until `oracle`'s background threads are idle, or give up after a
/// minute. Returns whether it went quiet.
fn wait_until_quiet(oracle: &mut BatchChild) -> bool {
    for _ in 0..(60_000 / QUIET_WINDOW_MS) {
        let answer = request(oracle, &json!({"op": "idle", "ms": QUIET_WINDOW_MS}));
        match answer["instructions"].as_u64() {
            Some(i) if i > QUIET_INSTRUCTIONS => continue,
            _ => return true,
        }
    }
    false
}

/// A run's cost as the oracle reports it.
#[derive(Clone, Copy)]
struct OracleRun {
    instructions: Option<u64>,
    allocated_bytes: u64,
}

impl OracleRun {
    fn min(self, other: OracleRun) -> OracleRun {
        OracleRun {
            instructions: match (self.instructions, other.instructions) {
                (Some(a), Some(b)) => Some(a.min(b)),
                _ => None,
            },
            allocated_bytes: self.allocated_bytes.min(other.allocated_bytes),
        }
    }
}

fn oracle_runs(answer: &Value) -> Vec<OracleRun> {
    assert_eq!(
        answer["ok"],
        Value::Bool(true),
        "MSBuild failed: {}",
        answer["errors"]
    );
    answer["runs"]
        .as_array()
        .expect("runs is an array")
        .iter()
        .map(|run| OracleRun {
            instructions: run["instructions"].as_u64(),
            allocated_bytes: run["allocatedBytes"].as_u64().expect("allocatedBytes"),
        })
        .collect()
}

/// The most batches a mode runs before it reports a minimum that is still
/// falling.
const MAX_BATCHES: usize = 20;

/// Measure one `bench` mode in a new oracle process, print its line, and
/// return the oracle's first answer, for the caller to check the evaluation
/// against ours.
fn oracle_mode(
    label: &str,
    base: &Value,
    mode: &str,
    reps: usize,
    spawn: &dyn Fn() -> BatchChild,
) -> Value {
    let mut oracle = spawn();
    let bench = |oracle: &mut BatchChild, reps: usize| {
        let mut request_body = base.clone();
        request_body["mode"] = json!(mode);
        request_body["reps"] = json!(reps);
        request(oracle, &request_body)
    };
    let first_answer = bench(&mut oracle, 1);
    let first = oracle_runs(&first_answer)[0];
    let to_first = first_answer["processInstructions"].as_u64();

    let mut best: Option<OracleRun> = None;
    let mut batches = 0;
    let mut unimproved = 0;
    let mut always_quiet = true;
    while batches < MAX_BATCHES && unimproved < 2 {
        always_quiet &= wait_until_quiet(&mut oracle);
        let batch = oracle_runs(&bench(&mut oracle, reps))
            .into_iter()
            .reduce(OracleRun::min)
            .expect("at least one rep");
        batches += 1;
        let improved = match (best.and_then(|b| b.instructions), batch.instructions) {
            (Some(b), Some(i)) => (i as f64) < 0.99 * b as f64,
            // With no counter there is nothing to converge on.
            (_, None) => false,
            (None, Some(_)) => true,
        };
        unimproved = if improved { 0 } else { unimproved + 1 };
        best = Some(best.map_or(batch, |b| b.min(batch)));
    }
    let best = best.expect("at least one batch");
    let settled = if unimproved >= 2 {
        format!("{batches} batches")
    } else {
        format!("{batches} batches, still falling")
    };
    let quiet = if always_quiet { "" } else { ", never quiet" };
    println!(
        "{label:<18} {:>12} {:>10} {:>12} managed bytes   first {}, to-first {} ({settled}{quiet})",
        format_instructions(best.instructions),
        "",
        best.allocated_bytes,
        format_instructions(first.instructions),
        format_instructions(to_first),
    );
    first_answer
}

/// The MSBuild rows: see the module docs.
fn msbuild_rows(
    project: &Path,
    parsed: &ParsedProject,
    env: &SdkDiscoveryEnv,
    extras: &HashMap<String, String>,
    reps: usize,
) {
    // The SDK our evaluation imports `Microsoft.NET.Sdk` from: its root is
    // `<sdk>/Sdks/Microsoft.NET.Sdk/Sdk`.
    let disc = SdkDiscovery::for_project(project, env, &Observer::new())
        .expect("SDK discovery succeeds under nix develop");
    let sdk_dir = match disc.resolve("Microsoft.NET.Sdk", &Observer::new()) {
        Ok(SdkResolution::Single(paths)) => paths
            .root
            .ancestors()
            .nth(3)
            .expect("the SDK root is three levels below the SDK")
            .to_string_lossy()
            .into_owned(),
        other => panic!("Microsoft.NET.Sdk resolved to {other:?}"),
    };
    let sdk_dir = sdk_dir.as_str();
    println!("SDK {sdk_dir}");
    let apphost = oracle_apphost();
    let project_dir = project.parent().expect("the project is in a directory");
    let scratch = std::env::temp_dir().join(format!("borzoi-eval-counts-{}", std::process::id()));
    let base = json!({
        "op": "bench",
        "project": project,
        "globals": extras,
        "scratch": scratch,
    });
    // The `dotnet` CLI sets `DOTNET_HOST_PATH` to itself for the MSBuild it
    // runs, and the `Fsc` task runs the compiler through it, so a design-time
    // build reaching `CoreCompile` fails without it. The evaluation modes run
    // without it, as our evaluation does, so both read one environment.
    let dotnet_host = Path::new(sdk_dir).join("../../dotnet");
    let answers: Vec<Value> = [
        ("oracle.fresh", "fresh", None),
        ("oracle.shared", "shared", None),
        (
            "oracle.designtime",
            "designTime",
            Some(dotnet_host.as_path()),
        ),
    ]
    .into_iter()
    .map(|(label, mode, host)| {
        oracle_mode(label, &base, mode, reps, &|| {
            spawn_oracle(&apphost, sdk_dir, project_dir, host)
        })
    })
    .collect();
    // Only the design-time build writes there; a leftover directory is the
    // temporary directory's to clear, so a failure here is not worth a panic.
    let _ = std::fs::remove_dir_all(&scratch);
    println!(
        "MSBuild {}",
        answers[0]["msbuildBinPath"]
            .as_str()
            .expect("msbuildBinPath")
    );

    // Compared as sorted lists: ours are in the order the compiler reads them
    // (`CompileOrder` applied), MSBuild's in evaluation order, and the question
    // is only whether both found the same items.
    let mut ours: Vec<PathBuf> = parsed
        .items
        .iter()
        .filter(|item| item.kind == ItemKind::Compile)
        .map(|item| item.include.clone())
        .collect();
    ours.sort();
    for answer in &answers {
        let mut theirs: Vec<PathBuf> = answer["compile"]
            .as_array()
            .expect("compile is an array")
            .iter()
            .map(|p| PathBuf::from(p.as_str().expect("a path")))
            .collect();
        theirs.sort();
        println!(
            "same evaluation: Compile items {} (ours {}, MSBuild's {})",
            if theirs == ours { "equal" } else { "DIFFER" },
            ours.len(),
            theirs.len(),
        );
    }
}

fn main() {
    let project = std::env::var_os("EVAL_COUNTS_PROJECT")
        .map(PathBuf::from)
        .unwrap_or_else(default_project);
    let reps: usize = std::env::var("EVAL_COUNTS_REPS")
        .ok()
        .map(|r| r.parse().expect("EVAL_COUNTS_REPS is a number"))
        .unwrap_or(5);
    let env = SdkDiscoveryEnv::from_process_env();
    let mut workspace = Workspace::with_env(env.clone());
    let extras = workspace.build_properties();
    println!("project {}", project.display());

    assert!(
        workspace.project(&project).is_some(),
        "the project evaluates"
    );
    if let Some(loops) = std::env::var("EVAL_COUNTS_LOOP")
        .ok()
        .map(|n| n.parse::<usize>().expect("EVAL_COUNTS_LOOP is a number"))
    {
        phase("lsp.evaluate", loops, || {
            workspace.drop_every_evaluation();
            workspace.project(&project).is_some()
        });
        return;
    }
    phase("lsp.evaluate", reps, || {
        workspace.drop_every_evaluation();
        workspace.project(&project).is_some()
    });
    assert!(workspace.project(&project).is_some());
    phase("lsp.revalidate", reps, || {
        workspace.begin_generation(Nanos::of(SystemTime::now()));
        let current = workspace.project(&project).is_some();
        workspace.end_generation();
        current
    });

    let source = msbuild_observed::host_fs::read_to_string(&project).expect("the project reads");
    let parsed = phase("msbuild.evaluate", reps, || {
        evaluate_once(&project, &source, &env, &extras)
    });
    let mut documents = ImportDocuments::default();
    drop(evaluate_reusing(
        &project,
        &source,
        &env,
        &extras,
        &mut documents,
    ));
    phase("msbuild.reusing", reps, || {
        evaluate_reusing(&project, &source, &env, &extras, &mut documents)
    });
    let counts = parsed.read_counts;
    let reads = parsed.read_set.reads();
    let texts: Vec<&Path> = reads
        .iter()
        .filter(|read| matches!(read.observation, Observation::Text(Ok(_))))
        .map(|read| read.path.as_path())
        .collect();
    let others: Vec<_> = reads
        .iter()
        .filter(|read| !matches!(read.observation, Observation::Text(_)))
        .collect();
    let bytes: usize = texts
        .iter()
        .map(|path| {
            msbuild_observed::host_fs::read_to_string(path)
                .map(|t| t.len())
                .unwrap_or(0)
        })
        .sum();
    println!(
        "read_counts: {} opens, {} stats, {} listings, {} canonicalisations; \
         {} distinct reads, {} distinct texts ({} bytes), {} other distinct queries",
        counts.opens,
        counts.stats,
        counts.listings,
        counts.canonicalizations,
        reads.len(),
        texts.len(),
        bytes,
        others.len()
    );

    for (label, matches) in [
        (
            "canonical",
            (|o: &Observation| matches!(o, Observation::Canonical(_))) as fn(&Observation) -> bool,
        ),
        ("kind", |o| matches!(o, Observation::Kind(_))),
        ("link_kind", |o| matches!(o, Observation::LinkKind(_))),
        ("listing", |o| matches!(o, Observation::Listing(_))),
        ("stamp", |o| matches!(o, Observation::Stamp(_))),
    ] {
        let of_kind: Vec<_> = others
            .iter()
            .filter(|read| matches(&read.observation))
            .collect();
        phase(&format!("fs.{label}({})", of_kind.len()), reps, || {
            of_kind
                .iter()
                .map(|read| msbuild_observed::answer_now(&read.path, &read.observation))
                .collect::<Vec<_>>()
        });
    }
    let sources: Vec<String> = phase("fs.text", reps, || {
        texts
            .iter()
            .map(|path| msbuild_observed::host_fs::read_to_string(path).expect("still readable"))
            .collect()
    });
    phase("xml.parse", reps, || {
        sources
            .iter()
            .map(|text| roxmltree::Document::parse(text).map(|d| d.descendants().count()))
            .filter_map(Result::ok)
            .sum::<usize>()
    });
    phase("digest", reps, || {
        sources
            .iter()
            .map(|t| TextDigest::of(t))
            .collect::<Vec<_>>()
    });
    phase("fs.other", reps, || {
        others
            .iter()
            .map(|read| msbuild_observed::answer_now(&read.path, &read.observation))
            .collect::<Vec<_>>()
    });

    if std::env::var("EVAL_COUNTS_MSBUILD").as_deref() != Ok("0") {
        msbuild_rows(&project, &parsed, &env, &extras, reps);
    }
}
