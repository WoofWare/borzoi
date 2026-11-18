//! Generative differential: how the walk reads **path spellings** — of the
//! project's own path, of its imports (plain, behind a condition the walk
//! cannot decide, and wildcard) and of an SDK's root — against MSBuild.
//!
//! MSBuild takes every path it loads as its full path (`Path.GetFullPath`:
//! `.` dropped, runs of `/` collapsed, `..` resolved lexically, whatever the
//! segment before it links to), and on Unix reads a `\` as `/`: the attribute
//! text of an `<Import>` before it expands it, the path of a file it loads
//! (a project, a wildcard's match) when it loads it. Whether a `\` is read
//! before or after a `..` resolves even differs between the in-process API
//! and `dotnet msbuild`. Each route has had its own bug, found one review
//! round at a time; this harness draws the routes together over one
//! adversarial alphabet:
//!
//! - project paths: `//`, `/./`, `dir/../dir`, a `..` through a directory
//!   link (which the file system resolves elsewhere), a `\`, a `\` before a
//!   `..`, a NUL, a trailing separator;
//! - imports: the same spellings, a written `\`, an escaped `%5C`, an escaped
//!   NUL, a trailing separator, and wildcards whose matches include literal
//!   backslash names (with and without the file the rewrite names);
//! - gates: none, an undecidable `Condition` on the import, and the same on
//!   an `<ImportGroup>`;
//! - SDK roots with and without a `\` (imports relative to the root, and an
//!   absolute one, which `Path.Combine` takes over the root).
//!
//! Graded against `ProjectInstance` (the oracle's `evaluated` op) under:
//!
//! - **certain-implies-exact**: a property the walk commits (a value, or an
//!   exact "unset") is MSBuild's;
//! - **rejection**: where MSBuild rejects the project, the walk commits
//!   nothing and records a (possible or certain) rejection; where MSBuild
//!   evaluates it, the walk claims no certain rejection;
//! - **must commit**: a case whose every spelling the walk models commits
//!   the body's last write, so declining is not free;
//!
//! and, for a case holding a `\` that the walk commits anything for, against
//! `dotnet msbuild` too, which reads the backslash at a different point.
//! A project path the walk refuses ([`ProjectFile::read`]) makes no claim.
//! The census printed at the end counts each verdict by route.

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use borzoi_msbuild::observed::{Observer, host_fs};
use borzoi_msbuild::test_support::{PropertyRead, ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{ProjectFile, RejectionCertainty, SdkPaths, SdkResolution, SdkResolveError};
use common::{Oracle, SplitMix64};

// ---------------------------------------------------------------------------
// The case space.
// ---------------------------------------------------------------------------

/// How the project's own path is spelt. Relative to `<case>`, whose project
/// directory is `proj`.
const PROJECT_SPELLINGS: &[(&str, &str)] = &[
    ("plain", "proj/Demo.fsproj"),
    ("doubled", "proj//Demo.fsproj"),
    ("curdir", "proj/./Demo.fsproj"),
    ("dotdot", "proj/x/../Demo.fsproj"),
    // `far` links to `<case>/decoy/x/y`: the file system reads
    // `<case>/decoy/proj/Demo.fsproj`, which does not exist.
    ("link-dotdot", "proj/far/../../proj/Demo.fsproj"),
    ("backslash", "proj\\Demo.fsproj"),
    ("backslash-dotdot", "proj/a\\b/../Demo.fsproj"),
    ("nul", "proj/Demo\0.fsproj"),
    ("trailing", "proj/Demo.fsproj/"),
];

/// The project spellings the walk models, which must commit.
const CLEAN_PROJECT: &[&str] = &["plain", "doubled", "curdir", "dotdot", "link-dotdot"];

/// An import's `Project`, relative to the project directory unless rooted.
/// `{dir}` stands for the project directory's full path.
const IMPORTS: &[(&str, &str)] = &[
    ("plain", "sub/i.props"),
    ("doubled", "sub//i.props"),
    ("curdir", "./sub/i.props"),
    ("dotdot", "x/../sub/i.props"),
    ("link-dotdot", "far/../../proj/sub/i.props"),
    ("rooted-doubled", "$(MSBuildProjectDirectory)//sub/i.props"),
    ("rooted-literal", "{dir}/x/../sub/i.props"),
    ("written-backslash", "sub\\i.props"),
    ("escaped-backslash", "sub%5Ci.props"),
    ("backslash-missing", "q\\r.props"),
    ("escaped-backslash-missing", "q%5Cr.props"),
    ("glob-backslash-name", "q*.props"),
    ("glob-backslash-name-rewrite-exists", "both*.props"),
    ("glob", "sub/*.props"),
    ("glob-nothing", "missing*.props"),
    ("trailing", "sub/i.props/"),
    ("escaped-nul", "sub/i%00.props"),
];

/// The imports the walk models, which must commit when ungated.
const CLEAN_IMPORTS: &[&str] = &[
    "plain",
    "doubled",
    "curdir",
    "dotdot",
    "link-dotdot",
    "rooted-doubled",
    "rooted-literal",
    "written-backslash",
    "glob",
    "glob-nothing",
];

/// An SDK import's `Project`: root-relative, or the absolute path of
/// `<case>/abs.props` (`{case}`), which `Path.Combine` takes over the root.
const SDK_IMPORTS: &[(&str, &str)] = &[
    ("sdk-relative", "known.props"),
    ("sdk-dotdot", "../Sdk/known.props"),
    ("sdk-absolute", "{case}/abs.props"),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Gate {
    None,
    /// An undecidable `Condition` on the `<Import>`, true in MSBuild.
    Undecided,
    /// The same on an `<ImportGroup>` around it.
    UndecidedGroup,
}

/// The condition the walk cannot decide and MSBuild takes.
const UNDECIDED: &str = "$([System.String]::IsNullOrWhiteSpace(''))";

#[derive(Debug, Clone)]
enum Import {
    Plain(usize),
    Sdk(usize),
}

#[derive(Debug, Clone)]
struct Case {
    project: usize,
    imports: Vec<(Import, Gate)>,
    /// The SDK directory holds a `\`.
    backslash_sdk: bool,
}

impl Case {
    fn generate(rng: &mut SplitMix64) -> Case {
        // Half the cases spell the project plainly, so the import routes are
        // graded without a refusal in front of them.
        let project = if rng.below(2) == 0 {
            0
        } else {
            rng.below(PROJECT_SPELLINGS.len())
        };
        let imports = (0..1 + rng.below(2))
            .map(|_| {
                let import = if rng.below(4) == 0 {
                    Import::Sdk(rng.below(SDK_IMPORTS.len()))
                } else {
                    Import::Plain(rng.below(IMPORTS.len()))
                };
                let gate = *rng.pick(&[
                    Gate::None,
                    Gate::None,
                    Gate::Undecided,
                    Gate::UndecidedGroup,
                ]);
                (import, gate)
            })
            .collect();
        Case {
            project,
            imports,
            backslash_sdk: rng.below(2) == 0,
        }
    }

    fn project_class(&self) -> &'static str {
        PROJECT_SPELLINGS[self.project].0
    }

    fn import_class(&self, import: &Import) -> &'static str {
        match import {
            Import::Plain(i) => IMPORTS[*i].0,
            Import::Sdk(i) => SDK_IMPORTS[*i].0,
        }
    }

    /// Whether every spelling in the case is one the walk models, so it must
    /// commit the body's last write. An SDK import is modelled when the root
    /// holds no `\`, or when the import is absolute and so takes no part of
    /// the root.
    fn must_commit(&self) -> bool {
        CLEAN_PROJECT.contains(&self.project_class())
            && self.imports.iter().all(|(import, gate)| {
                *gate == Gate::None
                    && match import {
                        Import::Plain(i) => CLEAN_IMPORTS.contains(&IMPORTS[*i].0),
                        Import::Sdk(i) => {
                            !self.backslash_sdk || SDK_IMPORTS[*i].0 == "sdk-absolute"
                        }
                    }
            })
    }

    /// Whether a `\` appears in a path MSBuild loads: the project's, or the
    /// SDK root's under an SDK import.
    fn holds_backslash(&self) -> bool {
        PROJECT_SPELLINGS[self.project].1.contains('\\')
            || (self.backslash_sdk
                && self
                    .imports
                    .iter()
                    .any(|(import, _)| matches!(import, Import::Sdk(_))))
    }

    fn xml(&self, case_dir: &Path) -> String {
        let dir = case_dir.join("proj");
        let mut xml = String::from(
            "<Project>\n  <PropertyGroup>\n    <ProjFull>$(MSBuildProjectFullPath)</ProjFull>\n  \
             </PropertyGroup>\n",
        );
        for (import, gate) in &self.imports {
            let (attribute, sdk) = match import {
                Import::Plain(i) => (
                    IMPORTS[*i].1.replace("{dir}", &dir.to_string_lossy()),
                    String::new(),
                ),
                Import::Sdk(i) => (
                    SDK_IMPORTS[*i]
                        .1
                        .replace("{case}", &case_dir.to_string_lossy()),
                    " Sdk=\"S\"".to_string(),
                ),
            };
            let attribute = attribute.replace('&', "&amp;").replace('"', "&quot;");
            let element =
                |condition: &str| format!("<Import{sdk} Project=\"{attribute}\"{condition} />");
            match gate {
                Gate::None => xml.push_str(&format!("  {}\n", element(""))),
                Gate::Undecided => xml.push_str(&format!(
                    "  {}\n",
                    element(&format!(" Condition=\"{UNDECIDED}\""))
                )),
                Gate::UndecidedGroup => xml.push_str(&format!(
                    "  <ImportGroup Condition=\"{UNDECIDED}\">\n    {}\n  </ImportGroup>\n",
                    element("")
                )),
            }
        }
        xml.push_str(
            "  <PropertyGroup>\n    <After>committed</After>\n  </PropertyGroup>\n</Project>\n",
        );
        xml
    }
}

/// The properties every case reads back.
const PROPERTIES: [&str; 4] = ["Trace", "Last", "After", "ProjFull"];

/// An imported file: appends `marker` to `Trace` and names itself in `Last`.
fn imported(marker: &str) -> String {
    format!(
        "<Project>\n  <PropertyGroup>\n    <Trace>$(Trace);{marker}</Trace>\n    \
         <Last>$(MSBuildThisFileFullPath)</Last>\n  </PropertyGroup>\n</Project>\n"
    )
}

// ---------------------------------------------------------------------------
// The layout and the two oracles.
// ---------------------------------------------------------------------------

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// The shared root: one SDK directory without a `\` and one with, each
/// holding the SDK `S`, and an oracle resolving SDKs from each.
struct Shared {
    root: PathBuf,
    plain: Oracle,
    backslash: Oracle,
}

impl Shared {
    fn new() -> Shared {
        let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
            "path-spelling-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&root).expect("mkdir root");
        let root = host_fs::canonicalize(&root).expect("canonicalize root");
        // `Sd/ks` is what the backslash directory's name reads as once
        // MSBuild reads its `\` as `/`: an SDK there too, whose file marks
        // itself apart, lets MSBuild load the SDK whichever way it reads the
        // root, and tells which way it did.
        for (sdks, marker) in [
            ("Sdks", "sdk-known"),
            ("Sd\\ks", "sdk-known-backslash"),
            ("Sd/ks", "sdk-known-rewrite"),
        ] {
            let sdk = root.join(sdks).join("S/Sdk");
            std::fs::create_dir_all(&sdk).expect("mkdir sdk");
            std::fs::write(sdk.join("known.props"), imported(marker)).expect("write");
            std::fs::write(sdk.join("Sdk.props"), "<Project />").expect("write");
            std::fs::write(sdk.join("Sdk.targets"), "<Project />").expect("write");
        }
        let plain = Oracle::spawn_with_sdks_path(&root.join("Sdks"));
        let backslash = Oracle::spawn_with_sdks_path(&root.join("Sd\\ks"));
        Shared {
            root,
            plain,
            backslash,
        }
    }

    fn sdks(&self, case: &Case) -> PathBuf {
        self.root
            .join(if case.backslash_sdk { "Sd\\ks" } else { "Sdks" })
    }
}

impl Drop for Shared {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

/// Lay out one case's directory.
fn lay_out(case_dir: &Path, xml: &str) {
    let proj = case_dir.join("proj");
    for dir in ["sub", "x", "both", "a\\b", "a"] {
        std::fs::create_dir_all(proj.join(dir)).expect("mkdir");
    }
    std::fs::create_dir_all(case_dir.join("decoy/x/y")).expect("mkdir decoy");
    std::os::unix::fs::symlink("../decoy/x/y", proj.join("far")).expect("symlink");
    std::fs::write(proj.join("Demo.fsproj"), xml).expect("write project");
    // What `dotnet msbuild` loads for `proj/a\b/../Demo.fsproj`.
    std::fs::write(proj.join("a/Demo.fsproj"), "<Project />").expect("write");
    for (name, marker) in [
        ("sub/i.props", "sub-i"),
        ("q\\r.props", "literal-q-r"),
        ("both/r.props", "both-r"),
        ("both\\r.props", "literal-both-r"),
    ] {
        std::fs::write(proj.join(name), imported(marker)).expect("write import");
    }
    std::fs::write(case_dir.join("abs.props"), imported("abs")).expect("write");
    // What the file system reaches for `proj/far/../../proj/sub/i.props`.
    std::fs::create_dir_all(case_dir.join("decoy/proj/sub")).expect("mkdir");
    std::fs::write(case_dir.join("decoy/proj/sub/i.props"), imported("decoy")).expect("write");
}

// ---------------------------------------------------------------------------
// Grading.
// ---------------------------------------------------------------------------

#[derive(Debug, Default)]
struct Outcome {
    refused: bool,
    msbuild_rejected: bool,
    committed: usize,
    findings: Vec<String>,
}

fn evaluate(shared: &mut Shared, case: &Case) -> Outcome {
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let case_dir = shared.root.join(format!("case{n}"));
    let xml = case.xml(&case_dir);
    lay_out(&case_dir, &xml);
    let spelt = case_dir.join(PROJECT_SPELLINGS[case.project].1);
    let mut outcome = Outcome::default();
    let describe = format!("{case:?}\n--- at {}\n{xml}", spelt.display());

    let sdks = shared.sdks(case);
    let sdk_root = sdks.join("S/Sdk");
    let resolver = move |name: &str, _: &Observer| {
        if name == "S" {
            Ok(SdkResolution::Single(SdkPaths {
                root: sdk_root.clone(),
                props: sdk_root.join("Sdk.props"),
                targets: sdk_root.join("Sdk.targets"),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let mut environment = common::oracle_environment();
    environment.insert(
        "MSBuildSDKsPath".to_string(),
        sdks.to_string_lossy().into_owned(),
    );

    let project = match ProjectFile::read(&spelt, &Observer::new()) {
        Ok(project) => project,
        Err(_) => {
            outcome.refused = true;
            let _ = std::fs::remove_dir_all(&case_dir);
            return outcome;
        }
    };
    let probe = ReadProbe {
        properties: PROPERTIES.iter().map(|p| (*p).to_owned()).collect(),
        ..ReadProbe::default()
    };
    let (parsed, ours) = parse_fsproj_reads(
        &project,
        &HashMap::new(),
        &environment,
        Some(&resolver),
        None,
        None,
        &probe,
    )
    .expect("well-formed XML parses");
    let committed: Vec<(&str, Option<String>)> = PROPERTIES
        .iter()
        .filter_map(|name| match &ours.properties[*name] {
            PropertyRead::Value(v) => Some((*name, Some(v.to_string()))),
            PropertyRead::Unset => Some((*name, None)),
            _ => None,
        })
        .collect();
    outcome.committed = committed.len();

    let oracle = if case.backslash_sdk {
        &mut shared.backslash
    } else {
        &mut shared.plain
    };
    let theirs = oracle.try_evaluated(&spelt, &[], &PROPERTIES, &[], &[]);
    match &theirs {
        None => {
            outcome.msbuild_rejected = true;
            if !committed.is_empty() {
                outcome.findings.push(format!(
                    "MSBuild rejects the project; we commit {committed:?}"
                ));
            }
            if parsed.rejection.is_none() {
                outcome
                    .findings
                    .push("MSBuild rejects the project; we record no rejection".to_string());
            }
        }
        Some(theirs) => {
            if parsed.rejection.as_ref().map(|r| r.certainty) == Some(RejectionCertainty::Certain) {
                outcome.findings.push(format!(
                    "MSBuild evaluates the project; we claim it rejects it: {:?}",
                    parsed.rejection
                ));
            }
            for (name, ours) in &committed {
                let theirs = theirs["properties"][*name].as_str();
                if theirs != ours.as_deref() {
                    outcome.findings.push(format!(
                        "${name}: we commit {ours:?}, MSBuild has {theirs:?}"
                    ));
                }
            }
            if case.must_commit() && !committed.iter().any(|(name, _)| *name == "After") {
                outcome.findings.push(format!(
                    "a modelled case did not commit After: {:?} (diagnostics {:?})",
                    ours.properties["After"], parsed.diagnostics
                ));
            }
        }
    }
    // `dotnet msbuild` reads a `\` at another point than the in-process API,
    // so where one reaches a path MSBuild loads, what we commit must be the
    // command line's too.
    if case.holds_backslash() && !committed.is_empty() {
        match cli_properties(&spelt, &sdks) {
            None => outcome.findings.push(format!(
                "dotnet msbuild rejects the project; we commit {committed:?}"
            )),
            Some(cli) => {
                for (name, ours) in &committed {
                    let theirs = cli.get(*name).map(String::as_str).filter(|v| !v.is_empty());
                    if theirs != ours.as_deref().filter(|v| !v.is_empty()) {
                        outcome.findings.push(format!(
                            "${name}: we commit {ours:?}, dotnet msbuild has {theirs:?}"
                        ));
                    }
                }
            }
        }
    }
    if !outcome.findings.is_empty() {
        outcome.findings.push(describe);
    }
    let _ = std::fs::remove_dir_all(&case_dir);
    outcome
}

/// `dotnet msbuild -getProperty` of [`PROPERTIES`] on `project`, with
/// `MSBuildSDKsPath` at `sdks`, or `None` when it fails.
fn cli_properties(project: &Path, sdks: &Path) -> Option<HashMap<String, String>> {
    let mut cmd = std::process::Command::new("dotnet");
    cmd.args(["msbuild", "-nologo"]);
    for name in PROPERTIES {
        cmd.arg(format!("-getProperty:{name}"));
    }
    cmd.arg(project);
    common::scrub_oracle_env(&mut cmd);
    cmd.env("MSBuildSDKsPath", sdks);
    let out = borzoi_oracle_harness::BoundedCommand::new(cmd)
        .timeout(borzoi_oracle_harness::default_timeout())
        .run()
        .expect("dotnet msbuild runs to completion");
    if !out.status.success() {
        return None;
    }
    let json: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("dotnet msbuild prints JSON for several names");
    Some(
        json["Properties"]
            .as_object()
            .expect("a Properties object")
            .iter()
            .map(|(k, v)| (k.clone(), v.as_str().unwrap_or_default().to_string()))
            .collect(),
    )
}

// ---------------------------------------------------------------------------
// The sweep.
// ---------------------------------------------------------------------------

#[derive(Debug, Default)]
struct Census {
    /// (route, verdict) → cases.
    counts: BTreeMap<(String, &'static str), usize>,
    findings: Vec<Vec<String>>,
    must_commit: usize,
}

fn sweep(seed: u64, cases: usize) -> Census {
    let mut shared = Shared::new();
    let mut rng = SplitMix64(seed);
    let mut census = Census::default();
    for _ in 0..cases {
        let case = Case::generate(&mut rng);
        let outcome = evaluate(&mut shared, &case);
        let verdict = if outcome.refused {
            "refused"
        } else if outcome.msbuild_rejected {
            "msbuild rejects"
        } else if outcome.committed > 0 {
            "committed"
        } else {
            "declined"
        };
        census.must_commit += usize::from(case.must_commit());
        let mut routes = vec![format!("project {}", case.project_class())];
        for (import, gate) in &case.imports {
            routes.push(format!(
                "import {} {gate:?}{}",
                case.import_class(import),
                if matches!(import, Import::Sdk(_)) && case.backslash_sdk {
                    " (backslash root)"
                } else {
                    ""
                }
            ));
        }
        for route in routes {
            *census.counts.entry((route, verdict)).or_default() += 1;
        }
        if !outcome.findings.is_empty() {
            census.findings.push(outcome.findings);
        }
    }
    let mut last = String::new();
    for ((route, verdict), n) in &census.counts {
        if *route != last {
            eprintln!("{route}");
            last.clone_from(route);
        }
        eprintln!("    {verdict}: {n}");
    }
    census
}

fn assert_clean(census: &Census) {
    assert!(
        census.findings.is_empty(),
        "{} cases diverge:\n{}\nthe first three in full:\n{}",
        census.findings.len(),
        census
            .findings
            .iter()
            .map(|f| format!(
                "{} -- {}",
                f[0],
                f[f.len() - 1].lines().next().unwrap_or_default()
            ))
            .collect::<Vec<_>>()
            .join("\n"),
        census
            .findings
            .iter()
            .take(3)
            .map(|f| f.join("\n"))
            .collect::<Vec<_>>()
            .join("\n=====\n")
    );
}

#[test]
fn path_spellings_are_read_as_msbuild_reads_them() {
    let census = sweep(0x5be1_1ed0_9a7c, 300);
    assert_clean(&census);
    assert!(
        census.must_commit >= 30,
        "only {} must-commit cases",
        census.must_commit
    );
}

#[test]
#[ignore = "soak: fresh seed, BORZOI_MSBUILD_SOAK_SEED / _CASES"]
fn soak() {
    let (seed, cases) = common::soak_parameters("path_spelling", 1500);
    assert_clean(&sweep(seed, cases));
}
