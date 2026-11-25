//! Differential: how `<Import Sdk="X" Project="P"/>` resolves `P`, against
//! real `dotnet msbuild`.
//!
//! MSBuild imports `Path.Combine(sdkResult.Path, P)` of `P` as written, then
//! expands and normalises it (`FileUtilities.NormalizePath`, Evaluator.cs). So
//! `P` may climb out of the SDK directory with `..` — the Web SDK's
//! `Sdk.Server.targets` imports `Microsoft.NET.Sdk.Web.ProjectSystem`'s
//! `..\targets\Microsoft.NET.Sdk.Web.BeforeCommon.targets` — and a `P` written
//! absolute names its own file, while one a property makes absolute is
//! appended to the SDK directory.
//!
//! The SDK here is a temp directory MSBuild's default resolver finds through
//! `MSBuildSDKsPath`. It holds marker files inside the SDK's `Sdk/` directory,
//! in its sibling `targets/`, in another SDK, and outside every SDK; each
//! appends its own name to `Seen`. A generated project imports respellings of
//! those files — `.` and `ghost/..` segments, either separator, doubled
//! separators, `%2e` escapes, absolute forms — with repeats, so MSBuild's
//! duplicate-import skip is graded alongside resolution. One `dotnet msbuild
//! -getProperty:Seen` grades a whole project; we must commit (no diagnostic)
//! and agree exactly.
//!
//! Each generator runs the same spellings through a plain `<Import Project="P"/>`
//! too, from a project in the SDK's directory: MSBuild normalises that path
//! the same way, and the walk opens what it names.
//!
//! Runs under `nix develop` like the sibling `dotnet msbuild` differentials.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

mod common;

use crate::common::parse_fsproj_with_imports;
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::{SdkPaths, SdkResolution, SdkResolveError};
use borzoi_oracle_harness::BoundedCommand;
use common::SplitMix64;

const MSBUILD_TIMEOUT: Duration = Duration::from_secs(600);

/// Marker files, each as the path components that reach it from the SDK's
/// `Sdk/` directory (`sdks/MySdk/Sdk`).
const TARGETS: &[(&str, &[&str])] = &[
    ("E", &["E.props"]),
    ("S", &["sub", "S.props"]),
    ("D", &["sub", "deeper", "D.props"]),
    ("T", &["..", "targets", "T.props"]),
    ("O", &["..", "..", "Other", "Sdk", "O.props"]),
    ("X", &["..", "..", "..", "outside", "X.props"]),
];

/// Every relative first segment [`respell_with_tail`] writes, as text.
const FIRST_SEGMENTS: &[&str] = &[
    "E.props", "sub", "ghost", "%2e", "%2e%2e", "%00", "a;b", "*", " x", "%3b", "%C3%A9", "x?",
];

/// Whether MSBuild's Unix path adjustment rewrites every `\` of `expanded`
/// whatever its working directory: the domain the walk must commit in, as
/// `FileUtilities.LooksLikeUnixFilePath` states it. The first segment of the
/// rewrite (`\` to `/`, slash runs collapsed, one pair of enclosing quotes
/// dropped) is `.` or `..`, or an absolute directory that exists; a lone
/// absolute segment must exist at all.
fn adjustment_certainly_converts(expanded: &str) -> bool {
    if expanded.starts_with("$(") || expanded.starts_with("@(") || expanded.starts_with(r"\\") {
        return false;
    }
    let mut converted = String::new();
    for c in expanded.chars() {
        let c = if c == '\\' { '/' } else { c };
        if !(c == '/' && converted.ends_with('/')) {
            converted.push(c);
        }
    }
    let quoted = converted.len() > 2
        && (converted.starts_with('\'') && converted.ends_with('\'')
            || converted.starts_with('"') && converted.ends_with('"'));
    let unquoted = if quoted {
        &converted[1..converted.len() - 1]
    } else {
        converted.as_str()
    };
    match unquoted[1..].find('/') {
        Some(at) => {
            let first = &unquoted[..at + 1];
            matches!(first, "." | "..")
                || (first.starts_with('/') && host_fs::metadata(first).is_ok_and(|m| m.is_dir()))
        }
        None => unquoted.starts_with('/') && host_fs::metadata(unquoted).is_ok(),
    }
}

/// Whether every spelling MSBuild's Unix path adjustments can leave of
/// `expanded` (one plain import path, escaped) opens one file under one
/// duplicate-import key, whatever each adjustment decided: the other half of
/// the domain the walk must commit in. MSBuild collapses `..` over `/` alone
/// before it turns a kept `\` into `/`, and keys the import by that spelling,
/// so this holds when no `\` touches a separator or an end (an adjustment then
/// only turns some `\` into `/`) and no `.` or `..` component follows the
/// start of the first `/`-segment holding a `\`. A wildcard globs the path,
/// which is another question.
fn adjustment_immaterial(expanded: &str) -> bool {
    if expanded.contains(['*', '?']) {
        return false;
    }
    let decoded = borzoi_msbuild::test_support::unescape(expanded);
    let chars: Vec<char> = decoded.chars().collect();
    let is_separator = |c: Option<&char>| matches!(c, Some('/' | '\\') | None);
    let flanked = (0..chars.len())
        .filter(|&i| chars[i] == '\\')
        .all(|i| i > 0 && !is_separator(chars.get(i - 1)) && !is_separator(chars.get(i + 1)));
    let Some(first) = decoded.find('\\') else {
        return true;
    };
    let from = decoded[..first].rfind('/').map_or(0, |at| at + 1);
    flanked
        && decoded[from..]
            .split(['/', '\\'])
            .all(|c| c != "." && c != "..")
}

/// Imports per generated project.
const IMPORTS_PER_PROJECT: usize = 30;

struct Layout {
    _dir: tempfile::TempDir,
    /// Canonical temp root, so absolute spellings agree with what both
    /// evaluators see (macOS's `/var` → `/private/var`).
    root: PathBuf,
    /// Where the SDKs live: `<root>/sdks`, or below a further directory.
    sdks: PathBuf,
}

impl Layout {
    /// A working directory holding nothing.
    fn empty_cwd(&self) -> PathBuf {
        let dir = self.root.join("cwd-empty");
        std::fs::create_dir_all(&dir).expect("mkdir empty cwd");
        dir
    }

    /// A working directory holding a directory for every relative first
    /// segment a generated spelling can start with, spelt as MSBuild probes
    /// it (the escaped text).
    fn full_cwd(&self) -> PathBuf {
        let dir = self.root.join("cwd-full");
        for name in FIRST_SEGMENTS {
            std::fs::create_dir_all(dir.join(name)).expect("mkdir first segment");
        }
        dir
    }

    fn sdks(&self) -> PathBuf {
        self.sdks.clone()
    }

    fn sdk_root(&self) -> PathBuf {
        self.sdks().join("MySdk").join("Sdk")
    }

    fn new() -> Layout {
        Layout::under("")
    }

    /// The SDKs below `<root>/<parent>`.
    fn under(parent: &str) -> Layout {
        let dir = tempfile::TempDir::new().expect("tempdir");
        let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path())
            .expect("canonicalise tempdir");
        let sdks = root.join(parent).join("sdks");
        let layout = Layout {
            _dir: dir,
            root,
            sdks,
        };
        let sdk_root = layout.sdk_root();
        std::fs::create_dir_all(&sdk_root).expect("mkdir sdk");
        for name in ["Sdk.props", "Sdk.targets"] {
            std::fs::write(sdk_root.join(name), "<Project/>").expect("write sdk entry");
        }
        for (marker, components) in TARGETS {
            let path = normalise(&components.iter().fold(sdk_root.clone(), |p, c| p.join(c)));
            std::fs::create_dir_all(path.parent().unwrap()).expect("mkdir marker dir");
            std::fs::write(
                &path,
                format!(
                    "<Project><PropertyGroup><Seen>$(Seen);{marker}</Seen></PropertyGroup></Project>"
                ),
            )
            .expect("write marker");
        }
        layout
    }
}

/// Lexical `.`/`..` collapse — what `Path.GetFullPath` does.
fn normalise(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

/// One spelling of `components` (relative to the SDK root), or of the
/// target's absolute path. `escaped_separators` admits `%2f`/`%5c`, which the
/// evaluator declines: MSBuild decodes them after deciding what is a
/// separator.
fn respell(
    rng: &mut SplitMix64,
    layout: &Layout,
    components: &[&str],
    escaped_separators: bool,
) -> String {
    let separators: &[&str] = if escaped_separators {
        &["/", "\\", "//", "/\\", "%2f", "%5c"]
    } else {
        &["/", "\\", "//", "/\\"]
    };
    let separator = |rng: &mut SplitMix64| -> &'static str { rng.pick(separators) };
    let mut parts: Vec<String> = Vec::new();
    let absolute = rng.below(6) == 0;
    let segments: Vec<String> = if absolute {
        let full = normalise(&components.iter().fold(layout.sdk_root(), |p, c| p.join(c)));
        full.components()
            .skip(1) // the root `/`
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect()
    } else {
        if rng.below(4) == 0 {
            parts.push(".".to_string());
        }
        components.iter().map(|c| (*c).to_string()).collect()
    };
    for segment in segments {
        match rng.below(8) {
            0 => parts.push(".".to_string()),
            1 => {
                parts.push("ghost".to_string());
                parts.push("..".to_string());
            }
            2 => parts.push("%2e".to_string()),
            _ => {}
        }
        let segment = if segment == ".." && rng.below(4) == 0 {
            "%2e%2e".to_string()
        } else {
            segment
        };
        parts.push(segment);
    }
    let mut out = String::new();
    if absolute {
        out.push('/');
    }
    for (i, part) in parts.iter().enumerate() {
        if i > 0 {
            out.push_str(separator(rng));
        }
        out.push_str(part);
    }
    out
}

/// The variables both sides see: what `dotnet` needs, plus `MSBuildSDKsPath`.
fn child_environment(layout: &Layout) -> HashMap<String, String> {
    let mut env: HashMap<String, String> = std::env::vars()
        .filter(|(key, _)| {
            matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR")
                || key.starts_with("DOTNET_")
                || key.starts_with("NUGET_")
        })
        .collect();
    env.insert(
        "MSBuildSDKsPath".to_string(),
        layout.sdks().to_string_lossy().into_owned(),
    );
    env
}

/// MSBuild's `Seen`, or its output when the evaluation fails.
fn msbuild_seen(proj: &Path, env: &HashMap<String, String>) -> Result<String, String> {
    msbuild_seen_from(proj, env, proj.parent().unwrap())
}

/// [`msbuild_seen`], with `dotnet msbuild` run from `cwd`.
fn msbuild_seen_from(
    proj: &Path,
    env: &HashMap<String, String>,
    cwd: &Path,
) -> Result<String, String> {
    let mut cmd = Command::new("dotnet");
    cmd.current_dir(cwd);
    cmd.env_clear();
    cmd.envs(env);
    cmd.args(["msbuild", "-nologo", "-getProperty:Seen"]);
    cmd.arg(proj);
    let out = BoundedCommand::new(cmd)
        .timeout(MSBUILD_TIMEOUT)
        .run()
        .unwrap_or_else(|e| panic!("dotnet msbuild for {}: {e:?}", proj.display()));
    let stdout = String::from_utf8(out.stdout).expect("msbuild stdout is UTF-8");
    if out.status.success() {
        Ok(stdout.trim().to_string())
    } else {
        Err(format!("{stdout}{}", String::from_utf8_lossy(&out.stderr)))
    }
}

/// How a generated project imports a spelling.
#[derive(Clone, Copy, Debug)]
enum Kind {
    /// `<Import Sdk="MySdk" Project="…"/>`, from `<root>/proj/p.proj`.
    Sdk,
    /// `<Import Project="…"/>`, from a project in the SDK's `Sdk/`
    /// directory, so that a relative spelling names the same file.
    Plain,
}

const KINDS: [Kind; 2] = [Kind::Sdk, Kind::Plain];

/// Write a project importing each of `imports` as `kind` says, and evaluate
/// it both ways.
fn evaluate_both(
    layout: &Layout,
    kind: Kind,
    imports: &[String],
) -> (
    String,
    borzoi_msbuild::ParsedProject,
    Result<String, String>,
) {
    evaluate_both_after(layout, kind, "", imports)
}

/// [`evaluate_both`], with `prelude` (property groups the imports read)
/// written before the imports.
fn evaluate_both_after(
    layout: &Layout,
    kind: Kind,
    prelude: &str,
    imports: &[String],
) -> (
    String,
    borzoi_msbuild::ParsedProject,
    Result<String, String>,
) {
    let body: String = imports
        .iter()
        .map(|p| match kind {
            Kind::Sdk => format!("  <Import Sdk=\"MySdk\" Project=\"{p}\" />\n"),
            Kind::Plain => format!("  <Import Project=\"{p}\" />\n"),
        })
        .collect();
    let xml = format!("<Project>\n{prelude}{body}</Project>\n");
    let proj_dir = match kind {
        Kind::Sdk => layout.root.join("proj"),
        Kind::Plain => layout.sdk_root(),
    };
    std::fs::create_dir_all(&proj_dir).expect("mkdir proj");
    let proj = proj_dir.join("p.proj");
    std::fs::write(&proj, &xml).expect("write project");

    let env = child_environment(layout);
    let sdk_root = layout.sdk_root();
    let resolver = |name: &str,
                    _observer: &borzoi_msbuild::observed::Observer|
     -> Result<SdkResolution, SdkResolveError> {
        if name == "MySdk" {
            Ok(SdkResolution::Single(SdkPaths {
                root: sdk_root.clone(),
                props: sdk_root.join("Sdk.props"),
                targets: sdk_root.join("Sdk.targets"),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &env,
        Some(&resolver),
        None,
    )
    .unwrap_or_else(|e| panic!("our parse: {e}\n{xml}"));
    let theirs = msbuild_seen(&proj, &env);
    (xml, parsed, theirs)
}

/// Where we commit, MSBuild evaluates and agrees; where MSBuild fails, we
/// decline. With `must_commit` (an input inside the modelled domain), we must
/// also commit wherever MSBuild evaluates. Returns whether MSBuild evaluated.
fn assert_certain_implies_exact(
    label: &str,
    xml: &str,
    parsed: &borzoi_msbuild::ParsedProject,
    theirs: Result<String, String>,
    must_commit: bool,
) -> bool {
    match theirs {
        Ok(_) if !must_commit && !parsed.diagnostics.is_empty() => true,
        Ok(theirs) => {
            assert!(
                parsed.diagnostics.is_empty(),
                "{label}: we declined where MSBuild evaluates cleanly:\n{xml}\n{:#?}",
                parsed.diagnostics
            );
            let ours = parsed.properties.get("Seen").cloned().unwrap_or_default();
            assert_eq!(ours, theirs, "{label}: Seen differs for\n{xml}");
            true
        }
        Err(output) => {
            assert!(
                !parsed.diagnostics.is_empty(),
                "{label}: MSBuild fails but we committed {:?}:\n{xml}\n{output}",
                parsed.properties.get("Seen")
            );
            false
        }
    }
}

fn check_seed(seed: u64, kind: Kind) {
    let layout = Layout::new();
    let mut rng = SplitMix64(seed);
    let imports: Vec<String> = (0..IMPORTS_PER_PROJECT)
        .map(|_| {
            let (_, components) = rng.pick(TARGETS);
            respell(&mut rng, &layout, components, false)
        })
        .collect();
    let (xml, parsed, theirs) = evaluate_both(&layout, kind, &imports);
    let label = format!("{kind:?} seed {seed}");
    assert!(
        theirs.is_ok(),
        "{label}: every spelling names a file, yet MSBuild failed:\n{xml}\n{theirs:?}"
    );
    assert_certain_implies_exact(&label, &xml, &parsed, theirs, true);
}

#[test]
fn sdk_import_project_paths_resolve_as_msbuild_does() {
    for kind in KINDS {
        for seed in 0..4 {
            check_seed(seed, kind);
        }
    }
}

#[test]
#[ignore = "soak: fresh seed, BORZOI_MSBUILD_SOAK_SEED / _CASES"]
fn sdk_import_project_paths_soak() {
    let (seed, cases) = common::soak_parameters("sdk_import_project_paths", 20);
    for kind in KINDS {
        for case in 0..cases as u64 {
            check_seed(seed.wrapping_add(case), kind);
        }
    }
}

/// A respelling with segments after the file name, and whether it lies in
/// the modelled domain. Some tails collapse lexically (`E.props/.`,
/// `E.props/ghost/..`) and MSBuild imports the file; some leave a trailing
/// separator (`E.props/`, `E.props/./`), name a child of a file
/// (`E.props/ghost`) or the SDK directory (`E.props/..`), and MSBuild fails.
/// Outside the domain: escaped separators, and a junk segment the `..` after
/// it erases — MSBuild acts on what it holds (splits the list, rejects the
/// NUL, globs), so collapsing it away would commit to the wrong file.
fn respell_with_tail(rng: &mut SplitMix64, layout: &Layout) -> (String, bool) {
    let (_, components) = rng.pick(TARGETS);
    let escaped_separators = rng.below(4) == 0;
    let mut out = respell(rng, layout, components, escaped_separators);
    let junk = rng.below(3) == 0;
    if junk {
        let junk = rng.pick(&["%00", "a;b", "*", " x", "%3b", "%C3%A9", "x?"]);
        out = format!("{junk}/../{out}");
    }
    for _ in 0..rng.below(3) {
        out.push_str(rng.pick(&["/", "\\"]));
        out.push_str(rng.pick(&[".", "ghost", "..", "%2e", ""]));
    }
    (out, !escaped_separators && !junk)
}

/// One import per project: an import MSBuild fails fails the whole
/// evaluation, so the verdict is per spelling.
fn check_tail_cases(seed: u64, cases: usize, kind: Kind) -> (usize, usize) {
    let layout = Layout::new();
    let mut rng = SplitMix64(seed);
    let (mut imported, mut failed) = (0, 0);
    for case in 0..cases {
        let (import, in_domain) = respell_with_tail(&mut rng, &layout);
        let (xml, parsed, theirs) = evaluate_both(&layout, kind, std::slice::from_ref(&import));
        let label = format!("{kind:?} seed {seed} case {case}");
        if assert_certain_implies_exact(&label, &xml, &parsed, theirs, in_domain) {
            imported += 1;
        } else {
            failed += 1;
        }
    }
    (imported, failed)
}

#[test]
fn sdk_import_project_path_tails_resolve_as_msbuild_does() {
    for kind in KINDS {
        let (imported, failed) = check_tail_cases(0, 16, kind);
        // Both verdicts must occur, or the generator stopped reaching one side.
        assert!(
            imported > 0 && failed > 0,
            "{kind:?}: imported {imported}, failed {failed}"
        );
    }
}

/// Every tail of up to two components on `E.props`, imported alone, both
/// ways: each separator `/` or `\`, each component empty, `.`, `..`, an absent
/// name or an escaped `.`. MSBuild imports the tails that collapse to the
/// file and fails the rest: one ending in a separator names a directory
/// (MSB4019), `/..` names the SDK directory, and an absent name a child of a
/// file. The walk must agree on every host, though macOS's `realpath`
/// resolves `E.props/` to `E.props`; and where MSBuild fails, it must
/// withdraw the evaluation ([`borzoi_msbuild::ParsedProject::rejection`]),
/// not only decline.
#[test]
fn every_short_tail_on_a_file_resolves_as_msbuild_does() {
    let layout = Layout::new();
    let steps: Vec<String> = ["/", "\\"]
        .iter()
        .flat_map(|sep| {
            ["", ".", "..", "ghost", "%2e"]
                .iter()
                .map(move |component| format!("{sep}{component}"))
        })
        .collect();
    let mut tails = vec![String::new()];
    for first in &steps {
        tails.push(first.clone());
        for second in &steps {
            tails.push(format!("{first}{second}"));
        }
    }
    for kind in KINDS {
        let (mut imported, mut failed) = (0, 0);
        for tail in &tails {
            let import = format!("E.props{tail}");
            let (xml, parsed, theirs) = evaluate_both(&layout, kind, std::slice::from_ref(&import));
            let label = format!("{kind:?} {import}");
            if assert_certain_implies_exact(&label, &xml, &parsed, theirs, true) {
                imported += 1;
            } else {
                assert!(
                    parsed.rejection.is_some(),
                    "{label}: MSBuild fails, but the walk withdrew nothing:\n{xml}\n{:#?}",
                    parsed.diagnostics
                );
                failed += 1;
            }
        }
        assert!(
            imported > 0 && failed > 0,
            "{kind:?}: imported {imported}, failed {failed}"
        );
    }
}

/// A respelling (with or without a tail) split at a random point, one side
/// held by the property `P`: `$(P)rest` or `first$(P)`. MSBuild joins the SDK
/// directory to the attribute as written, before expanding it, so a rooted
/// spelling that starts inside `$(P)` is appended to the SDK directory, while
/// one written rooted names its own file.
fn check_property_cases(seed: u64, cases: usize, kind: Kind) -> PropertyTally {
    let layout = Layout::new();
    let mut rng = SplitMix64(seed);
    let mut tally = PropertyTally::default();
    for case in 0..cases {
        let (spelling, in_domain) = respell_with_tail(&mut rng, &layout);
        let boundaries: Vec<usize> = (0..=spelling.len())
            .filter(|at| spelling.is_char_boundary(*at))
            .collect();
        let at = *rng.pick(&boundaries);
        let (first, rest) = spelling.split_at(at);
        let (value, attribute) = if rng.below(2) == 0 {
            (first, format!("$(P){rest}"))
        } else {
            (rest, format!("{first}$(P)"))
        };
        let prelude = format!("  <PropertyGroup><P>{value}</P></PropertyGroup>\n");
        let (xml, parsed, theirs) =
            evaluate_both_after(&layout, kind, &prelude, std::slice::from_ref(&attribute));
        let label = format!("{kind:?} seed {seed} case {case}");
        // A `\` the property supplies to a plain import meets MSBuild's Unix
        // path adjustment, which keeps or rewrites it as the first segment of
        // the expanded path exists under MSBuild's working directory. So
        // MSBuild runs from directories holding none and all of the
        // generator's first segments too: an answer that moves with the
        // directory is one we must decline.
        let (theirs, must_commit) = match kind {
            Kind::Plain if value.contains('\\') => {
                let expanded = attribute.replace('\\', "/").replace("$(P)", value);
                let theirs = msbuild_seen_from_every_cwd(&layout, theirs);
                tally.moved += usize::from(theirs.as_ref().is_err_and(|e| e.contains(MOVES)));
                let must_commit = in_domain
                    && (adjustment_certainly_converts(&expanded)
                        || adjustment_immaterial(&expanded));
                tally.adjusted += usize::from(must_commit && theirs.is_ok());
                (theirs, must_commit)
            }
            _ => (theirs, in_domain),
        };
        if assert_certain_implies_exact(&label, &xml, &parsed, theirs, must_commit) {
            tally.imported += 1;
        } else {
            tally.failed += 1;
        }
    }
    tally
}

/// What [`check_property_cases`] saw.
#[derive(Debug, Default)]
struct PropertyTally {
    /// Cases MSBuild evaluated.
    imported: usize,
    /// Cases MSBuild failed.
    failed: usize,
    /// Plain cases holding a `\` that the walk had to commit and agree on:
    /// MSBuild's adjustment rewrites it, or no spelling it leaves differs.
    adjusted: usize,
    /// Plain cases whose answer moved with MSBuild's working directory.
    moved: usize,
}

/// The mark [`msbuild_seen_from_every_cwd`] puts on an answer that moves.
const MOVES: &str = "MSBuild's answer moves with its working directory";

/// MSBuild's `Seen` for the plain project in `layout`'s SDK directory, given
/// `from_project_dir` (its answer run from there), run again from directories
/// holding none and all of the generator's first segments. Answers that
/// differ are an `Err`, which the walk must decline as it declines a failure.
fn msbuild_seen_from_every_cwd(
    layout: &Layout,
    from_project_dir: Result<String, String>,
) -> Result<String, String> {
    let proj = layout.sdk_root().join("p.proj");
    let env = child_environment(layout);
    let mut answers = vec![from_project_dir];
    for cwd in [layout.empty_cwd(), layout.full_cwd()] {
        answers.push(msbuild_seen_from(&proj, &env, &cwd));
    }
    if answers.iter().all(|a| *a == answers[0]) {
        answers.swap_remove(0)
    } else {
        Err(format!("{MOVES}: {answers:#?}"))
    }
}

#[test]
fn sdk_import_project_paths_through_a_property_resolve_as_msbuild_does() {
    for kind in KINDS {
        let tally = check_property_cases(0, 24, kind);
        assert!(
            tally.imported > 0 && tally.failed > 0,
            "{kind:?}: {tally:?}"
        );
        if let Kind::Plain = kind {
            // The generator still reaches both sides of the adjustment.
            assert!(tally.adjusted > 0 && tally.moved > 0, "{kind:?}: {tally:?}");
        }
    }
}

/// The shape that found the raw-text join: a property holding an absolute
/// path names `<sdk>//<that path>` to MSBuild, which is no file, while the
/// same text written in the attribute names the file itself.
#[test]
fn an_absolute_path_through_a_property_is_appended_to_the_sdk_directory() {
    let layout = Layout::new();
    let absolute = layout.sdk_root().join("E.props");
    let absolute = absolute.to_string_lossy();
    let prelude = format!("  <PropertyGroup><P>{absolute}</P></PropertyGroup>\n");
    let (xml, parsed, theirs) =
        evaluate_both_after(&layout, Kind::Sdk, &prelude, &["$(P)".to_string()]);
    assert!(
        !assert_certain_implies_exact("via $(P)", &xml, &parsed, theirs, true),
        "MSBuild imported {absolute} through $(P)"
    );
    let (xml, parsed, theirs) = evaluate_both(&layout, Kind::Sdk, &[absolute.into_owned()]);
    assert!(assert_certain_implies_exact(
        "written", &xml, &parsed, theirs, true
    ));
}

/// A plain import of a path whose `\` a property supplies, from the SDK
/// directory (which holds `sub/`), with MSBuild run from there, from an empty
/// directory and from one holding every first segment. Each case says whether
/// MSBuild's answer moves with its working directory, and whether the walk
/// must commit (the adjustment rewrites whatever the directory holds).
#[test]
fn a_backslash_a_property_supplies_is_adjusted_as_msbuild_does() {
    let layout = Layout::new();
    let root = layout.sdk_root();
    let root = root.to_string_lossy();
    let cases: &[(&str, &[&str], bool, bool)] = &[
        // `..` is a directory under any working directory.
        (r"..\targets", &["$(P)/T.props"], false, true),
        (r"..\Sdk\", &["$(P)/E.props"], false, true),
        // So is `.`: the rewrite is the duplicate-import key, and `E` is
        // imported once.
        (r".\sub\..\E.props", &["E.props", "$(P)"], false, true),
        // `sub` may or may not be a directory under the working directory,
        // but no spelling the adjustment leaves collapses or keys otherwise:
        // `D` is imported once, and `S` once.
        (
            r"sub\deeper\D.props",
            &["$(P)", "sub/deeper/D.props"],
            false,
            true,
        ),
        (r"sub\S.props", &["sub/S.props", "$(P)"], false, true),
        // An absolute first segment is probed where it is.
        (&format!(r"{root}\sub"), &["$(P)/../E.props"], false, true),
        // `sub\deeper/..` pops `sub\deeper` whole when `sub/` is missing
        // under the working directory, so MSBuild opens `Sdk/S.props`, which
        // is not there, and otherwise `Sdk/sub/S.props`.
        (r"sub\deeper", &["$(P)/../S.props"], true, false),
        // A `\` kept is kept in the duplicate-import key, which then differs
        // from `E.props`'s: `E` is imported twice unless `ghost/` exists.
        (r"ghost\..\E.props", &["E.props", "$(P)"], true, false),
        // A missing absolute first segment keeps the `\`, wherever MSBuild
        // runs, and the walk declines.
        (
            r"/borzoi-missing-root\x\..\..",
            &["$(P)/E.props"],
            false,
            false,
        ),
    ];
    for &(value, imports, moves, must_commit) in cases {
        let prelude = format!("  <PropertyGroup><P>{value}</P></PropertyGroup>\n");
        let imports: Vec<String> = imports.iter().map(|i| (*i).to_string()).collect();
        let (xml, parsed, theirs) = evaluate_both_after(&layout, Kind::Plain, &prelude, &imports);
        let theirs = msbuild_seen_from_every_cwd(&layout, theirs);
        assert_eq!(
            theirs.as_ref().is_err_and(|e| e.contains(MOVES)),
            moves,
            "{value}: {theirs:?}"
        );
        assert_certain_implies_exact(value, &xml, &parsed, theirs, must_commit);
    }
}

#[test]
#[ignore = "soak: fresh seed, BORZOI_MSBUILD_SOAK_SEED / _CASES"]
fn sdk_import_project_paths_through_a_property_soak() {
    let (seed, cases) = common::soak_parameters("sdk_import_project_paths_property", 40);
    for kind in KINDS {
        let tally = check_property_cases(seed, cases, kind);
        println!("{kind:?}: {tally:?}");
    }
}

/// Spellings outside the modelled domain whose `..` erases a segment MSBuild
/// acts on. Each fails or imports differently in MSBuild, so committing to the
/// collapsed path would be wrong; we must decline or agree.
#[test]
fn sdk_import_project_paths_outside_the_domain_never_commit_wrongly() {
    let layout = Layout::new();
    for import in [
        // MSB4102: a NUL in the path.
        "%00/../E.props",
        // A list: `<root>/E.props` and the project-relative `sub/../E.props`.
        "E.props;sub/../E.props",
        // Wildcards glob before normalising.
        "x?/../E.props",
        "*/../E.props",
        // Whitespace is trimmed from a list entry.
        " x/../E.props",
        // A decoded `\` is no separator when `..` collapses.
        ".%5c./../targets/T.props",
        "sub%5c../E.props",
        "sub%2f../E.props",
    ] {
        for kind in KINDS {
            let import = import.to_string();
            let (xml, parsed, theirs) = evaluate_both(&layout, kind, std::slice::from_ref(&import));
            assert_certain_implies_exact(
                &format!("{kind:?} {import}"),
                &xml,
                &parsed,
                theirs,
                false,
            );
        }
    }
}

/// An SDK root holding a character MSBuild re-parses in the combined import
/// path (`;` splits, `*`/`?` glob, `%XX` decodes, and on Unix a `\` reads as
/// a separator): we decline or agree.
#[test]
fn sdk_roots_msbuild_would_reparse_never_commit_wrongly() {
    for parent in ["a;b", "st*r", "q?", "x%41", "back\\slash"] {
        let layout = Layout::under(parent);
        for import in ["E.props", "../targets/T.props", "../../../../E.props"] {
            let import = import.to_string();
            let (xml, parsed, theirs) =
                evaluate_both(&layout, Kind::Sdk, std::slice::from_ref(&import));
            assert_certain_implies_exact(
                &format!("{parent:?} {import}"),
                &xml,
                &parsed,
                theirs,
                false,
            );
        }
    }
}

#[test]
#[ignore = "soak: fresh seed, BORZOI_MSBUILD_SOAK_SEED / _CASES"]
fn sdk_import_project_path_tails_soak() {
    let (seed, cases) = common::soak_parameters("sdk_import_project_path_tails", 40);
    for kind in KINDS {
        let (imported, failed) = check_tail_cases(seed, cases, kind);
        println!("{kind:?}: imported {imported}, failed {failed}");
    }
}

/// The real Web SDK: `Sdk.Server.targets` imports
/// `Microsoft.NET.Sdk.Web.ProjectSystem`'s
/// `..\targets\Microsoft.NET.Sdk.Web.BeforeCommon.targets`, which defaults
/// `EventSourceSupport` to `true` for an AOT-published app before
/// `Microsoft.NET.Sdk`'s targets run. We must reach it, commit the value, and
/// agree with MSBuild.
#[test]
fn web_sdk_before_common_targets_is_imported() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let root =
        borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalise tempdir");
    let proj = root.join("Web.fsproj");
    let xml = r#"<Project Sdk="Microsoft.NET.Sdk.Web">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <PublishAot>true</PublishAot>
  </PropertyGroup>
</Project>
"#;
    std::fs::write(&proj, xml).expect("write project");

    let dotnet_root = common::dotnet_root_from_env();
    let (user_dotnet_root, overrides_present) = common::workload_env_from_process();
    let workload_env = borzoi_msbuild::workloads::WorkloadEnvironment {
        user_dotnet_root: user_dotnet_root.as_deref(),
        overrides_present,
        // The fixture tempdir has no global.json above it.
        global_json: Default::default(),
        process_architecture: None,
    };
    let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        borzoi_msbuild::resolve_sdk(
            &dotnet_root,
            None,
            name,
            None,
            None,
            &workload_env,
            observer,
        )
    };
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, xml)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        Some(&resolver),
        None,
    )
    .unwrap_or_else(|e| panic!("our parse: {e}"));
    let declined_imports: Vec<_> = parsed
        .diagnostics
        .iter()
        .filter(|d| {
            matches!(
                &d.kind,
                borzoi_msbuild::DiagnosticKind::UnsupportedConstruct { element }
                    if element.starts_with("Import")
            ) || matches!(&d.kind, borzoi_msbuild::DiagnosticKind::ImportFailed { .. })
        })
        .collect();
    assert!(
        declined_imports.is_empty(),
        "the Web SDK chain declined an import: {declined_imports:#?}"
    );
    assert!(
        !parsed
            .property("EventSourceSupport")
            .untrusted_cause()
            .is_some(),
        "EventSourceSupport untrusted: {:?}",
        parsed.property("EventSourceSupport").untrusted_cause()
    );
    let ours = parsed
        .properties
        .get("EventSourceSupport")
        .cloned()
        .unwrap_or_default();

    let mut cmd = Command::new("dotnet");
    cmd.current_dir(&root);
    cmd.env_clear();
    cmd.envs(std::env::vars().filter(|(key, _)| {
        matches!(key.as_str(), "PATH" | "HOME" | "TMPDIR")
            || key.starts_with("DOTNET_")
            || key.starts_with("NUGET_")
    }));
    cmd.args(["msbuild", "-nologo", "-getProperty:EventSourceSupport"]);
    cmd.arg(&proj);
    let out = BoundedCommand::new(cmd)
        .timeout(MSBUILD_TIMEOUT)
        .run_ok(format_args!("dotnet msbuild for {}", proj.display()));
    let theirs = String::from_utf8(out.stdout)
        .expect("msbuild stdout is UTF-8")
        .trim()
        .to_string();
    assert_eq!(theirs, "true", "MSBuild no longer exercises the import");
    assert_eq!(ours, theirs);
}

/// MSBuild turns each `\` written in an import's `Project` into `/` before it
/// expands it, SDK import or plain: a property function reading a `\` written
/// in its argument reads a `/`.
#[test]
fn a_backslash_written_in_the_attribute_is_a_slash_before_expansion() {
    let layout = Layout::new();
    let sdk_root = layout.sdk_root();
    for (name, marker) in [("True.props", "slash"), ("False.props", "backslash")] {
        std::fs::write(
            sdk_root.join(name),
            format!(
                "<Project><PropertyGroup><Seen>$(Seen);{marker}</Seen></PropertyGroup></Project>"
            ),
        )
        .expect("write marker");
    }
    let prelude = "  <PropertyGroup><Slash>a/b</Slash></PropertyGroup>\n";
    let imports = vec![r"$(Slash.Contains('\')).props".to_owned()];
    // On Windows, `FixFilePath` leaves the attribute as written.
    let expected = if cfg!(windows) {
        ";backslash"
    } else {
        ";slash"
    };
    for kind in KINDS {
        let (xml, parsed, theirs) = evaluate_both_after(&layout, kind, prelude, &imports);
        assert_eq!(
            theirs.as_deref(),
            Ok(expected),
            "{kind:?}: MSBuild's import"
        );
        assert_certain_implies_exact(&format!("{kind:?}"), &xml, &parsed, theirs, true);
    }
}

/// A rooted SDK import bypasses the SDK root, and a `..` after a property's
/// `\` pops `seg/child`'s last segment where `seg/` is under the startup
/// directory and `seg\child` whole elsewhere: MSBuild opens `work/seg/T.props`
/// or `work/T.props`. The walk commits neither.
#[test]
#[cfg(not(windows))]
fn a_rooted_sdk_import_through_a_backslash_and_a_parent_hop_declines() {
    let layout = Layout::new();
    let work = layout.root.join("work");
    std::fs::create_dir_all(work.join("seg")).expect("mkdir work/seg");
    for (file, marker) in [("T.props", "top"), ("seg/T.props", "seg")] {
        std::fs::write(
            work.join(file),
            format!(
                "<Project><PropertyGroup><Seen>$(Seen);{marker}</Seen></PropertyGroup></Project>"
            ),
        )
        .expect("write marker");
    }
    let prelude = "  <PropertyGroup><G>seg\\child</G></PropertyGroup>\n";
    let import = format!("/missing/..{}/$(G)/../T.props", work.display());
    let (xml, parsed, _) = evaluate_both_after(&layout, Kind::Sdk, prelude, &[import]);
    // MSBuild's answer moves with its startup directory.
    let proj = layout.root.join("proj").join("p.proj");
    let env = child_environment(&layout);
    let with_seg = layout.root.join("cwd-seg");
    std::fs::create_dir_all(with_seg.join("seg")).expect("mkdir cwd-seg/seg");
    assert_eq!(
        msbuild_seen_from(&proj, &env, &with_seg).as_deref(),
        Ok(";seg"),
        "from a directory holding seg/\n{xml}"
    );
    assert_eq!(
        msbuild_seen_from(&proj, &env, &layout.empty_cwd()).as_deref(),
        Ok(";top"),
        "from one holding none\n{xml}"
    );
    assert!(
        !matches!(
            parsed.property("Seen"),
            borzoi_msbuild::PropertyRead::Value(_)
        ),
        "we committed {:?}\n{xml}",
        parsed.property("Seen")
    );
}

/// A rooted SDK import that keeps a property's `\` with no `.` or `..` after
/// it names one file from every startup directory: the `..` before it pops
/// what it pops in every spelling. The walk follows it.
#[test]
#[cfg(not(windows))]
fn a_rooted_sdk_import_keeping_a_backslash_after_its_parent_hop_is_followed() {
    let layout = Layout::new();
    let work = layout.root.join("work");
    std::fs::create_dir_all(work.join("sub")).expect("mkdir work/sub");
    std::fs::write(
        work.join("sub/T.props"),
        "<Project><PropertyGroup><Seen>$(Seen);sub</Seen></PropertyGroup></Project>",
    )
    .expect("write marker");
    let prelude = "  <PropertyGroup><G>sub\\T.props</G></PropertyGroup>\n";
    let import = format!("/missing/..{}/$(G)", work.display());
    let (xml, parsed, theirs) = evaluate_both_after(&layout, Kind::Sdk, prelude, &[import]);
    assert_eq!(theirs.as_deref(), Ok(";sub"), "MSBuild's import\n{xml}");
    let proj = layout.root.join("proj").join("p.proj");
    let env = child_environment(&layout);
    let with_sub = layout.root.join("cwd-sub");
    std::fs::create_dir_all(with_sub.join("sub")).expect("mkdir cwd-sub/sub");
    assert_eq!(
        msbuild_seen_from(&proj, &env, &with_sub).as_deref(),
        Ok(";sub"),
        "from a directory holding sub/\n{xml}"
    );
    assert_eq!(
        parsed.property("Seen"),
        borzoi_msbuild::PropertyRead::Value(";sub".to_owned()),
        "{xml}"
    );
}

/// With the startup directory supplied and no `seg/` there, a rooted SDK
/// import keeps the property's `\`, and MSBuild's `..` pops `seg\child`
/// whole: it opens `work/T.props`. The walk does not model that spelling, and
/// declines.
#[test]
#[cfg(not(windows))]
fn a_rooted_sdk_import_keeping_a_backslash_declines_with_a_start() {
    let layout = Layout::new();
    let work = layout.root.join("work");
    std::fs::create_dir_all(work.join("seg")).expect("mkdir work/seg");
    for (file, marker) in [("T.props", "top"), ("seg/T.props", "seg")] {
        std::fs::write(
            work.join(file),
            format!(
                "<Project><PropertyGroup><Seen>$(Seen);{marker}</Seen></PropertyGroup></Project>"
            ),
        )
        .expect("write marker");
    }
    let start = layout.empty_cwd();
    let sdk_root = layout.sdk_root();
    let resolver = |name: &str,
                    _observer: &borzoi_msbuild::observed::Observer|
     -> Result<SdkResolution, SdkResolveError> {
        if name == "MySdk" {
            Ok(SdkResolution::Single(SdkPaths {
                root: sdk_root.clone(),
                props: sdk_root.join("Sdk.props"),
                targets: sdk_root.join("Sdk.targets"),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let xml = format!(
        "<Project>\n  <PropertyGroup><G>seg\\child</G></PropertyGroup>\n  \
         <Import Sdk=\"MySdk\" Project=\"/missing/..{}/$(G)/../T.props\" />\n</Project>\n",
        work.display()
    );
    let proj = layout.root.join("proj").join("p.proj");
    std::fs::create_dir_all(proj.parent().unwrap()).expect("mkdir proj");
    std::fs::write(&proj, &xml).expect("write project");
    let (parsed, _) = borzoi_msbuild::test_support::parse_fsproj_reads(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml).expect("a full path"),
        &HashMap::new(),
        &child_environment(&layout),
        Some(&resolver),
        None,
        Some(&start),
        &borzoi_msbuild::test_support::ReadProbe::default(),
    )
    .expect("well-formed");
    assert!(
        !matches!(
            parsed.property("Seen"),
            borzoi_msbuild::PropertyRead::Value(_)
        ),
        "we committed {:?}\n{xml}",
        parsed.property("Seen")
    );
}

/// A missing SDK import named through a property's `\` names one file under
/// the SDK root from every startup directory, so its failure is certain.
#[test]
#[cfg(not(windows))]
fn a_missing_sdk_import_through_a_backslash_is_a_certain_rejection() {
    let layout = Layout::new();
    // Two backslashes: the whole value's pass collapses the run where it
    // respells, so the worlds differ in more than separators.
    let prelude = "  <PropertyGroup><S>seg\\\\Missing.props</S></PropertyGroup>\n";
    let (xml, parsed, theirs) =
        evaluate_both_after(&layout, Kind::Sdk, prelude, &["$(S)".to_owned()]);
    assert!(theirs.is_err(), "MSBuild rejects it: {theirs:?}\n{xml}");
    assert_eq!(
        parsed.rejection.map(|r| r.certainty),
        Some(borzoi_msbuild::RejectionCertainty::Certain),
        "{xml}"
    );
}

/// Whether an import under a gate the walk cannot decide may load nothing is
/// judged on the file MSBuild would open: the attribute's written `\` is a
/// `/` there too. Only `False.props` exists; MSBuild takes the gate (it folds
/// `É` and `é` alike, which the walk does not model), opens `True.props`,
/// and rejects the project.
#[test]
#[cfg(not(windows))]
fn an_undecided_import_is_judged_on_the_file_msbuild_opens() {
    let layout = Layout::new();
    let sdk_root = layout.sdk_root();
    std::fs::write(sdk_root.join("False.props"), "<Project/>").expect("write props");
    std::fs::write(layout.root.join("False.props"), "<Project/>").expect("write props");
    let env = child_environment(&layout);
    let resolver = |name: &str,
                    _observer: &borzoi_msbuild::observed::Observer|
     -> Result<SdkResolution, SdkResolveError> {
        if name == "MySdk" {
            Ok(SdkResolution::Single(SdkPaths {
                root: sdk_root.clone(),
                props: sdk_root.join("Sdk.props"),
                targets: sdk_root.join("Sdk.targets"),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    for sdk in [" Sdk=\"MySdk\"", ""] {
        let xml = format!(
            "<Project>\n  <PropertyGroup><Slash>a/b</Slash></PropertyGroup>\n  \
             <Import{sdk} Project=\"$(Slash.Contains('\\')).props\" Condition=\"'É' == 'é'\" />\n  \
             <PropertyGroup><Seen>after</Seen></PropertyGroup>\n</Project>\n"
        );
        let proj = layout.root.join("p.proj");
        std::fs::write(&proj, &xml).expect("write project");
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&proj, &xml).expect("a full path"),
            &HashMap::new(),
            &env,
            Some(&resolver),
            None,
        )
        .unwrap_or_else(|e| panic!("our parse: {e}\n{xml}"));
        let theirs = msbuild_seen_from(&proj, &env, &layout.root);
        assert!(
            theirs.is_err(),
            "{sdk}: MSBuild opens True.props: {theirs:?}"
        );
        assert!(
            parsed.rejection.is_some(),
            "{sdk}: we commit {:?}\n{xml}",
            parsed.properties.get("Seen")
        );
    }
}

/// Under a gate the walk cannot decide, a rooted SDK import that keeps a
/// property's `\` is judged as one the walk does not follow: MSBuild's `..`
/// pops `seg\child` whole where the startup directory holds no `seg`, so it
/// opens the missing `work/T.props`, not `work/seg/T.props`, and rejects.
#[test]
#[cfg(not(windows))]
fn an_undecided_rooted_sdk_import_keeping_a_backslash_may_reject() {
    let layout = Layout::new();
    let work = layout.root.join("work");
    std::fs::create_dir_all(work.join("seg")).expect("mkdir work/seg");
    std::fs::write(work.join("seg/T.props"), "<Project/>").expect("write props");
    let env = child_environment(&layout);
    let sdk_root = layout.sdk_root();
    let resolver = |name: &str,
                    _observer: &borzoi_msbuild::observed::Observer|
     -> Result<SdkResolution, SdkResolveError> {
        if name == "MySdk" {
            Ok(SdkResolution::Single(SdkPaths {
                root: sdk_root.clone(),
                props: sdk_root.join("Sdk.props"),
                targets: sdk_root.join("Sdk.targets"),
            }))
        } else {
            Err(SdkResolveError::NotFound)
        }
    };
    let xml = format!(
        "<Project>\n  <PropertyGroup><G>seg\\child</G></PropertyGroup>\n  \
         <Import Sdk=\"MySdk\" Project=\"/missing/..{}/$(G)/../T.props\" \
         Condition=\"'É' == 'é'\" />\n  \
         <PropertyGroup><Seen>after</Seen></PropertyGroup>\n</Project>\n",
        work.display()
    );
    let proj = layout.root.join("p.proj");
    std::fs::write(&proj, &xml).expect("write project");
    let start = layout.empty_cwd();
    let theirs = msbuild_seen_from(&proj, &env, &start);
    assert!(theirs.is_err(), "MSBuild opens work/T.props: {theirs:?}");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&proj, &xml).expect("a full path"),
        &HashMap::new(),
        &env,
        Some(&resolver),
        None,
    )
    .unwrap_or_else(|e| panic!("our parse: {e}\n{xml}"));
    assert!(
        parsed.rejection.is_some(),
        "we commit {:?}\n{xml}",
        parsed.properties.get("Seen")
    );
}

/// A resolver that returns no root gives MSBuild no file to open, whatever
/// the `Project`: a rooted one that keeps a property's `\` imports nothing,
/// followed or under a gate the walk cannot decide, and costs the walk
/// nothing.
#[test]
#[cfg(not(windows))]
fn a_rooted_backslash_under_no_sdk_root_imports_nothing() {
    let layout = Layout::new();
    let env = child_environment(&layout);
    let resolver =
        |_: &str,
         _observer: &borzoi_msbuild::observed::Observer|
         -> Result<SdkResolution, SdkResolveError> { Ok(SdkResolution::Roots(Vec::new())) };
    for gate in ["", " Condition=\"'É' == 'é'\""] {
        let xml = format!(
            "<Project>\n  <PropertyGroup><G>seg\\child</G></PropertyGroup>\n  \
             <Import Sdk=\"MySdk\" Project=\"/missing/$(G)/../T.props\"{gate} />\n  \
             <PropertyGroup><Seen>after</Seen></PropertyGroup>\n</Project>\n"
        );
        let proj = layout.root.join("p.proj");
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&proj, &xml).expect("a full path"),
            &HashMap::new(),
            &env,
            Some(&resolver),
            None,
        )
        .unwrap_or_else(|e| panic!("our parse: {e}\n{xml}"));
        assert!(
            parsed.rejection.is_none(),
            "{gate}: {:#?}",
            parsed.rejection
        );
        // An undecided gate leaves the items uncertain on its own.
        if gate.is_empty() {
            assert!(!parsed.items_uncertain, "{:#?}", parsed.diagnostics);
        }
        assert_eq!(
            parsed.properties.get("Seen").map(String::as_str),
            Some("after"),
            "{gate}"
        );
    }
}
