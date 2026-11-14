//! [`SdkLanguageFacts`] against the compilers it describes: every SDK installed
//! under `$DOTNET_ROOT` has its own `FSharp/fsc.dll` run over every
//! `<LangVersion>` spelling, and what the compiler does with each is held
//! exactly to the reading its band's row gives (certain-implies-exact). An SDK
//! whose band has no row is reported, not graded: the table declines it, and
//! the LSP falls back to the pinned compiler's reading with no floor. A row no
//! installed SDK grades fails the run, because a row is a claim about a
//! compiler, and an ungraded one is a claim nothing has checked.
//!
//! What a compiler does with a spelling is read from the compiler's own
//! messages, never from its source:
//!
//! - FS0246 ("Unrecognized value") is [`LangVersionReading::Unrecognised`].
//! - FS3880 ("out of support") is [`LangVersionReading::OutOfSupport`], at the
//!   version the same spelling selects under `SKIP_VERSION_SUPPORTED_CHECK=1`,
//!   which lifts the refusal.
//! - Otherwise the compiler checks at some version, named by FS3350 ("Feature
//!   … is not available in F# *V*") on a probe file using a feature newer than
//!   *V*. Each probe is a parse-stage feature, so a parse-only run suffices.
//! - Where no probe fires, the version is at least the newest feature any
//!   probe gates in this compiler. A type-checked from-end slice (FS3303,
//!   preview-only in every compiler graded) then separates `preview` from the
//!   one listed (`--langversion:?`) numbered version at or above that feature;
//!   if more than one listed version could be it, the probes cannot tell them
//!   apart and the run fails, asking for a probe gated at the newer one.
//!
//! [`a_project_reads_langversion_with_its_sdks_compiler`] then checks the
//! plumbing: a project pinned to each installed SDK by `global.json` evaluates
//! to that SDK's compiler, and the workspace, the `.fsproj` diagnostics and the
//! fold read its `<LangVersion>` as that compiler does.
//!
//! Requires the devshell's `$DOTNET_ROOT`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use borzoi::sdk_discovery::SdkDiscoveryEnv;
use borzoi::sdk_language::{
    COMPILER_ENVIRONMENT, COMPILER_SELECTORS, LangVersionReading, LangVersionSelection,
    ProjectCompiler, RefusalKind, SdkLanguageFacts,
};
use borzoi::workspace::Workspace;
use borzoi_cst::language_version::LanguageVersion;
use borzoi_msbuild::SdkVersion;
use borzoi_spawn::BoundedCommand;

use crate::common::host_fs::{self, HostPath as _};

/// One installed SDK's compiler.
struct Compiler {
    sdk: SdkVersion,
    fsc: PathBuf,
}

fn dotnet_root() -> PathBuf {
    std::env::var_os("DOTNET_ROOT")
        .map(PathBuf::from)
        .expect("DOTNET_ROOT unset (run under `nix develop`)")
}

/// Every SDK under `$DOTNET_ROOT/sdk` that ships an F# compiler, by version.
fn installed_compilers() -> Vec<Compiler> {
    let sdks = dotnet_root().join("sdk");
    let mut compilers: Vec<Compiler> = host_fs::read_dir(&sdks)
        .unwrap_or_else(|e| panic!("list {}: {e}", sdks.display()))
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let sdk = SdkVersion::parse(entry.file_name().to_str()?)?;
            let fsc = entry.path().join("FSharp").join("fsc.dll");
            fsc.host_is_file().then_some(Compiler { sdk, fsc })
        })
        .collect();
    compilers.sort_by(|a, b| a.sdk.cmp(&b.sdk));
    assert!(
        !compilers.is_empty(),
        "no SDK under {} ships FSharp/fsc.dll",
        sdks.display()
    );
    compilers
}

/// The reference assemblies a type-checked probe compiles against: one
/// `Microsoft.NETCore.App.Ref` pack's, chosen deterministically.
fn reference_assemblies() -> Vec<PathBuf> {
    let packs = dotnet_root()
        .join("packs")
        .join("Microsoft.NETCore.App.Ref");
    let mut dirs: Vec<PathBuf> = host_fs::read_dir(&packs)
        .unwrap_or_else(|e| panic!("list {}: {e}", packs.display()))
        .filter_map(|e| Some(e.ok()?.path().join("ref").join("net10.0")))
        .filter(|dir| dir.join("System.Runtime.dll").host_is_file())
        .collect();
    dirs.sort();
    let dir = dirs
        .pop()
        .unwrap_or_else(|| panic!("no ref/net10.0 pack under {}", packs.display()));
    let mut dlls: Vec<PathBuf> = host_fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("list {}: {e}", dir.display()))
        .filter_map(|e| Some(e.ok()?.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "dll"))
        .collect();
    dlls.sort();
    dlls
}

/// The probe sources, written once.
struct Probes {
    _dir: tempfile::TempDir,
    /// Parse-stage features, each gated at a known version in some compiler.
    parse: Vec<PathBuf>,
    /// A from-end slice, which the type checker refuses below `preview`
    /// (FS3303).
    preview: PathBuf,
    references: Vec<PathBuf>,
}

impl Probes {
    fn write() -> Probes {
        let dir = tempfile::tempdir().expect("temp dir");
        let write = |name: &str, text: &str| {
            let path = dir.path().join(name);
            std::fs::write(&path, text).expect("write probe");
            path
        };
        let parse = vec![
            // `AllowTypedLetUseAndBang`, F# 10.0.
            write(
                "TypedLetBang.fs",
                "module TypedLetBang\nlet f () = async {\n    let! x: int = async { return 1 }\n    return x\n}\n",
            ),
            // `PreprocessorElif`, F# 11.0.
            write(
                "Elif.fs",
                "module Elif\n#if A\nlet a = 1\n#elif B\nlet a = 2\n#endif\n",
            ),
        ];
        let preview = write(
            "FromEndSlice.fs",
            "module FromEndSlice\nlet a = [| 1; 2 |]\nlet b = a.[^1]\n",
        );
        Probes {
            _dir: dir,
            parse,
            preview,
            references: reference_assemblies(),
        }
    }
}

/// The `error FSnnnn: …` lines of a compiler run.
fn errors(output: &str) -> Vec<&str> {
    output
        .lines()
        .filter(|line| line.contains("error FS"))
        .collect()
}

fn has_error(output: &str, code: &str) -> bool {
    errors(output)
        .iter()
        .any(|line| line.contains(&format!("error {code}:")))
}

/// Run `compiler` with `args`, `SKIP_VERSION_SUPPORTED_CHECK` set to `1` when
/// `skip` and unset otherwise, and return its output.
fn run(compiler: &Compiler, args: &[OsString], skip: bool) -> String {
    run_with(compiler, args, skip.then_some("1"))
}

/// Run `compiler` with `args` and `SKIP_VERSION_SUPPORTED_CHECK` set to
/// `skip`, or unset for `None`, and return its output.
fn run_with(compiler: &Compiler, args: &[OsString], skip: Option<&str>) -> String {
    let mut cmd = Command::new("dotnet");
    cmd.arg("exec")
        .arg(&compiler.fsc)
        .arg("--nologo")
        .args(args);
    match skip {
        Some(value) => cmd.env("SKIP_VERSION_SUPPORTED_CHECK", value),
        None => cmd.env_remove("SKIP_VERSION_SUPPORTED_CHECK"),
    };
    // A refusal or a probe's error exits non-zero; the output is the answer.
    let output = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(300))
        .run()
        .unwrap_or_else(|e| panic!("fsc of SDK {}: {e}", compiler.sdk));
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    text
}

fn lang_arg(spelling: Option<&str>) -> Vec<OsString> {
    spelling
        .map(|s| vec![OsString::from(format!("--langversion:{s}"))])
        .unwrap_or_default()
}

/// A version the compiler names, as borzoi models it.
fn modelled(text: &str) -> Result<LanguageVersion, String> {
    LanguageVersion::from_lang_version_text(text)
        .filter(|v| *v != LanguageVersion::Preview)
        .ok_or_else(|| format!("the compiler names F# {text}, a version borzoi does not model"))
}

/// What the compiler says about versions, before any spelling is read.
struct Calibration {
    /// The numbered versions `--langversion:?` lists, ascending.
    listed: Vec<LanguageVersion>,
    /// The one it marks `(Default)`.
    marked_default: LanguageVersion,
    /// The newest version any parse probe's feature is introduced at, in this
    /// compiler: a version with no FS3350 on the probes is at least this.
    probed_top: LanguageVersion,
}

fn calibrate(compiler: &Compiler, probes: &Probes) -> Result<Calibration, String> {
    let help = run(compiler, &[OsString::from("--langversion:?")], false);
    let mut listed = Vec::new();
    let mut marked_default = None;
    for line in help.lines().map(str::trim) {
        let (text, is_default) = match line.strip_suffix("(Default)") {
            Some(text) => (text.trim(), true),
            None => (line, false),
        };
        if !text.starts_with(|c: char| c.is_ascii_digit()) {
            continue;
        }
        let version = modelled(text)?;
        listed.push(version);
        if is_default {
            marked_default = Some(version);
        }
    }
    listed.sort();
    let marked_default =
        marked_default.ok_or_else(|| format!("--langversion:? marks no default:\n{help}"))?;
    // The probes at the oldest listed version, the refusal lifted: every
    // probe this compiler gates fires, each naming its feature's version.
    let oldest = listed
        .first()
        .ok_or_else(|| format!("--langversion:? lists no version:\n{help}"))?;
    let mut args = lang_arg(Some(&oldest.to_string()));
    args.push("--parseonly".into());
    args.extend(probes.parse.iter().map(|p| p.as_os_str().to_owned()));
    let output = run(compiler, &args, true);
    let mut probed_top = None;
    for line in errors(&output) {
        if let Some((_, introduced)) = unavailable(line) {
            let introduced = modelled(introduced)?;
            probed_top = probed_top.max(Some(introduced));
        }
    }
    let probed_top =
        probed_top.ok_or_else(|| format!("no probe is gated in this compiler:\n{output}"))?;
    Ok(Calibration {
        listed,
        marked_default,
        probed_top,
    })
}

/// FS3350's `(current, introduced)` versions, if `line` is one.
fn unavailable(line: &str) -> Option<(&str, &str)> {
    let rest = line.split_once("error FS3350: ")?.1;
    let rest = rest.split_once("is not available in F# ")?.1;
    let (current, rest) = rest.split_once(". Please use language version ")?;
    let introduced = rest.split_once(" or greater")?.0;
    Some((current, introduced))
}

/// What `compiler` does with `--langversion:<spelling>` (no flag for `None`).
fn measure(
    compiler: &Compiler,
    probes: &Probes,
    calibration: &Calibration,
    spelling: Option<&str>,
    skip: bool,
) -> Result<LangVersionReading, String> {
    let mut args = lang_arg(spelling);
    args.push("--parseonly".into());
    args.extend(probes.parse.iter().map(|p| p.as_os_str().to_owned()));
    let output = run(compiler, &args, skip);
    if has_error(&output, "FS0246") {
        return Ok(LangVersionReading::Unrecognised);
    }
    if has_error(&output, "FS3880") {
        if skip {
            return Err(format!("FS3880 with the check skipped:\n{output}"));
        }
        return match measure(compiler, probes, calibration, spelling, true)? {
            LangVersionReading::Checks(version) => Ok(LangVersionReading::OutOfSupport(version)),
            other => Err(format!("FS3880, then {other:?} with the check skipped")),
        };
    }
    let mut current = None;
    for line in errors(&output) {
        let Some((named, _)) = unavailable(line) else {
            return Err(format!("an error no probe accounts for:\n{output}"));
        };
        let named = modelled(named)?;
        if current.is_some_and(|c| c != named) {
            return Err(format!("FS3350 names two versions:\n{output}"));
        }
        current = Some(named);
    }
    if let Some(version) = current {
        return Ok(LangVersionReading::Checks(version));
    }
    let mut args = lang_arg(spelling);
    args.extend(["--typecheckonly".into(), "--noframework".into()]);
    let core = compiler.fsc.with_file_name("FSharp.Core.dll");
    for reference in std::iter::once(&core).chain(&probes.references) {
        let mut arg = OsString::from("-r:");
        arg.push(reference);
        args.push(arg);
    }
    args.push(probes.preview.as_os_str().to_owned());
    let checked = run(compiler, &args, skip);
    let errors = errors(&checked);
    if errors.is_empty() {
        return Ok(LangVersionReading::Checks(LanguageVersion::Preview));
    }
    if !errors.iter().all(|line| line.contains("error FS3303:")) {
        return Err(format!("the preview probe fails otherwise:\n{checked}"));
    }
    let candidates: Vec<_> = calibration
        .listed
        .iter()
        .filter(|v| **v >= calibration.probed_top)
        .collect();
    match candidates.as_slice() {
        [only] => Ok(LangVersionReading::Checks(**only)),
        _ => Err(format!(
            "the probes cannot tell {candidates:?} apart; add a parse probe for a feature \
             introduced at the newer of them"
        )),
    }
}

/// Every spelling graded: the absent value, each alias in two cases, each
/// numbered version in both forms the pinned compiler takes, and spellings
/// no graded compiler recognises.
fn spellings() -> Vec<Option<String>> {
    let mut out: Vec<Option<String>> = vec![None];
    for alias in ["default", "latest", "latestmajor", "preview"] {
        out.push(Some(alias.to_string()));
        out.push(Some(alias.to_ascii_uppercase()));
    }
    for version in LanguageVersion::NUMBERED {
        let text = version.to_string();
        if let Some(short) = text.strip_suffix(".0") {
            out.push(Some(short.to_string()));
        }
        out.push(Some(text));
    }
    for junk in ["4", "4.8", "5.00", "11.2", "12", "12.0", "bogus"] {
        out.push(Some(junk.to_string()));
    }
    out
}

/// Every spelling's measured reading, measured on a few threads at a time.
fn measure_all(
    compiler: &Compiler,
    probes: &Probes,
    calibration: &Calibration,
) -> BTreeMap<Option<String>, Result<LangVersionReading, String>> {
    let spellings = spellings();
    let chunk = spellings.len().div_ceil(6);
    std::thread::scope(|scope| {
        let handles: Vec<_> = spellings
            .chunks(chunk)
            .map(|batch| {
                scope.spawn(move || {
                    batch
                        .iter()
                        .map(|s| {
                            let reading =
                                measure(compiler, probes, calibration, s.as_deref(), false);
                            (s.clone(), reading)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("a measuring thread panicked"))
            .collect()
    })
}

fn spelling_name(spelling: &Option<String>) -> &str {
    spelling.as_deref().unwrap_or("(unset)")
}

#[test]
fn every_installed_compiler_reads_langversion_as_its_row_says() {
    let probes = Probes::write();
    let compilers = installed_compilers();
    let mut failures = Vec::new();
    for compiler in &compilers {
        let row = SdkLanguageFacts::for_sdk(&compiler.sdk);
        let calibration = match calibrate(compiler, &probes) {
            Ok(calibration) => calibration,
            Err(why) if row.is_some() => {
                failures.push(format!("SDK {}: cannot calibrate: {why}", compiler.sdk));
                continue;
            }
            Err(why) => {
                eprintln!(
                    "SDK {} (no row, declined): cannot calibrate: {why}",
                    compiler.sdk
                );
                continue;
            }
        };
        let measured = measure_all(compiler, &probes, &calibration);
        let Some(facts) = row else {
            eprintln!(
                "SDK {} has no row; the table declines it. Measured:",
                compiler.sdk
            );
            for (spelling, reading) in &measured {
                eprintln!("  {:>12}  {reading:?}", spelling_name(spelling));
            }
            continue;
        };
        eprintln!("SDK {}: grading {facts:?}", compiler.sdk);
        if facts.default != calibration.marked_default {
            failures.push(format!(
                "SDK {}: --langversion:? marks {} the default, the row says {}",
                compiler.sdk, calibration.marked_default, facts.default
            ));
        }
        let newest = calibration.listed.last().copied();
        if newest != Some(facts.newest) {
            failures.push(format!(
                "SDK {}: --langversion:? lists up to {newest:?}, the row says {}",
                compiler.sdk, facts.newest
            ));
        }
        for (spelling, reading) in &measured {
            let ours = facts.reading(spelling.as_deref());
            match reading {
                Ok(theirs) if *theirs == ours => {}
                Ok(theirs) => failures.push(format!(
                    "SDK {}: {}: the compiler {theirs:?}, the row {ours:?}",
                    compiler.sdk,
                    spelling_name(spelling)
                )),
                Err(why) => failures.push(format!(
                    "SDK {}: {}: unmeasurable: {why}",
                    compiler.sdk,
                    spelling_name(spelling)
                )),
            }
        }
        // `1` lifts the floor (graded above); `project_compiler` claims no
        // other value does.
        if let Some(below) = LanguageVersion::NUMBERED
            .iter()
            .rev()
            .find(|v| **v < facts.floor)
        {
            let mut args = lang_arg(Some(&below.to_string()));
            args.push("--parseonly".into());
            args.extend(probes.parse.iter().map(|p| p.as_os_str().to_owned()));
            for value in ["true", "0", " 1"] {
                let output = run_with(compiler, &args, Some(value));
                if !has_error(&output, "FS3880") {
                    failures.push(format!(
                        "SDK {}: F# {below} with SKIP_VERSION_SUPPORTED_CHECK={value:?} is not \
                         refused, but only `1` lifts the floor in borzoi's model:\n{output}",
                        compiler.sdk
                    ));
                }
            }
        }
    }
    for (major, minor, band) in SdkLanguageFacts::graded_bands() {
        let graded = compilers.iter().any(|c| {
            !c.sdk.is_prerelease()
                && (c.sdk.major(), c.sdk.minor(), c.sdk.feature_band()) == (major, minor, band)
        });
        if !graded {
            failures.push(format!(
                "the row for {major}.{minor}.{band}xx is graded by no installed SDK: drop it, or \
                 install an SDK of that band for this differential"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A minimal SDK project pinned by `global.json` to exactly `sdk`, with
/// `lang` as its `<LangVersion>` and one Compile item, `A.fs`, holding
/// `source`.
fn pinned_project(dir: &Path, sdk: &SdkVersion, lang: Option<&str>, source: &str) -> PathBuf {
    std::fs::write(
        dir.join("global.json"),
        format!(r#"{{ "sdk": {{ "version": "{sdk}", "rollForward": "disable" }} }}"#),
    )
    .unwrap();
    let lang = lang
        .map(|l| format!("<LangVersion>{l}</LangVersion>"))
        .unwrap_or_default();
    let fsproj = dir.join("App.fsproj");
    std::fs::write(
        &fsproj,
        format!(
            r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework>{lang}</PropertyGroup>
  <ItemGroup><Compile Include="A.fs" /></ItemGroup>
</Project>
"#
        ),
    )
    .unwrap();
    std::fs::write(dir.join("A.fs"), source).unwrap();
    fsproj
}

/// A file whose tree differs either side of the F# 8 strict-indentation
/// boundary.
const STRADDLING: &str = "match x with\n";

/// The environments a project is evaluated under, each with whether it skips
/// the compiler's support check: the test's own, one with `DOTNET_HOST_PATH`
/// set, as `dotnet build` sets it (the evaluation cannot decide the SDK's gate
/// on it either way, and the compiler is the SDK's under both arms), and one
/// with `SKIP_VERSION_SUPPORTED_CHECK=1`, which lifts the floor.
fn environments() -> Vec<(&'static str, SdkDiscoveryEnv, bool)> {
    let mut plain = SdkDiscoveryEnv::from_process_env();
    plain
        .build_environment
        .retain(|name, _| name != "SKIP_VERSION_SUPPORTED_CHECK");
    let mut hosted = plain.clone();
    hosted.build_environment.insert(
        "DOTNET_HOST_PATH".to_string(),
        dotnet_root().join("dotnet").display().to_string(),
    );
    let mut skipped = plain.clone();
    skipped
        .build_environment
        .insert("SKIP_VERSION_SUPPORTED_CHECK".to_string(), "1".to_string());
    vec![
        ("plain", plain, false),
        ("DOTNET_HOST_PATH", hosted, false),
        ("support check skipped", skipped, true),
    ]
}

#[test]
fn a_project_reads_langversion_with_its_sdks_compiler() {
    let mut graded = 0;
    for compiler in installed_compilers() {
        if compiler.sdk.is_prerelease() {
            continue;
        }
        for (lang, (route, env, skipped)) in [None, Some("7.0"), Some("11")]
            .into_iter()
            .flat_map(|lang| environments().into_iter().map(move |env| (lang, env)))
        {
            let dir = tempfile::tempdir().unwrap();
            let fsproj = pinned_project(dir.path(), &compiler.sdk, lang, STRADDLING);
            let mut workspace = Workspace::with_env(env.clone());
            let facts = SdkLanguageFacts::for_sdk(&compiler.sdk);
            assert_eq!(
                workspace.compiler_sdk_for_project(&fsproj).as_ref(),
                facts.map(|_| &compiler.sdk),
                "a project pinned to SDK {} builds with its compiler ({route}), named for a \
                 graded SDK",
                compiler.sdk
            );
            let selection = workspace.lang_version_selection(&fsproj);
            let Some(facts) = facts else {
                assert_eq!(selection.refusal, None, "no floor for an SDK with no row");
                continue;
            };
            graded += 1;
            let expected = match facts.reading(lang) {
                LangVersionReading::Checks(v) => (v, None),
                LangVersionReading::OutOfSupport(v) if skipped => (v, None),
                LangVersionReading::OutOfSupport(v) => {
                    (v, Some(RefusalKind::OutOfSupport { floor: facts.floor }))
                }
                LangVersionReading::Unrecognised => (
                    lang.and_then(LanguageVersion::from_lang_version_text)
                        .unwrap_or(facts.default),
                    Some(RefusalKind::Unrecognised),
                ),
            };
            assert_eq!(
                (
                    selection.version,
                    selection.refusal.as_ref().map(|r| r.kind)
                ),
                expected,
                "SDK {}, LangVersion {lang:?} ({route})",
                compiler.sdk
            );
            let project_compiler = ProjectCompiler {
                sdk: compiler.sdk.clone(),
                support_check_skipped: skipped,
            };
            assert_eq!(
                selection,
                LangVersionSelection::of(
                    workspace.project(&fsproj).unwrap(),
                    Some(&project_compiler)
                )
            );

            // The `.fsproj` diagnostics report the refusal, and only it.
            let text = host_fs::read_to_string(&fsproj).unwrap();
            let diags = borzoi::fsproj_diagnostics::diagnostics_for(
                &text,
                &fsproj,
                &env,
                &workspace.build_properties(),
            );
            let reported: Vec<_> = diags
                .iter()
                .filter_map(|d| match &d.code {
                    Some(lsp_types::NumberOrString::String(code)) => Some(code.as_str()),
                    _ => None,
                })
                .collect();
            let expected_code = selection.refusal.as_ref().map(|r| r.code());
            assert_eq!(
                reported,
                expected_code.into_iter().collect::<Vec<_>>(),
                "SDK {}, LangVersion {lang:?}: {diags:#?}",
                compiler.sdk
            );

            // A refused version is a guess, so the straddling file refuses
            // the fold; a version the compiler checks at folds it.
            let mut sema = borzoi::semantic::SemanticState::new();
            let docs = borzoi::vfs::Vfs::new();
            let folds = sema
                .parses_for_project(&fsproj, &mut workspace, &docs)
                .is_some();
            assert_eq!(
                folds,
                selection.refusal.is_none(),
                "SDK {}, LangVersion {lang:?}: a refusal doubts the version",
                compiler.sdk
            );
        }
    }
    assert!(
        graded > 0,
        "no installed SDK has a row to check the plumbing with"
    );
}

/// The installed SDKs with a graded row, newest first.
fn graded_compilers() -> Vec<Compiler> {
    let mut graded: Vec<Compiler> = installed_compilers()
        .into_iter()
        .filter(|c| SdkLanguageFacts::for_sdk(&c.sdk).is_some())
        .collect();
    graded.reverse();
    assert!(!graded.is_empty(), "no installed SDK has a row");
    graded
}

/// What MSBuild evaluates each of `names` to in `fsproj`, run through the
/// `dotnet` host as `dotnet build` runs it (so with `DOTNET_HOST_PATH` set).
fn msbuild_properties(fsproj: &Path, names: &[&str]) -> BTreeMap<String, String> {
    let mut cmd = Command::new("dotnet");
    cmd.current_dir(fsproj.parent().unwrap())
        .arg("msbuild")
        .arg(fsproj)
        .args(["-nologo", "-nodeReuse:false"])
        .args(names.iter().map(|n| format!("-getProperty:{n}")))
        .env_remove("SKIP_VERSION_SUPPORTED_CHECK");
    let output = BoundedCommand::new(cmd)
        .timeout(Duration::from_secs(300))
        .run()
        .unwrap_or_else(|e| panic!("dotnet msbuild {}: {e}", fsproj.display()));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).unwrap_or_else(|e| {
        panic!(
            "dotnet msbuild -getProperty output is not JSON ({e}):\n{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    names
        .iter()
        .map(|name| {
            let value = json["Properties"][name]
                .as_str()
                .unwrap_or_else(|| panic!("no {name} in {json}"));
            (name.to_string(), value.to_string())
        })
        .collect()
}

/// The compiler a build of an ordinary project on each graded SDK runs is that
/// SDK's `fsc.dll`, under either arm of the SDK's `DOTNET_HOST_PATH` gate, and
/// the server names it under both.
///
/// MSBuild, run through the host as `dotnet build` is, takes the set arm:
/// `$(DotnetFscCompilerPath)` names the SDK's `fsc.dll`, and no F# shim
/// overrides it. Under the unset arm the `Fsc` task runs the tool beside its
/// own assembly, `$(FSharpBuildAssemblyFile)`, which is the SDK's, beside the
/// same `fsc.dll`.
#[test]
fn the_build_runs_the_compiler_the_server_names() {
    for compiler in graded_compilers() {
        let dir = tempfile::tempdir().unwrap();
        let fsproj = pinned_project(dir.path(), &compiler.sdk, None, STRADDLING);
        let props = msbuild_properties(
            &fsproj,
            &[
                "DotnetFscCompilerPath",
                "FSharpBuildAssemblyFile",
                "FSharp_Shim_Present",
            ],
        );
        let sdk_file = |name: &str, file: &str| {
            borzoi::sdk_language::sdk_version_of_sdk_file(&props[name], &["FSharp", file])
        };
        assert_eq!(
            sdk_file("DotnetFscCompilerPath", "fsc.dll").as_ref(),
            Some(&compiler.sdk),
            "{props:?}"
        );
        assert_eq!(
            sdk_file("FSharpBuildAssemblyFile", "FSharp.Build.dll").as_ref(),
            Some(&compiler.sdk),
            "{props:?}"
        );
        assert!(
            compiler
                .fsc
                .with_file_name("FSharp.Build.dll")
                .host_is_file(),
            "the task assembly sits beside {}",
            compiler.fsc.display()
        );
        assert_eq!(props["FSharp_Shim_Present"], "", "{props:?}");
        // The install's workload manifests are held apart from foreign build
        // code, or no project on a real install would have its compiler named.
        let (_, plain, _) = environments().remove(0);
        let mut workspace = Workspace::with_env(plain);
        let parsed = workspace.project(&fsproj).unwrap();
        assert!(
            !parsed.workload_definitions.targets.is_empty(),
            "the install's workload manifests define targets"
        );
        assert!(!parsed.foreign_definitions.defines_build_code());
        for (route, env, _) in environments() {
            let mut workspace = Workspace::with_env(env);
            assert_eq!(
                workspace.compiler_sdk_for_project(&fsproj).as_ref(),
                Some(&compiler.sdk),
                "{route}"
            );
        }
    }
}

/// Where a test project defines something: the project body, an imported
/// file, under a condition the evaluation cannot decide, in a target body,
/// and as a task output.
#[derive(Debug, Clone, Copy)]
enum Site {
    Body,
    DirectoryBuildProps,
    Undecidable,
    TargetBody,
    TaskOutput,
}

const SITES: [Site; 5] = [
    Site::Body,
    Site::DirectoryBuildProps,
    Site::Undecidable,
    Site::TargetBody,
    Site::TaskOutput,
];

/// A project on `sdk` whose `site` defines `property` as `value`, plus
/// `targets` in its `Directory.Build.targets`.
fn project_defining(
    dir: &Path,
    sdk: &SdkVersion,
    site: Site,
    property: &str,
    targets: &str,
) -> PathBuf {
    let fsproj = pinned_project(dir, sdk, None, STRADDLING);
    let write = format!("<{property}>/opt/elsewhere</{property}>");
    let (body, props) = match site {
        Site::Body => (
            format!("<PropertyGroup>{write}</PropertyGroup>"),
            String::new(),
        ),
        Site::DirectoryBuildProps => (
            String::new(),
            format!("<PropertyGroup>{write}</PropertyGroup>"),
        ),
        Site::Undecidable => (
            format!(
                r#"<PropertyGroup Condition="'$([System.Guid]::NewGuid())' == ''">{write}</PropertyGroup>"#
            ),
            String::new(),
        ),
        Site::TargetBody => (
            format!(
                r#"<Target Name="Pick" BeforeTargets="CoreCompile"><PropertyGroup>{write}</PropertyGroup></Target>"#
            ),
            String::new(),
        ),
        Site::TaskOutput => (
            format!(
                r#"<Target Name="Pick" BeforeTargets="CoreCompile"><CreateProperty Value="/opt/elsewhere"><Output TaskParameter="Value" PropertyName="{property}" /></CreateProperty></Target>"#
            ),
            String::new(),
        ),
    };
    let text = host_fs::read_to_string(&fsproj).unwrap();
    std::fs::write(
        &fsproj,
        text.replace("</Project>", &format!("{body}\n</Project>")),
    )
    .unwrap();
    std::fs::write(
        dir.join("Directory.Build.props"),
        format!("<Project>{props}</Project>"),
    )
    .unwrap();
    std::fs::write(
        dir.join("Directory.Build.targets"),
        format!("<Project>{targets}</Project>"),
    )
    .unwrap();
    fsproj
}

/// Anything outside the SDK that could choose the compiler makes the server
/// decline to name it: every selector, at every site in turn (each site meets
/// every fourth or fifth selector, and `DotnetFscCompilerPath` meets all of
/// them), any build code (a target or task, whatever it does), a reshaped
/// target graph, and a selector in the environment or as a global. An
/// evaluation-time write of anything else leaves the SDK's compiler named.
#[test]
fn a_compiler_choice_from_outside_the_sdk_declines() {
    let compiler = graded_compilers().remove(0);
    let (_, plain, _) = environments().remove(0);
    let named = |fsproj: &Path, env: &SdkDiscoveryEnv| {
        Workspace::with_env(env.clone()).compiler_sdk_for_project(fsproj)
    };
    let mut cases: Vec<(Site, &str)> = COMPILER_SELECTORS
        .iter()
        .enumerate()
        .map(|(i, selector)| (SITES[i % SITES.len()], *selector))
        .collect();
    cases.extend(SITES.iter().map(|site| (*site, "DotnetFscCompilerPath")));
    for (site, selector) in cases {
        let dir = tempfile::tempdir().unwrap();
        let fsproj = project_defining(dir.path(), &compiler.sdk, site, selector, "");
        assert_eq!(named(&fsproj, &plain), None, "{selector} at {site:?}");
    }
    for site in SITES {
        let dir = tempfile::tempdir().unwrap();
        let fsproj = project_defining(dir.path(), &compiler.sdk, site, "LangVersionNote", "");
        // A target body or a task output is build code, which may do anything.
        let build_code = matches!(site, Site::TargetBody | Site::TaskOutput);
        assert_eq!(
            named(&fsproj, &plain).as_ref(),
            (!build_code).then_some(&compiler.sdk),
            "a non-selector at {site:?}"
        );
    }
    for targets in [
        r#"<Target Name="CoreCompile" />"#,
        r#"<UsingTask TaskName="Fsc" AssemblyFile="/opt/My.Build.dll" />"#,
        r#"<UsingTask TaskName="Review.Fsc" AssemblyFile="/opt/My.Build.dll" Override="true" />"#,
        r#"<Target Name="Build"><Exec Command="dotnet /opt/fsc.dll" /></Target>"#,
        r#"<Target Name="Note" AfterTargets="Build"><Message Text="built" /></Target>"#,
        r#"<PropertyGroup><BuildDependsOn>Mine</BuildDependsOn></PropertyGroup>"#,
        r#"<Import Project="$(MSBuildToolsPath)/Microsoft.CSharp.targets" />"#,
        r#"<PropertyGroup><Selector>DotnetFscCompilerPath</Selector></PropertyGroup><Target Name="Pick" BeforeTargets="CoreCompile"><CreateProperty Value="x"><Output TaskParameter="Value" PropertyName="$(Selector)" /></CreateProperty></Target>"#,
    ] {
        let dir = tempfile::tempdir().unwrap();
        let fsproj = project_defining(
            dir.path(),
            &compiler.sdk,
            Site::Body,
            "LangVersionNote",
            targets,
        );
        assert_eq!(named(&fsproj, &plain), None, "{targets}");
    }
    let dir = tempfile::tempdir().unwrap();
    let fsproj = pinned_project(dir.path(), &compiler.sdk, None, STRADDLING);
    for selector in COMPILER_SELECTORS
        .iter()
        .filter(|s| !s.eq_ignore_ascii_case("DOTNET_HOST_PATH"))
    {
        let mut env = plain.clone();
        env.build_environment
            .insert(selector.to_string(), "/opt/elsewhere".to_string());
        assert_eq!(named(&fsproj, &env), None, "{selector} in the environment");
        let globals = HashMap::from([(selector.to_string(), "/opt/elsewhere".to_string())]);
        let mut workspace = Workspace::with_env_and_extra_build_properties(plain.clone(), globals);
        assert_eq!(
            workspace.compiler_sdk_for_project(&fsproj),
            None,
            "{selector} as a global"
        );
    }
    for variable in COMPILER_ENVIRONMENT {
        let mut env = plain.clone();
        env.build_environment
            .insert(variable.to_string(), "/opt/elsewhere".to_string());
        assert_eq!(named(&fsproj, &env), None, "{variable} in the environment");
    }
    let dir = tempfile::tempdir().unwrap();
    let redirected = pinned_project(dir.path(), &compiler.sdk, None, STRADDLING);
    let text = host_fs::read_to_string(&redirected).unwrap().replace(
        r#"<Project Sdk="Microsoft.NET.Sdk">"#,
        r#"<Project Sdk="Microsoft.NET.Sdk" DefaultTargets="Clean">"#,
    );
    assert!(text.contains("DefaultTargets"));
    std::fs::write(&redirected, text).unwrap();
    assert_eq!(
        named(&redirected, &plain),
        None,
        "a redirected default target"
    );
    let globals = HashMap::from([("BuildDependsOn".to_string(), "Clean".to_string())]);
    let mut workspace = Workspace::with_env_and_extra_build_properties(plain.clone(), globals);
    assert_eq!(
        workspace.compiler_sdk_for_project(&fsproj),
        None,
        "a target graph reshaped by a global"
    );
}

/// A target outside the SDK that may write `$(LangVersion)` before
/// `CoreCompile` reads it leaves the value the compiler is handed
/// unestablished: no refusal is reported, and the version is doubted.
#[test]
fn a_build_time_langversion_write_reports_no_refusal() {
    let compiler = graded_compilers()
        .into_iter()
        .find(|c| SdkLanguageFacts::for_sdk(&c.sdk).unwrap().floor > LanguageVersion::V7_0)
        .expect("an installed graded SDK with a floor above F# 7.0");
    let dir = tempfile::tempdir().unwrap();
    let fsproj = pinned_project(dir.path(), &compiler.sdk, Some("7.0"), STRADDLING);
    let text = host_fs::read_to_string(&fsproj).unwrap().replace(
        "</Project>",
        r#"<Target Name="Raise" BeforeTargets="CoreCompile"><PropertyGroup><LangVersion>8.0</LangVersion></PropertyGroup></Target></Project>"#,
    );
    std::fs::write(&fsproj, &text).unwrap();
    let (_, env, _) = environments().remove(0);
    let mut workspace = Workspace::with_env(env.clone());
    let parsed = workspace.project(&fsproj).unwrap();
    assert!(!parsed.property_provenance_untrusted("LangVersion"));
    assert!(borzoi::sdk_language::lang_version_untrusted_cause(parsed).is_some());
    let diags = borzoi::fsproj_diagnostics::diagnostics_for(
        &text,
        &fsproj,
        &env,
        &workspace.build_properties(),
    );
    assert!(
        diags
            .iter()
            .all(|d| d.code != Some(lsp_types::NumberOrString::String("FS3880".to_string()))),
        "{diags:#?}"
    );
    let mut sema = borzoi::semantic::SemanticState::new();
    let docs = borzoi::vfs::Vfs::new();
    assert!(
        sema.parses_for_project(&fsproj, &mut workspace, &docs)
            .is_none(),
        "the straddling file is refused under a doubted version"
    );
}

/// The SDK's files that choose its F# compiler: its F# props and targets, and
/// the .NET SDK's F# shims that import them.
fn compiler_choice_files(sdk_dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let fsharp = sdk_dir.join("FSharp");
    let shims = sdk_dir
        .join("Sdks")
        .join("Microsoft.NET.Sdk")
        .join("targets");
    for (dir, keep) in [
        (&fsharp, (|_: &str| true) as fn(&str) -> bool),
        (&shims, |name: &str| {
            name.starts_with("Microsoft.NET.Sdk.FSharp")
        }),
    ] {
        for entry in
            host_fs::read_dir(dir).unwrap_or_else(|e| panic!("list {}: {e}", dir.display()))
        {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            let lower = name.to_ascii_lowercase();
            if keep(&name) && (lower.ends_with(".props") || lower.ends_with(".targets")) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Every property the SDK's own files read in choosing the compiler a build
/// runs: the `Fsc` task's `ToolPath`, `ToolExe` and `DotnetFscCompilerPath`,
/// the assembly its `UsingTask` names, and, transitively, every property
/// read by a write (its value, its condition, its group's) of a name already
/// in the set. The names whose final value `project_compiler` checks directly
/// are kept but not followed: what feeds them cannot move the compiler without
/// moving their value.
fn compiler_choice_reads(sdk_dir: &Path) -> BTreeSet<String> {
    const CHECKED: &[&str] = &[
        "fsharppropsshim",
        "fsharptargetsshim",
        "usebundledfsharptargets",
    ];
    let texts: Vec<String> = compiler_choice_files(sdk_dir)
        .iter()
        .map(|f| host_fs::read_to_string(f).unwrap())
        .collect();
    let docs: Vec<roxmltree::Document<'_>> = texts
        .iter()
        .map(|t| roxmltree::Document::parse(t).expect("an SDK file parses"))
        .collect();
    let refs = |raw: &str| -> Vec<String> {
        borzoi_msbuild::test_support::property_references(raw)
            .into_iter()
            .map(str::to_ascii_lowercase)
            .collect()
    };
    let mut set = BTreeSet::new();
    let elements = || {
        docs.iter()
            .flat_map(|d| d.descendants().filter(|n| n.is_element()))
    };
    for node in elements() {
        let tag = node.tag_name().name();
        let attrs: &[&str] = match tag {
            "Fsc" => &[
                "ToolPath",
                "ToolExe",
                "DotnetFscCompilerPath",
                "SkipCompilerExecution",
            ],
            "Target" if node.attribute("Name") == Some("CoreCompile") => &["Condition"],
            "UsingTask" if node.attribute("TaskName") == Some("Fsc") => {
                &["AssemblyFile", "Condition"]
            }
            _ => &[],
        };
        for attr in attrs {
            set.extend(node.attribute(*attr).map(refs).unwrap_or_default());
        }
    }
    set.extend(CHECKED.iter().map(|s| s.to_string()));
    loop {
        let before = set.len();
        for node in elements() {
            let Some(group) = node.parent_element() else {
                continue;
            };
            let name = node.tag_name().name().to_ascii_lowercase();
            if group.tag_name().name() != "PropertyGroup"
                || !set.contains(&name)
                || CHECKED.contains(&name.as_str())
            {
                continue;
            }
            let text: String = node.descendants().filter_map(|n| n.text()).collect();
            for raw in [
                Some(text.as_str()),
                node.attribute("Condition"),
                group.attribute("Condition"),
            ]
            .into_iter()
            .flatten()
            {
                set.extend(refs(raw));
            }
        }
        if set.len() == before {
            return set;
        }
    }
}

/// [`COMPILER_SELECTORS`] covers every property each installed graded SDK reads
/// in choosing its compiler, but the names MSBuild reserves, which nothing
/// outside the SDK can set (`MSBuildThisFileDirectory` and the like).
#[test]
fn the_selectors_cover_what_each_sdk_reads_to_choose_its_compiler() {
    let selectors: BTreeSet<String> = COMPILER_SELECTORS
        .iter()
        .map(|s| s.to_ascii_lowercase())
        .collect();
    let mut missing = Vec::new();
    for compiler in graded_compilers() {
        let sdk_dir = compiler.fsc.parent().unwrap().parent().unwrap();
        let reads = compiler_choice_reads(sdk_dir);
        eprintln!("SDK {}: the compiler choice reads {reads:?}", compiler.sdk);
        for name in reads {
            if !selectors.contains(&name)
                && !borzoi_msbuild::test_support::is_msbuild_reserved_name(&name)
            {
                missing.push(format!("SDK {}: {name}", compiler.sdk));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "the SDK reads these in choosing its compiler, and COMPILER_SELECTORS lacks them:\n{}",
        missing.join("\n")
    );
}

/// A refusal read from an untrusted `$(LangVersion)` is not reported: the
/// value the build holds may be one the compiler takes. Here the evaluation
/// keeps `7.0`, below the floor, but cannot decide the gate on the `8.0`
/// write after it.
#[test]
fn an_untrusted_langversion_reports_no_refusal() {
    let compiler = graded_compilers()
        .into_iter()
        .find(|c| SdkLanguageFacts::for_sdk(&c.sdk).unwrap().floor > LanguageVersion::V7_0)
        .expect("an installed graded SDK with a floor above F# 7.0");
    let dir = tempfile::tempdir().unwrap();
    let fsproj = pinned_project(dir.path(), &compiler.sdk, Some("7.0"), STRADDLING);
    let text = host_fs::read_to_string(&fsproj).unwrap();
    let text = text.replace(
        "</PropertyGroup>",
        r#"</PropertyGroup><PropertyGroup Condition="'$([System.Guid]::NewGuid())' == ''"><LangVersion>8.0</LangVersion></PropertyGroup>"#,
    );
    std::fs::write(&fsproj, &text).unwrap();
    let (_, env, _) = environments().remove(0);
    let mut workspace = Workspace::with_env(env.clone());
    let parsed = workspace.project(&fsproj).unwrap();
    assert!(parsed.property_provenance_untrusted("LangVersion"));
    assert_eq!(parsed.lang_version.as_deref(), Some("7.0"));
    assert!(
        workspace.lang_version_selection(&fsproj).refusal.is_some(),
        "the best guess is below the floor"
    );
    let diags = borzoi::fsproj_diagnostics::diagnostics_for(
        &text,
        &fsproj,
        &env,
        &workspace.build_properties(),
    );
    assert!(
        diags
            .iter()
            .all(|d| d.code != Some(lsp_types::NumberOrString::String("FS3880".to_string()))),
        "{diags:#?}"
    );
}

/// The environment-variable-shaped strings in `dll`'s UTF-16 literals, at
/// either byte alignment (a user-string heap entry starts wherever its length
/// prefix ends).
fn variable_literals(dll: &Path) -> BTreeSet<String> {
    let bytes = host_fs::read(dll).unwrap_or_else(|e| panic!("read {}: {e}", dll.display()));
    let shaped = |s: &str| {
        s.len() >= 4
            && s.starts_with(|c: char| c.is_ascii_uppercase())
            && s.contains('_')
            && !s.starts_with('_')
            && !s.ends_with('_')
            && !s.contains("__")
    };
    let mut found = BTreeSet::new();
    for offset in [0, 1] {
        let mut run = String::new();
        for pair in bytes[offset..].as_chunks::<2>().0 {
            let c = (pair[1] == 0)
                .then_some(pair[0] as char)
                .filter(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || *c == '_');
            match c {
                Some(c) => run.push(c),
                None => {
                    if shaped(&run) {
                        found.insert(std::mem::take(&mut run));
                    }
                    run.clear();
                }
            }
        }
    }
    found
}

/// The variable-shaped strings in `FSharp.Build.dll` that choose no compiler.
const NOT_COMPILER_CHOICE: &[(&str, &str)] = &[
    (
        "DOTNET_HOST_PATH",
        "the shared host discovery, which finds a `dotnet` to run a compiler; the \
         props' read of it is a selector",
    ),
    ("DOTNET_MULTILEVEL_LOOKUP", "the same host discovery"),
    ("VS_VERSION_INFO", "the Win32 version resource's name"),
    (
        "BUILDING_WITH_LKG",
        "a preprocessor symbol in the source `FSharpEmbedResourceText` generates",
    ),
];

/// Every variable the SDK's `Fsc` task could read is accounted for: each
/// variable-shaped literal in each graded SDK's `FSharp.Build.dll` is in
/// [`COMPILER_ENVIRONMENT`] or known to choose no compiler, and each entry of
/// [`COMPILER_ENVIRONMENT`] is still read.
#[test]
fn every_variable_the_compile_task_reads_is_accounted_for() {
    let mut failures = Vec::new();
    for compiler in graded_compilers() {
        let literals = variable_literals(&compiler.fsc.with_file_name("FSharp.Build.dll"));
        eprintln!("SDK {}: FSharp.Build.dll names {literals:?}", compiler.sdk);
        for literal in &literals {
            let known = COMPILER_ENVIRONMENT.contains(&literal.as_str())
                || NOT_COMPILER_CHOICE.iter().any(|(name, _)| name == literal);
            if !known {
                failures.push(format!(
                    "SDK {}: FSharp.Build.dll names {literal}, which may choose the compiler: \
                     add it to COMPILER_ENVIRONMENT, or to NOT_COMPILER_CHOICE with the reason",
                    compiler.sdk
                ));
            }
        }
        for variable in COMPILER_ENVIRONMENT {
            if !literals.contains(*variable) {
                failures.push(format!(
                    "SDK {}: FSharp.Build.dll no longer names {variable}",
                    compiler.sdk
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The version the compiler is handed is read from the effective values, so
/// a global `LangVersion=?` (the compiler's version query) and a global
/// `OtherFlags` naming a version report no refusal either.
#[test]
fn a_global_carrier_reports_no_refusal() {
    let compiler = graded_compilers()
        .into_iter()
        .find(|c| SdkLanguageFacts::for_sdk(&c.sdk).unwrap().floor > LanguageVersion::V7_0)
        .expect("an installed graded SDK with a floor above F# 7.0");
    let (_, env, _) = environments().remove(0);
    for (project_lang, global, value) in [
        (None, "LangVersion", "?"),
        (Some("7.0"), "OtherFlags", "--langversion:8.0"),
    ] {
        let dir = tempfile::tempdir().unwrap();
        let fsproj = pinned_project(dir.path(), &compiler.sdk, project_lang, STRADDLING);
        let globals = HashMap::from([(global.to_string(), value.to_string())]);
        let workspace = Workspace::with_env_and_extra_build_properties(env.clone(), globals);
        let text = host_fs::read_to_string(&fsproj).unwrap();
        let diags = borzoi::fsproj_diagnostics::diagnostics_for(
            &text,
            &fsproj,
            &env,
            &workspace.build_properties(),
        );
        assert!(
            diags.iter().all(|d| !matches!(
                &d.code,
                Some(lsp_types::NumberOrString::String(code)) if code == "FS0246" || code == "FS3880"
            )),
            "{global}={value}: {diags:#?}"
        );
    }
}
