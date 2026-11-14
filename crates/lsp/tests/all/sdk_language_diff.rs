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

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use borzoi::sdk_discovery::SdkDiscoveryEnv;
use borzoi::sdk_language::{
    LangVersionReading, LangVersionSelection, RefusalKind, SdkLanguageFacts,
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
    let mut cmd = Command::new("dotnet");
    cmd.arg("exec")
        .arg(&compiler.fsc)
        .arg("--nologo")
        .args(args);
    if skip {
        cmd.env("SKIP_VERSION_SUPPORTED_CHECK", "1");
    } else {
        cmd.env_remove("SKIP_VERSION_SUPPORTED_CHECK");
    }
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

/// The environments a project is evaluated under: the test's own, where the
/// compiler is the one beside the F# props the SDK imports, and one with
/// `DOTNET_HOST_PATH` set, as `dotnet build` sets it, where the SDK writes
/// `$(DotnetFscCompilerPath)` and that decides.
fn environments() -> Vec<(&'static str, SdkDiscoveryEnv)> {
    let plain = SdkDiscoveryEnv::from_process_env();
    let mut hosted = plain.clone();
    hosted.build_environment.insert(
        "DOTNET_HOST_PATH".to_string(),
        dotnet_root().join("dotnet").display().to_string(),
    );
    vec![("props shim", plain), ("DotnetFscCompilerPath", hosted)]
}

#[test]
fn a_project_reads_langversion_with_its_sdks_compiler() {
    let mut graded = 0;
    for compiler in installed_compilers() {
        if compiler.sdk.is_prerelease() {
            continue;
        }
        for (lang, (route, env)) in [None, Some("7.0"), Some("11")]
            .into_iter()
            .flat_map(|lang| environments().into_iter().map(move |env| (lang, env)))
        {
            let dir = tempfile::tempdir().unwrap();
            let fsproj = pinned_project(dir.path(), &compiler.sdk, lang, STRADDLING);
            let mut workspace = Workspace::with_env(env.clone());
            assert_eq!(
                workspace.compiler_sdk_for_project(&fsproj).as_ref(),
                Some(&compiler.sdk),
                "a project pinned to SDK {} builds with its compiler ({route})",
                compiler.sdk
            );
            let selection = workspace.lang_version_selection(&fsproj);
            let Some(facts) = SdkLanguageFacts::for_sdk(&compiler.sdk) else {
                assert_eq!(selection.refusal, None, "no floor for an SDK with no row");
                continue;
            };
            graded += 1;
            let expected = match facts.reading(lang) {
                LangVersionReading::Checks(v) => (v, None),
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
                "SDK {}, LangVersion {lang:?}",
                compiler.sdk
            );
            assert_eq!(
                selection,
                LangVersionSelection::of(workspace.project(&fsproj).unwrap(), Some(&compiler.sdk))
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
