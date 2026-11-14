//! What the F# compiler a project builds with makes of its `<LangVersion>`.
//!
//! The compiler that checks an SDK project is, by default, the `fsc.dll` in
//! the .NET SDK the project resolves (honouring `global.json`, through
//! [`SdkDiscovery`]): `Microsoft.FSharp.NetSdk.props` points
//! `$(DotnetFscCompilerPath)` at the one beside itself, `<root>/sdk/<version>/FSharp/fsc.dll`.
//! [`project_compiler`] names that SDK, and declines wherever something outside
//! the SDK could choose another compiler. Four facts about `<LangVersion>` vary
//! by compiler:
//!
//! - the version an absent `<LangVersion>` (or `default`) selects;
//! - the versions `latest` and `latestmajor` spell;
//! - the newest numbered version it recognises (a newer one is FS0246);
//! - the oldest it supports (an older one is FS3880). This varies within a
//!   major: SDK 10.0.112's compiler checks at 4.6, SDK 10.0.401's refuses
//!   everything below 8.0.
//!
//! [`SdkLanguageFacts::for_sdk`] holds them per SDK feature band, and only for
//! bands a compiler has graded: `tests/all/sdk_language_diff.rs` runs every
//! installed SDK's `fsc.dll` over every `<LangVersion>` spelling and holds each
//! row to it exactly, and fails on a row no installed SDK grades. Any other
//! SDK — unknown, prerelease, or unresolved — gets no row, and the reading
//! falls back to the pinned compiler's
//! ([`LanguageVersion::from_lang_version_text`], [`LanguageVersion::DEFAULT`])
//! with no floor: claiming an unknown compiler refuses a version would report a
//! build failure that may not happen.
//!
//! The floor is also what #732 needs: a guessed version's invariance check
//! may narrow its ladder to [`SdkLanguageFacts::floor`] only for an SDK that
//! has a row, since a row's floor is graded and no row means the full ladder.
//!
//! [`SdkDiscovery`]: crate::sdk_discovery::SdkDiscovery

use std::collections::HashMap;

use borzoi_cst::language_version::LanguageVersion;
use borzoi_msbuild::{ParsedProject, SdkVersion, UntrustedCause};

/// One SDK's F# compiler, as far as `<LangVersion>` goes. See the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SdkLanguageFacts {
    /// What an absent `<LangVersion>`, or `default`, selects.
    pub default: LanguageVersion,
    /// What `latest` selects.
    pub latest: LanguageVersion,
    /// What `latestmajor` selects.
    pub latest_major: LanguageVersion,
    /// The newest numbered version the compiler recognises. A newer one is
    /// FS0246 ("Unrecognized value").
    pub newest: LanguageVersion,
    /// The oldest version the compiler supports. An older one, though
    /// recognised, is FS3880 ("out of support").
    /// [`LanguageVersion::MIN`] for a compiler that supports every version
    /// it recognises.
    pub floor: LanguageVersion,
}

/// What one compiler does with one `<LangVersion>` value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LangVersionReading {
    /// It checks the project at this version.
    Checks(LanguageVersion),
    /// It recognises this version but refuses to check at it (FS3880).
    OutOfSupport(LanguageVersion),
    /// It does not recognise the value (FS0246).
    Unrecognised,
}

/// A feature band (`major.minor.Nxx`) and its compiler's facts.
struct BandRow {
    major: u64,
    minor: u64,
    band: u64,
    facts: SdkLanguageFacts,
}

/// Every band whose compiler `tests/all/sdk_language_diff.rs` grades. A band
/// leaves this table when no installed SDK grades it any more: an ungraded
/// row is a claim about a compiler nothing has run.
const BANDS: &[BandRow] = &[
    BandRow {
        major: 10,
        minor: 0,
        band: 1,
        facts: SdkLanguageFacts {
            default: LanguageVersion::V10_0,
            latest: LanguageVersion::V10_0,
            latest_major: LanguageVersion::V10_0,
            newest: LanguageVersion::V10_0,
            floor: LanguageVersion::V4_6,
        },
    },
    BandRow {
        major: 10,
        minor: 0,
        band: 4,
        facts: SdkLanguageFacts {
            default: LanguageVersion::V10_0,
            latest: LanguageVersion::V10_0,
            latest_major: LanguageVersion::V10_0,
            newest: LanguageVersion::V11_0,
            floor: LanguageVersion::V8_0,
        },
    },
];

impl SdkLanguageFacts {
    /// The facts for the compiler `sdk` ships, or `None` when its band has no
    /// graded row. A prerelease SDK never has one: its compiler is not the
    /// band's release compiler.
    pub fn for_sdk(sdk: &SdkVersion) -> Option<&'static SdkLanguageFacts> {
        if sdk.is_prerelease() {
            return None;
        }
        BANDS
            .iter()
            .find(|row| {
                row.major == sdk.major()
                    && row.minor == sdk.minor()
                    && row.band == sdk.feature_band()
            })
            .map(|row| &row.facts)
    }

    /// The feature bands with a row, as `major.minor.Nxx`, for the grading
    /// differential to account for.
    pub fn graded_bands() -> impl Iterator<Item = (u64, u64, u64)> {
        BANDS.iter().map(|row| (row.major, row.minor, row.band))
    }

    /// What this compiler does with `lang_version`, the evaluated
    /// `$(LangVersion)` (`None` when unset). Case-insensitive, as the
    /// compiler is.
    pub fn reading(&self, lang_version: Option<&str>) -> LangVersionReading {
        let Some(text) = lang_version else {
            return LangVersionReading::Checks(self.default);
        };
        let version = match text.to_ascii_uppercase().as_str() {
            "DEFAULT" => return LangVersionReading::Checks(self.default),
            "LATEST" => return LangVersionReading::Checks(self.latest),
            "LATESTMAJOR" => return LangVersionReading::Checks(self.latest_major),
            _ => match LanguageVersion::from_lang_version_text(text) {
                Some(version) => version,
                None => return LangVersionReading::Unrecognised,
            },
        };
        if version == LanguageVersion::Preview {
            LangVersionReading::Checks(version)
        } else if version > self.newest {
            LangVersionReading::Unrecognised
        } else if version < self.floor {
            LangVersionReading::OutOfSupport(version)
        } else {
            LangVersionReading::Checks(version)
        }
    }
}

/// The properties the F# SDK reads in choosing the compiler a build runs:
/// which F# props and targets the SDK imports, which assembly's `Fsc` task
/// runs, and the tool path, executable and compiler path that task is handed.
/// Inside the SDK only its own F# files write any of them (`sdk_language_diff`
/// derives the set from each installed SDK's files and fails on a name missing
/// here).
pub const COMPILER_SELECTORS: &[&str] = &[
    "DotnetFscCompilerPath",
    "DisableAutoSetFscCompilerPath",
    "FscToolPath",
    "FscToolExe",
    "DOTNET_HOST_PATH",
    "FSharp_Shim_Present",
    "FSharpPreferNetFrameworkTools",
    "FSharpPreferAnyCpuTools",
    "FSharpPrefer64BitTools",
    "Fsc_Dotnet_ToolPath",
    "Fsc_Dotnet_ToolExe",
    "Fsc_Dotnet_DotnetFscCompilerPath",
    "Fsc_NetFramework_ToolPath",
    "Fsc_NetFramework_AnyCpu_ToolExe",
    "Fsc_NetFramework_PlatformSpecific_ToolExe",
    "FSharpBuildAssemblyFile",
    "UseBundledFSharpTargets",
    "FSharpPropsShim",
    "FSharpTargetsShim",
    // Gates the import of `$(FSharpTargetsShim)`.
    "IsCrossTargetingBuild",
    "SkipCompilerExecution",
];

/// The environment variables the SDK's `Fsc` task reads itself in locating its
/// compiler when it is handed no compiler path (`FSHARP_COMPILER_BIN` names
/// the directory instead of the task's own). `sdk_language_diff` reads every
/// variable-shaped string in each installed SDK's `FSharp.Build.dll` and fails
/// on one neither here nor known to choose something else.
pub const COMPILER_ENVIRONMENT: &[&str] = &["FSHARP_COMPILER_BIN"];

/// The suffix of the properties a target's `DependsOnTargets` reads by
/// convention (`BuildDependsOn`, `CoreCompileDependsOn`, …): a write of one
/// reshapes which targets run.
const TARGET_GRAPH_SUFFIX: &str = "dependson";

/// The target that runs the `Fsc` task, and the task.
const COMPILE_TARGET: &str = "CoreCompile";
const COMPILE_TASK: &str = "Fsc";

/// The compiler that builds a project, as far as reading its `<LangVersion>`
/// goes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectCompiler {
    /// The SDK whose `FSharp/fsc.dll` it is.
    pub sdk: SdkVersion,
    /// The build's environment sets `SKIP_VERSION_SUPPORTED_CHECK` to `1`,
    /// under which the compiler checks below its floor rather than refusing
    /// (FS3880).
    pub support_check_skipped: bool,
}

/// Whether `environment` lifts the compiler's support floor. The compiler reads
/// the variable itself (`LanguageVersion.IsVersionSupported`) and lifts the
/// floor for the value `1` exactly; a build hands its environment to the
/// compiler it spawns.
pub fn support_check_skipped(environment: &HashMap<String, String>) -> bool {
    const NAME: &str = "SKIP_VERSION_SUPPORTED_CHECK";
    environment.iter().any(|(name, value)| {
        let named = if cfg!(windows) {
            name.eq_ignore_ascii_case(NAME)
        } else {
            name == NAME
        };
        named && value == "1"
    })
}

/// The compiler that builds `parsed`, evaluated under `environment` (the
/// process environment its evaluation saw) and the global properties
/// `globals`, or `None` when it cannot be said.
///
/// The claim is that it is the entry SDK's own `fsc.dll`, and it rests on
/// what the build cannot be told rather than on what the evaluation computed:
///
/// - Inside the SDK, the choice of compiler is made by its F# props and
///   targets alone. They choose between `dotnet <sdk>/FSharp/fsc.dll` (when
///   `DOTNET_HOST_PATH` is set, as `dotnet build` sets it) and the compiler
///   beside the SDK's own `Fsc` task assembly, the same file; the evaluation
///   cannot decide that gate (it does not model `DOTNET_HOST_PATH`), and need
///   not. `sdk_language_diff` grades both arms against each installed SDK.
/// - So the build runs another compiler, or none, only if something outside
///   the SDK chooses: defines one of [`COMPILER_SELECTORS`], runs build code of
///   its own (any target or task: a replaced `Build` or `CoreCompile`, or a
///   target that rewrites a selector, may do anything), reshapes the target
///   graph (a `…DependsOn` property), sets a selector in the environment or as
///   a global, or sets one of [`COMPILER_ENVIRONMENT`], which the task reads
///   itself. A definition anywhere in a document the walk entered outside the
///   SDK declines, whatever its condition, and so does one whose name the build
///   computes ([`ParsedProject::foreign_definitions`]), and any content the
///   walk did not enter ([`ParsedProject::hidden_content`]).
/// - The SDK must be the canonical layout with a graded row
///   ([`SdkLanguageFacts::for_sdk`]): the argument above is about its files,
///   and only a graded SDK's files have been checked. Its F# props and targets
///   (`$(FSharpPropsShim)`, `$(FSharpTargetsShim)`, imported under
///   `$(UseBundledFSharpTargets)` = `true`) must be its own, and trusted.
///
/// `DOTNET_HOST_PATH` in the environment is not a selector: the `dotnet` host
/// sets it for the build whatever the caller's value.
pub fn project_compiler(
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
) -> Option<ProjectCompiler> {
    let is_selector = |name: &str| {
        COMPILER_SELECTORS
            .iter()
            .any(|selector| name.eq_ignore_ascii_case(selector))
    };
    let set_in_environment = environment.iter().any(|(name, value)| {
        !value.is_empty()
            && ((!name.eq_ignore_ascii_case("DOTNET_HOST_PATH") && is_selector(name))
                || COMPILER_ENVIRONMENT
                    .iter()
                    .any(|variable| name.eq_ignore_ascii_case(variable)))
    });
    let set_globally = globals.keys().any(|name| is_selector(name));
    if set_in_environment || set_globally || parsed.hidden_content.is_some() {
        return None;
    }
    let chooses = |defined: &borzoi_msbuild::ForeignDefinitions| {
        COMPILER_SELECTORS
            .iter()
            .any(|name| defined.defines_property(name))
            || defined.defines_property_where(|name| name.ends_with(TARGET_GRAPH_SUFFIX))
            || defined.defines_target(COMPILE_TARGET)
            || defined.defines_task(COMPILE_TASK)
    };
    // A workload manifest is the install's own build code, held to what it
    // touches; anything else outside the SDK may not run build code at all.
    let foreign = &parsed.foreign_definitions;
    if chooses(foreign) || foreign.defines_build_code() || chooses(&parsed.workload_definitions) {
        return None;
    }
    let sdk = entry_sdk_version(parsed.resolved_sdk_root.as_deref()?)?;
    SdkLanguageFacts::for_sdk(&sdk)?;
    let written = |name: &str| {
        parsed
            .properties
            .iter()
            .find(|(written, _)| written.eq_ignore_ascii_case(name))
            .map(|(_, value)| value.as_str())
    };
    let trusted = |name: &str| {
        if parsed.property_provenance_untrusted(name) {
            None
        } else {
            written(name)
        }
    };
    let names_own = |name: &str, file: &str| {
        trusted(name).and_then(|value| sdk_version_of_sdk_file(value, &["FSharp", file]))
            == Some(sdk.clone())
    };
    let bundled = trusted("UseBundledFSharpTargets")
        .is_some_and(|value| value.trim().eq_ignore_ascii_case("true"));
    if !bundled
        || !names_own("FSharpPropsShim", "Microsoft.FSharp.NetSdk.props")
        || !names_own("FSharpTargetsShim", "Microsoft.FSharp.NetSdk.targets")
    {
        return None;
    }
    // Only the SDK's props can have written it, and they name their own.
    if written("DotnetFscCompilerPath").is_some() && !names_own("DotnetFscCompilerPath", "fsc.dll")
    {
        return None;
    }
    Some(ProjectCompiler {
        sdk,
        support_check_skipped: support_check_skipped(environment),
    })
}

/// The version of the canonical-layout SDK `root` (`…/sdk/<version>/Sdks/<name>/Sdk`).
fn entry_sdk_version(root: &std::path::Path) -> Option<SdkVersion> {
    let mut components = root.components().rev().map(|c| c.as_os_str().to_str());
    let mut next = || components.next().flatten();
    if !next()?.eq_ignore_ascii_case("Sdk") {
        return None;
    }
    next()?;
    if !next()?.eq_ignore_ascii_case("Sdks") {
        return None;
    }
    let version = next()?;
    if !next()?.eq_ignore_ascii_case("sdk") {
        return None;
    }
    SdkVersion::parse(version)
}

/// The version of the SDK whose own file `value` names: a path
/// `<root>/sdk/<version>/<tail…>`, in either separator, optionally in the
/// double quotes the SDK writes `DotnetFscCompilerPath` with. `None` for any
/// other shape.
pub fn sdk_version_of_sdk_file(value: &str, tail: &[&str]) -> Option<SdkVersion> {
    let trimmed = value.trim();
    let unquoted = trimmed
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .unwrap_or(trimmed);
    let mut components = unquoted
        .split(['/', '\\'])
        .filter(|c| !c.is_empty() && *c != ".")
        .rev();
    for expected in tail.iter().rev() {
        if components.next()? != *expected {
            return None;
        }
    }
    let version = components.next()?;
    if components.next()? != "sdk" {
        return None;
    }
    SdkVersion::parse(version)
}

/// Why the compiler will not build a project at its `<LangVersion>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LangVersionRefusal {
    /// The SDK whose compiler refuses.
    pub sdk: SdkVersion,
    /// The evaluated `$(LangVersion)`.
    pub text: String,
    /// How it refuses.
    pub kind: RefusalKind,
}

/// How a compiler refuses a `<LangVersion>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefusalKind {
    /// FS3880: the version is older than `floor`, the oldest it supports.
    OutOfSupport { floor: LanguageVersion },
    /// FS0246: the compiler does not recognise the value.
    Unrecognised,
}

impl LangVersionRefusal {
    /// The compiler's error number.
    pub fn code(&self) -> &'static str {
        match self.kind {
            RefusalKind::OutOfSupport { .. } => "FS3880",
            RefusalKind::Unrecognised => "FS0246",
        }
    }

    /// The refusal, worded for the user.
    pub fn message(&self) -> String {
        match self.kind {
            RefusalKind::OutOfSupport { floor } => format!(
                "{}: language version '{}' is out of support: the F# compiler in .NET SDK {} \
                 refuses to build below F# {floor}",
                self.code(),
                self.text,
                self.sdk,
            ),
            RefusalKind::Unrecognised => format!(
                "{}: the F# compiler in .NET SDK {} does not recognise language version '{}'",
                self.code(),
                self.sdk,
                self.text,
            ),
        }
    }
}

/// The language version a project's files parse at, and whether that version
/// is one the real build checks at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LangVersionSelection {
    /// The version every Compile item parses at. Under a refusal it is the
    /// best guess: the version the text names, or the compiler's default.
    pub version: LanguageVersion,
    /// Set when the project's compiler is known and refuses to build at its
    /// `<LangVersion>`, so no version is the one the build checks at.
    pub refusal: Option<LangVersionRefusal>,
}

impl LangVersionSelection {
    /// The selection for `parsed`, built by `compiler` ([`project_compiler`]'s
    /// answer): that compiler's reading of its `$(LangVersion)` when its SDK
    /// has a graded row, else the pinned compiler's.
    pub fn of(parsed: &ParsedProject, compiler: Option<&ProjectCompiler>) -> LangVersionSelection {
        let text = parsed.lang_version.as_deref();
        let Some((compiler, facts)) =
            compiler.and_then(|c| SdkLanguageFacts::for_sdk(&c.sdk).map(|f| (c, f)))
        else {
            return LangVersionSelection {
                version: text
                    .map_or(Some(LanguageVersion::DEFAULT), |text| {
                        LanguageVersion::from_lang_version_text(text)
                    })
                    .unwrap_or(LanguageVersion::DEFAULT),
                refusal: None,
            };
        };
        let refusal = |kind| {
            Some(LangVersionRefusal {
                sdk: compiler.sdk.clone(),
                text: text.unwrap_or_default().to_string(),
                kind,
            })
        };
        match facts.reading(text) {
            LangVersionReading::Checks(version) => LangVersionSelection {
                version,
                refusal: None,
            },
            LangVersionReading::OutOfSupport(version) if compiler.support_check_skipped => {
                LangVersionSelection {
                    version,
                    refusal: None,
                }
            }
            LangVersionReading::OutOfSupport(version) => LangVersionSelection {
                version,
                refusal: refusal(RefusalKind::OutOfSupport { floor: facts.floor }),
            },
            LangVersionReading::Unrecognised => LangVersionSelection {
                version: text
                    .and_then(LanguageVersion::from_lang_version_text)
                    .unwrap_or(facts.default),
                refusal: refusal(RefusalKind::Unrecognised),
            },
        }
    }
}

/// Why the version a project's files parse at may not be the version its build
/// checks at. Wherever one is set, a file whose parse depends on the version
/// is read only as far as the version cannot matter: the fold refuses a file
/// whose tree differs across the version ladder, and a file's recovery is
/// proven only where its diagnostics agree across it
/// (`SyntaxRecovery::of_guessed_version`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LangVersionDoubt {
    /// The value the compiler is handed is not established
    /// ([`lang_version_untrusted_cause`]).
    Provenance(UntrustedCause),
    /// The project's compiler refuses its `<LangVersion>`, so the build checks
    /// at no version.
    Refused(LangVersionRefusal),
}

impl LangVersionDoubt {
    /// The doubt over `parsed`'s language version, if any. Untrusted
    /// provenance comes first: a refusal read from an untrusted value is
    /// itself a guess.
    pub fn of(parsed: &ParsedProject, selection: &LangVersionSelection) -> Option<Self> {
        if let Some(cause) = lang_version_untrusted_cause(parsed) {
            return Some(LangVersionDoubt::Provenance(cause));
        }
        selection.refusal.clone().map(LangVersionDoubt::Refused)
    }
}

/// The properties `CoreCompile` hands the compiler its language version
/// through: `$(LangVersion)`, and `$(OtherFlags)` (as `$(FscOtherFlags)`),
/// appended after it, where a `--langversion` or a response file overrides it.
const LANG_VERSION_CARRIERS: [&str; 3] = ["LangVersion", "OtherFlags", "FscOtherFlags"];

/// Why the evaluated `$(LangVersion)` may not be the version the compiler is
/// handed, or `None` when it is. The compiler takes what `CoreCompile` reads at
/// build time, so besides an untrusted evaluation, a target outside the SDK
/// that may write one of [`LANG_VERSION_CARRIERS`] ([`ForeignDefinitions`]),
/// content the walk did not enter (which may hold such a target), and
/// `$(OtherFlags)` that may name a version (`langversion`, or an `@` response
/// file) leave it unestablished. The SDK writes `LangVersion` only at
/// evaluation.
///
/// [`ForeignDefinitions`]: borzoi_msbuild::ForeignDefinitions
pub fn lang_version_untrusted_cause(parsed: &ParsedProject) -> Option<UntrustedCause> {
    for carrier in ["LangVersion", "OtherFlags"] {
        if let Some(cause) = parsed.property_untrusted_cause(carrier) {
            return Some(cause.clone());
        }
    }
    if let Some(carrier) = LANG_VERSION_CARRIERS.iter().find(|carrier| {
        [&parsed.foreign_definitions, &parsed.workload_definitions]
            .iter()
            .any(|defined| defined.writes_property_at_build_time(carrier))
    }) {
        return Some(UntrustedCause::Unentered(format!(
            "a target that may write `{carrier}` before `CoreCompile` reads it"
        )));
    }
    let other_flags = parsed
        .properties
        .iter()
        .find(|(name, _)| name.eq_ignore_ascii_case("OtherFlags"))
        .map(|(_, value)| value.to_ascii_lowercase())
        .unwrap_or_default();
    if other_flags.contains("langversion") || other_flags.contains('@') {
        return Some(UntrustedCause::Unentered(
            "`$(OtherFlags)`, which may name a language version after `$(LangVersion)`".to_string(),
        ));
    }
    parsed.hidden_content.clone()
}

#[cfg(test)]
mod tests {
    use super::LanguageVersion::*;
    use super::*;

    fn sdk(text: &str) -> SdkVersion {
        SdkVersion::parse(text).expect("an SDK version")
    }

    #[test]
    fn a_band_row_covers_every_patch_and_nothing_else() {
        let ten_one = SdkLanguageFacts::for_sdk(&sdk("10.0.112")).expect("10.0.1xx");
        assert_eq!(SdkLanguageFacts::for_sdk(&sdk("10.0.100")), Some(ten_one));
        assert_eq!(SdkLanguageFacts::for_sdk(&sdk("10.0.199")), Some(ten_one));
        assert_eq!(ten_one.floor, V4_6);
        let ten_four = SdkLanguageFacts::for_sdk(&sdk("10.0.401")).expect("10.0.4xx");
        assert_eq!(ten_four.floor, V8_0);
        for unknown in [
            "10.0.200", "10.0.300", "10.0.500", "9.0.100", "11.0.100", "10.1.100",
        ] {
            assert_eq!(SdkLanguageFacts::for_sdk(&sdk(unknown)), None, "{unknown}");
        }
    }

    #[test]
    fn a_prerelease_sdk_has_no_row() {
        assert_eq!(
            SdkLanguageFacts::for_sdk(&sdk("10.0.100-rc.2.25502.107")),
            None
        );
    }

    #[test]
    fn the_reading_spells_the_aliases_and_bounds_the_numbers() {
        let facts = SdkLanguageFacts::for_sdk(&sdk("10.0.401")).unwrap();
        use LangVersionReading::*;
        assert_eq!(facts.reading(None), Checks(V10_0));
        assert_eq!(facts.reading(Some("LatestMajor")), Checks(V10_0));
        assert_eq!(facts.reading(Some("preview")), Checks(Preview));
        assert_eq!(facts.reading(Some("11")), Checks(V11_0));
        assert_eq!(facts.reading(Some("8.0")), Checks(V8_0));
        assert_eq!(facts.reading(Some("7.0")), OutOfSupport(V7_0));
        assert_eq!(facts.reading(Some("4.6")), OutOfSupport(V4_6));
        assert_eq!(facts.reading(Some("11.2")), Unrecognised);
        assert_eq!(facts.reading(Some("bogus")), Unrecognised);
        let older = SdkLanguageFacts::for_sdk(&sdk("10.0.112")).unwrap();
        assert_eq!(older.reading(Some("4.6")), Checks(V4_6));
        assert_eq!(older.reading(Some("11.0")), Unrecognised);
    }

    #[test]
    fn the_compiler_sdk_is_the_version_directory_of_its_fsc() {
        let fsc = |path| sdk_version_of_sdk_file(path, &["FSharp", "fsc.dll"]);
        assert_eq!(
            sdk_version_of_sdk_file(
                r"C:\dotnet\sdk\10.0.401\FSharp\Microsoft.FSharp.NetSdk.props",
                &["FSharp", "Microsoft.FSharp.NetSdk.props"],
            ),
            Some(sdk("10.0.401"))
        );
        assert_eq!(
            fsc(r#""/usr/share/dotnet/sdk/10.0.401/FSharp/fsc.dll""#),
            Some(sdk("10.0.401"))
        );
        assert_eq!(
            fsc("/usr/share/dotnet/sdk/10.0.112/FSharp/fsc.dll"),
            Some(sdk("10.0.112"))
        );
        for other in [
            "/home/u/.nuget/packages/fsharp.compiler/1.0.0/tools/fsc.dll",
            "/usr/share/dotnet/sdk/10.0.401/FSharp/fsi.dll",
            "/usr/share/dotnet/sdk/10.0.401/fsc.dll",
            "/opt/fsharp/10.0.401/FSharp/fsc.dll",
            "/usr/share/dotnet/sdk/not-a-version/FSharp/fsc.dll",
            "",
        ] {
            assert_eq!(fsc(other), None, "{other}");
        }
    }

    fn evaluate(body: &str) -> ParsedProject {
        borzoi_msbuild::parse_fsproj(
            &format!("<Project><PropertyGroup>{body}</PropertyGroup></Project>"),
            std::path::Path::new("/w/App.fsproj"),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("the project evaluates")
    }

    /// An evaluation of an ordinary project on the canonical-layout SDK
    /// `version`: what the evaluator reports for one, with nothing defined
    /// outside the SDK.
    fn on_sdk(version: &str) -> ParsedProject {
        let mut parsed = evaluate("");
        let root = format!("/d/sdk/{version}");
        parsed.resolved_sdk_root = Some(format!("{root}/Sdks/Microsoft.NET.Sdk/Sdk").into());
        for (name, value) in [
            ("UseBundledFSharpTargets", "true".to_string()),
            (
                "FSharpPropsShim",
                format!(r"{root}\FSharp\Microsoft.FSharp.NetSdk.props"),
            ),
            (
                "FSharpTargetsShim",
                format!(r"{root}\FSharp\Microsoft.FSharp.NetSdk.targets"),
            ),
        ] {
            parsed.properties.insert(name.to_string(), value);
        }
        assert_eq!(parsed.foreign_definitions, Default::default());
        parsed
    }

    fn compiler_of(parsed: &ParsedProject, environment: &[(&str, &str)]) -> Option<SdkVersion> {
        let environment = environment
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
        project_compiler(parsed, &environment, &HashMap::new()).map(|c| c.sdk)
    }

    /// The compiler is the entry SDK's own while nothing outside the SDK can
    /// choose another, and each way something could declines.
    #[test]
    fn the_compiler_is_the_sdk_s_own_unless_something_outside_it_chooses() {
        let ten_four = Some(sdk("10.0.401"));
        assert_eq!(compiler_of(&on_sdk("10.0.401"), &[]), ten_four);
        assert_eq!(compiler_of(&on_sdk("10.0.112"), &[]), Some(sdk("10.0.112")));
        // An SDK whose files no compiler in the table grades.
        assert_eq!(compiler_of(&on_sdk("9.0.100"), &[]), None);
        assert_eq!(compiler_of(&on_sdk("10.0.100-rc.2.25502.107"), &[]), None);
        // `dotnet build` sets it, and the host overrides the caller's value.
        assert_eq!(
            compiler_of(&on_sdk("10.0.401"), &[("DOTNET_HOST_PATH", "/d/dotnet")]),
            ten_four
        );
        for selector in COMPILER_SELECTORS
            .iter()
            .filter(|s| !s.eq_ignore_ascii_case("DOTNET_HOST_PATH"))
        {
            let lower = selector.to_ascii_lowercase();
            assert_eq!(
                compiler_of(&on_sdk("10.0.401"), &[(&lower, "x")]),
                None,
                "{selector} in the environment"
            );
        }
        for selector in COMPILER_SELECTORS {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .foreign_definitions
                .properties
                .entry(selector.to_ascii_lowercase())
                .or_default()
                .insert("/w/Directory.Build.props".into());
            assert_eq!(compiler_of(&parsed, &[]), None, "{selector} defined");
        }
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .properties
            .entry("langversion".to_string())
            .or_default()
            .insert("/w/App.fsproj".into());
        assert_eq!(compiler_of(&parsed, &[]), ten_four, "not a selector");
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .targets
            .entry("corecompile".to_string())
            .or_default()
            .insert("/w/Directory.Build.targets".into());
        assert_eq!(compiler_of(&parsed, &[]), None, "CoreCompile redefined");
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .tasks
            .entry("fsc".to_string())
            .or_default()
            .insert("/w/Directory.Build.props".into());
        assert_eq!(compiler_of(&parsed, &[]), None, "Fsc registered");
        for (table, name) in [
            ("tasks", "my.ns.fsc"),
            ("tasks", "$(task)"),
            ("properties", "$(selector)"),
        ] {
            let mut parsed = on_sdk("10.0.401");
            let foreign = &mut parsed.foreign_definitions;
            let table = if table == "tasks" {
                &mut foreign.tasks
            } else {
                &mut foreign.properties
            };
            table
                .entry(name.to_string())
                .or_default()
                .insert("/w/Directory.Build.targets".into());
            assert_eq!(compiler_of(&parsed, &[]), None, "{name}");
        }
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .tasks
            .entry("notfsc".to_string())
            .or_default()
            .insert("/w/Directory.Build.targets".into());
        assert_eq!(compiler_of(&parsed, &[]), None, "any task is build code");
        for (table, name, expected) in [
            ("targets", "stampversion", None),
            ("properties", "builddependson", None),
            ("properties", "corecompiledependson", None),
            ("properties", "versionprefix", ten_four.clone()),
        ] {
            let mut parsed = on_sdk("10.0.401");
            let foreign = &mut parsed.foreign_definitions;
            let table = if table == "targets" {
                &mut foreign.targets
            } else {
                &mut foreign.properties
            };
            table
                .entry(name.to_string())
                .or_default()
                .insert("/w/Directory.Build.targets".into());
            assert_eq!(compiler_of(&parsed, &[]), expected, "{name}");
        }
        for selector in COMPILER_SELECTORS {
            let globals = HashMap::from([(selector.to_ascii_lowercase(), "x".to_string())]);
            assert_eq!(
                project_compiler(&on_sdk("10.0.401"), &HashMap::new(), &globals),
                None,
                "{selector} as a global"
            );
        }
        let mut parsed = on_sdk("10.0.401");
        parsed.hidden_content = Some(UntrustedCause::Unentered("an import".to_string()));
        assert_eq!(compiler_of(&parsed, &[]), None, "content unseen");

        let with = |name: &str, value: &str| {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .properties
                .insert(name.to_string(), value.to_string());
            parsed
        };
        let props = "FSharpPropsShim";
        for (name, value, expected) in [
            (
                props,
                "/d/sdk/10.0.112/FSharp/Microsoft.FSharp.NetSdk.props",
                None,
            ),
            (props, "/opt/FSharp/Microsoft.FSharp.NetSdk.props", None),
            (
                "FSharpTargetsShim",
                "/d/sdk/10.0.112/FSharp/Microsoft.FSharp.NetSdk.targets",
                None,
            ),
            ("UseBundledFSharpTargets", "false", None),
            (
                "DotnetFscCompilerPath",
                r#""/d/sdk/10.0.401/FSharp/fsc.dll""#,
                ten_four.clone(),
            ),
            (
                "DotnetFscCompilerPath",
                r#""/d/sdk/10.0.112/FSharp/fsc.dll""#,
                None,
            ),
        ] {
            assert_eq!(
                compiler_of(&with(name, value), &[]),
                expected,
                "{name}={value}"
            );
        }
        let mut parsed = on_sdk("10.0.401");
        parsed.properties.remove("FSharpTargetsShim");
        assert_eq!(compiler_of(&parsed, &[]), None, "no targets shim");
        let mut parsed = on_sdk("10.0.401");
        parsed.untrusted_properties.insert(
            "fsharppropsshim".to_string(),
            UntrustedCause::Unentered("a gate".to_string()),
        );
        assert_eq!(compiler_of(&parsed, &[]), None, "untrusted props shim");
        let mut parsed = on_sdk("10.0.401");
        parsed.resolved_sdk_root = Some("/opt/my-sdk".into());
        assert_eq!(compiler_of(&parsed, &[]), None, "not the canonical layout");
    }

    /// The compiler lifts its floor for `SKIP_VERSION_SUPPORTED_CHECK=1`
    /// exactly.
    #[test]
    fn the_support_check_is_skipped_for_one_exactly() {
        let parsed = on_sdk("10.0.401");
        let skipped = |value: &str| {
            let environment = HashMap::from([(
                "SKIP_VERSION_SUPPORTED_CHECK".to_string(),
                value.to_string(),
            )]);
            project_compiler(&parsed, &environment, &HashMap::new())
                .unwrap()
                .support_check_skipped
        };
        assert!(skipped("1"));
        for other in ["", "0", "true", " 1", "yes"] {
            assert!(!skipped(other), "{other:?}");
        }
        assert!(
            !project_compiler(&parsed, &HashMap::new(), &HashMap::new())
                .unwrap()
                .support_check_skipped
        );
    }

    /// A compiler with no row reads the value as the pinned compiler does and
    /// claims no floor; a skipped support check lifts the floor.
    #[test]
    fn an_sdk_with_no_row_gets_the_pinned_reading_and_no_floor() {
        let compiler = |version: &str, support_check_skipped| ProjectCompiler {
            sdk: sdk(version),
            support_check_skipped,
        };
        let parsed = evaluate("<LangVersion>4.6</LangVersion>");
        let selection = LangVersionSelection::of(&parsed, Some(&compiler("9.0.100", false)));
        assert_eq!(
            selection,
            LangVersionSelection {
                version: V4_6,
                refusal: None
            }
        );
        let parsed = evaluate("");
        let selection = LangVersionSelection::of(&parsed, None);
        assert_eq!(selection.version, LanguageVersion::DEFAULT);
        let below_floor = evaluate("<LangVersion>4.6</LangVersion>");
        let refused = LangVersionSelection::of(&below_floor, Some(&compiler("10.0.401", false)));
        assert_eq!(refused.version, V4_6);
        assert_eq!(
            refused.refusal.map(|r| r.kind),
            Some(RefusalKind::OutOfSupport { floor: V8_0 })
        );
        assert_eq!(
            LangVersionSelection::of(&below_floor, Some(&compiler("10.0.401", true))),
            LangVersionSelection {
                version: V4_6,
                refusal: None
            }
        );
        let unrecognised = evaluate("<LangVersion>12.0</LangVersion>");
        assert_eq!(
            LangVersionSelection::of(&unrecognised, Some(&compiler("10.0.401", true)))
                .refusal
                .map(|r| r.kind),
            Some(RefusalKind::Unrecognised)
        );
    }

    /// The task's own environment reads choose the compiler too.
    #[test]
    fn a_compiler_location_in_the_environment_declines() {
        for variable in COMPILER_ENVIRONMENT {
            assert_eq!(
                compiler_of(&on_sdk("10.0.401"), &[(variable, "/opt/fsc")]),
                None,
                "{variable}"
            );
        }
    }

    #[test]
    fn a_refusal_names_the_sdk_and_the_value() {
        for kind in [
            RefusalKind::Unrecognised,
            RefusalKind::OutOfSupport { floor: V8_0 },
        ] {
            let message = LangVersionRefusal {
                sdk: sdk("10.0.112"),
                text: "11".to_string(),
                kind,
            }
            .message();
            assert!(message.contains(".NET SDK 10.0.112"), "{message}");
            assert!(message.contains("language version '11'"), "{message}");
        }
    }

    /// The version the compiler is handed is established only while nothing
    /// that carries it may move after evaluation.
    #[test]
    fn the_language_version_is_established_only_while_nothing_carries_another() {
        let doubted = |parsed: &ParsedProject| lang_version_untrusted_cause(parsed).is_some();
        assert!(!doubted(&on_sdk("10.0.401")));
        for flags in ["--warnon:3390", "--LangVersion:8.0", "@/w/more.rsp"] {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .properties
                .insert("OtherFlags".to_string(), flags.to_string());
            assert_eq!(doubted(&parsed), flags != "--warnon:3390", "{flags}");
        }
        for carrier in LANG_VERSION_CARRIERS {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .foreign_definitions
                .build_time_properties
                .entry(carrier.to_ascii_lowercase())
                .or_default()
                .insert("/w/Directory.Build.targets".into());
            assert!(doubted(&parsed), "{carrier} written by a target");
        }
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .properties
            .entry("langversion".to_string())
            .or_default()
            .insert("/w/App.fsproj".into());
        assert!(!doubted(&parsed), "an evaluation-time write is evaluated");
        let mut parsed = on_sdk("10.0.401");
        parsed.hidden_content = Some(UntrustedCause::Unentered("an import".to_string()));
        assert!(doubted(&parsed), "content unseen");
    }

    /// A workload manifest is the install's own build code: its targets stand,
    /// but a selector, a reshaped graph or a replaced compile step declines.
    #[test]
    fn a_workload_manifest_is_held_to_what_it_touches() {
        let ten_four = Some(sdk("10.0.401"));
        for (table, name, expected) in [
            ("targets", "_workloadtelemetry", ten_four.clone()),
            (
                "properties",
                "usingmicrosoftnetsdkwebassembly",
                ten_four.clone(),
            ),
            ("properties", "fsctoolpath", None),
            ("properties", "builddependson", None),
            ("targets", "corecompile", None),
            ("tasks", "my.fsc", None),
        ] {
            let mut parsed = on_sdk("10.0.401");
            let workload = &mut parsed.workload_definitions;
            let table = match table {
                "targets" => &mut workload.targets,
                "tasks" => &mut workload.tasks,
                _ => &mut workload.properties,
            };
            table
                .entry(name.to_string())
                .or_default()
                .insert("/d/sdk-manifests/x/WorkloadManifest.targets".into());
            assert_eq!(compiler_of(&parsed, &[]), expected, "{name}");
        }
    }
}
