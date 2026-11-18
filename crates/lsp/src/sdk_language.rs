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
//! The floor also bounds what a guessed version must get right: a reading
//! taken at a guess need only be invariant from the floor of the compiler that
//! checks the file up ([`checked_floor`]), and only a graded row has a floor
//! above [`LanguageVersion::MIN`]; no row means the full ladder.
//!
//! # The boundary
//!
//! The LSP as a whole takes the project's compiler to be the one it models: it
//! parses every file with the pinned compiler's grammar, whatever compiler the
//! project builds with. This module refines that, and no more. The compiler is
//! taken to be the resolved SDK's own unless a replacement is *visible outside
//! the SDK* ([`project_compiler`]): a compiler selector written, or set in the
//! environment or as a global; any target, task or target selection of a
//! project's own; a reshaped target graph; an SDK file the project imports
//! itself; content the walk could not see. Each of those declines, and a
//! refusal is withheld wherever something visible may change the value the
//! compiler is handed after evaluation ([`lang_version_untrusted_cause`]).
//! The files themselves parse at the evaluated version unless the evaluated
//! values show it may be another ([`lang_version_value_doubt`]): a target that
//! rewrites the version at build time withholds the refusal but does not move
//! the parse, as before this module. Packages commonly ship targets that write
//! properties under computed names (Nerdbank.GitVersioning's
//! `PropertyName="%(…)"`), and doubting every such project's version would
//! cost its fold for a write that never names it.
//!
//! The compiler can also switch a language feature apart from the version
//! (`--strict-indentation±`, `--disableLanguageFeature`), and then checks by a
//! set of rules no version has. Where the evaluation shows the build may pass
//! such a switch ([`feature_switch_evidence`]: a `$(OtherFlags)` that is not
//! version-neutral switches alone, or that the walk may have wrong, or a
//! `DisabledLanguageFeatures` item or a target writing `OtherFlags` that a
//! document outside the SDK names), the version is doubted however well
//! established it is ([`LangVersionDoubt::FeatureSwitch`]), and the fold reads
//! no file whose tree the language rules may shape: the version ladder's
//! shape bands do not bracket a rule set off the ladder. The switches are not
//! mirrored into the parse; no project of either corpus passes one. A computed
//! name and content the walk did not enter stay on the boundary above for the
//! switches as for the version, and hold only a guessed version to the whole
//! ladder ([`feature_switch_doubt`]).
//!
//! What stays **unmodelled**, by the same assumption the rest of the LSP makes:
//!
//! - a replacement hidden in an import the SDK performs that a project property
//!   steers: `NuGetBuildTasksPackTargets` with
//!   `ImportNuGetBuildTasksPackTargetsFromSdk`, pointed at
//!   `Microsoft.CSharp.targets`, has the SDK itself import a different
//!   `CoreCompile`;
//! - arguments the build is given outside the project: a `Directory.Build.rsp`
//!   response file, or a command line's `-p:` and `-t:`.
//!
//! A route of either kind is known and out of scope; closing one would need the
//! evaluator to track which properties a foreign file wrote into each SDK
//! import, not another case here.
//!
//! [`SdkDiscovery`]: crate::sdk_discovery::SdkDiscovery

use std::collections::HashMap;

use borzoi_cst::language_version::LanguageVersion;
use borzoi_msbuild::{InexactUnset, ParsedProject, PropertyRead, SdkVersion, UntrustedCause};

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

impl ProjectCompiler {
    /// The oldest language version this compiler checks a file at: its
    /// graded row's [`SdkLanguageFacts::floor`], below which it refuses the
    /// version (FS3880) rather than check at it. [`LanguageVersion::MIN`] when
    /// the build's environment lifts the floor (`SKIP_VERSION_SUPPORTED_CHECK=1`)
    /// or the SDK has no row.
    ///
    /// A guessed language version need only be right from here up, unless the
    /// build switches a feature apart from the version ([`checked_floor`]). The
    /// floor rests on the compiler and its environment alone, never on the
    /// version the build hands it: a doubted `$(LangVersion)` may name any
    /// version, and `$(OtherFlags)` or a response file may pass another, but
    /// the compiler refuses each below its floor all the same. It reads nothing
    /// but the variable to lift the floor (`LanguageVersion.IsVersionSupported`),
    /// and the SDK's `Fsc` task hands the compiler no environment of its own.
    pub fn floor(&self) -> LanguageVersion {
        if self.support_check_skipped {
            return LanguageVersion::MIN;
        }
        SdkLanguageFacts::for_sdk(&self.sdk).map_or(LanguageVersion::MIN, |facts| facts.floor)
    }
}

/// The oldest language version whose rules the build of `parsed` may parse a
/// file by, where `compiler` is [`project_compiler`]'s answer: that compiler's
/// [`ProjectCompiler::floor`], or [`LanguageVersion::MIN`] when it cannot be
/// said. This is what a reading taken at a guessed version must be invariant
/// from (`SyntaxRecovery::of_guessed_version`), so an unknown compiler, one
/// with no graded row, and one with its floor lifted each leave the whole
/// ladder to check.
///
/// So does a build that may switch a language feature apart from the version
/// ([`feature_switch_doubt`]): `--strict-indentation-` restores the
/// indentation rules of the versions below 8.0 at any version, and
/// `--disableLanguageFeature` takes a feature away, so a rule from below the
/// floor may still shape the parse.
pub fn checked_floor(
    parsed: &ParsedProject,
    compiler: Option<&ProjectCompiler>,
) -> LanguageVersion {
    if feature_switch_doubt(parsed).is_some() {
        return LanguageVersion::MIN;
    }
    compiler.map_or(LanguageVersion::MIN, ProjectCompiler::floor)
}

/// The compiler switches that turn a language feature on or off apart from the
/// language version, as `fsc --help` spells them (`sdk_language_diff` reads
/// every graded SDK's list and fails on a switch in neither this list nor
/// [`VERSION_NEUTRAL_SWITCHES`]).
pub const FEATURE_SWITCHES: &[&str] = &["strict-indentation", "disableLanguageFeature"];

/// The compiler switches, as `fsc --help` spells them, known not to turn a
/// language feature on or off apart from the language version: the only ones
/// a `$(OtherFlags)` may hold for a guess to be held to the compiler's floor
/// ([`only_version_neutral_switches`]). `--langversion` names the version
/// itself, which the compiler refuses below its floor whatever spells it, and
/// `--define` sets `#if` symbols, at every version alike.
pub const VERSION_NEUTRAL_SWITCHES: &[&str] = &[
    "allsigs",
    "always-inline",
    "baseaddress",
    "checked",
    "checknulls",
    "checksumalgorithm",
    "codepage",
    "compilertool",
    "compressmetadata",
    "consolecolors",
    "crossoptimize",
    "debug",
    "define",
    "delaysign",
    "deterministic",
    "doc",
    "embed",
    "fullpaths",
    "help",
    "highentropyva",
    "keyfile",
    "langversion",
    "lib",
    "linkresource",
    "mlcompatibility",
    "nocopyfsharpcore",
    "noframework",
    "nointerfacedata",
    "nologo",
    "nooptimizationdata",
    "nowarn",
    "nowin32manifest",
    "optimize",
    "out",
    "pathmap",
    "pdb",
    "platform",
    "preferreduilang",
    "publicsign",
    "quotations-debug",
    "realsig",
    "reference",
    "reflectionfree",
    "refonly",
    "refout",
    "resource",
    "sig",
    "simpleresolution",
    "sourcelink",
    "standalone",
    "staticlink",
    "subsystemversion",
    "tailcalls",
    "target",
    "targetprofile",
    "utf8output",
    "version",
    "warn",
    "warnaserror",
    "warnon",
    "win32icon",
    "win32manifest",
    "win32res",
];

/// Whether `flags`, a `$(OtherFlags)` value, is a sequence of switches each of
/// which is in [`VERSION_NEUTRAL_SWITCHES`], spelt `-name` or `--name`,
/// optionally followed by `+`, `-` or `:argument`. Decided on the finest split
/// (every run of whitespace), and only for a value with no quote in it, since
/// the `Fsc` task joins and strips quoted text: each piece the compiler can
/// read as an argument of its own is then one of these, or a part of one's
/// argument, which names no switch. So anything else, a response file
/// (`@file`), a source path, a short alias (`-d:`), a quoted splice
/// (`--strict-""indentation-`), declines. Allowing only what is known, rather
/// than denying [`FEATURE_SWITCHES`], is what makes a spelling nobody listed
/// decline.
pub fn only_version_neutral_switches(flags: &str) -> bool {
    !flags.contains(['"', '\'', '@'])
        && flags.split_whitespace().all(|piece| {
            let Some(switch) = piece.strip_prefix("--").or_else(|| piece.strip_prefix('-')) else {
                return false;
            };
            let name = switch.split(':').next().unwrap_or_default();
            let name = name.strip_suffix(['+', '-']).unwrap_or(name);
            VERSION_NEUTRAL_SWITCHES.contains(&name)
        })
}

/// The `Fsc` task parameters, named for the properties `CoreCompile` reads
/// them from, through which a build can pass one of [`FEATURE_SWITCHES`]:
/// `$(OtherFlags)`, appended to the arguments as it stands (a switch, or an
/// `@` response file that may hold one). `sdk_language_diff` reads every
/// parameter `CoreCompile` hands the task in each graded SDK and fails on one
/// neither here, in [`FEATURE_SWITCH_ITEMS`], nor known not to carry one.
pub const FEATURE_SWITCH_CARRIERS: &[&str] = &["OtherFlags"];

/// The `Fsc` task parameters, named for the item types `CoreCompile` reads
/// them from, through which a build can pass one of [`FEATURE_SWITCHES`]:
/// `@(DisabledLanguageFeatures)`, each item passed as
/// `--disableLanguageFeature`. No SDK file defines such an item
/// (`sdk_language_diff` checks), so only a document outside the SDK can.
pub const FEATURE_SWITCH_ITEMS: &[&str] = &["DisabledLanguageFeatures"];

/// Why the build of `parsed` may switch a language feature apart from its
/// language version, or `None` when it passes none of [`FEATURE_SWITCHES`]:
/// every property carrier ([`FEATURE_SWITCH_CARRIERS`]) is unset or a trusted
/// value of version-neutral switches alone ([`only_version_neutral_switches`]),
/// no target outside the
/// SDK (or in a workload manifest) may write one before `CoreCompile` reads
/// it, no document outside the SDK defines an item of a type in
/// [`FEATURE_SWITCH_ITEMS`], and the walk entered every document.
///
/// Everything [`feature_switch_evidence`] reads, and besides it what may pass a
/// switch without naming one: a target or item whose name is computed (which
/// matches every query), and content the walk did not enter. This is what holds
/// a guessed version to the whole ladder ([`checked_floor`]); only the evidence
/// doubts a version that is otherwise the build's.
pub fn feature_switch_doubt(parsed: &ParsedProject) -> Option<FeatureSwitchRoute> {
    feature_switch_route(parsed, SwitchReach::May)
}

/// Why the evaluated project shows its build may switch a language feature
/// apart from its language version: a carrier ([`FEATURE_SWITCH_CARRIERS`])
/// whose evaluated value holds anything but version-neutral switches
/// ([`only_version_neutral_switches`]), or whose read the evaluation may have
/// wrong (as [`lang_version_value_doubt`] reads `$(LangVersion)`'s); a target
/// outside the SDK (or in a workload manifest) that writes a carrier under its
/// own name; or a document outside the SDK that defines an item of a type in
/// [`FEATURE_SWITCH_ITEMS`] under its own name.
///
/// This doubts the version the files parse at ([`LangVersionDoubt::FeatureSwitch`]),
/// however well established `$(LangVersion)` is: under such a switch the
/// compiler checks by a set of rules no language version has. What it leaves
/// to [`feature_switch_doubt`] alone, a computed name and content the walk did
/// not enter, is the boundary the module docs state for the version itself.
pub fn feature_switch_evidence(parsed: &ParsedProject) -> Option<FeatureSwitchRoute> {
    feature_switch_route(parsed, SwitchReach::Named)
}

/// Which routes to a feature switch [`feature_switch_route`] reads.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SwitchReach {
    /// What the evaluation shows ([`feature_switch_evidence`]).
    Named,
    /// Besides that, what may pass one unseen ([`feature_switch_doubt`]).
    May,
}

/// A way the build may pass one of [`FEATURE_SWITCHES`] to the compiler.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeatureSwitchRoute {
    /// A carrier ([`FEATURE_SWITCH_CARRIERS`]) whose read the evaluation may
    /// have wrong, for `cause`.
    Untrusted {
        carrier: &'static str,
        cause: UntrustedCause,
    },
    /// A carrier whose evaluated value holds something other than
    /// version-neutral switches ([`only_version_neutral_switches`]).
    Flags {
        carrier: &'static str,
        value: String,
    },
    /// A target outside the SDK (or in a workload manifest) that may write a
    /// carrier before `CoreCompile` reads it.
    TargetWrite { carrier: &'static str },
    /// A document outside the SDK (or a workload manifest) that may define an
    /// item of a type in [`FEATURE_SWITCH_ITEMS`].
    Item { item: &'static str },
    /// Content the walk did not enter ([`ParsedProject::hidden_content`]).
    Hidden(UntrustedCause),
}

fn feature_switch_route(parsed: &ParsedProject, reach: SwitchReach) -> Option<FeatureSwitchRoute> {
    let definitions = [&parsed.foreign_definitions, &parsed.workload_definitions];
    for &carrier in FEATURE_SWITCH_CARRIERS {
        let untrusted = |cause| Some(FeatureSwitchRoute::Untrusted { carrier, cause });
        let value = match parsed.property(carrier) {
            PropertyRead::Unset => None,
            PropertyRead::Value(value) => Some(value),
            PropertyRead::Untrusted(cause) => return untrusted(cause),
            PropertyRead::UnsetInexact(why) => match (reach, why) {
                (
                    SwitchReach::Named,
                    InexactUnset::Toolset
                    | InexactUnset::Opaque(_)
                    | InexactUnset::ConsumerCarveOut,
                ) => None,
                (_, why) => return untrusted(why.cause(carrier)),
            },
        };
        if let Some(value) = value.filter(|value| !only_version_neutral_switches(value)) {
            return Some(FeatureSwitchRoute::Flags { carrier, value });
        }
        if definitions.iter().any(|defined| match reach {
            SwitchReach::Named => defined.names_property_at_build_time(carrier),
            SwitchReach::May => defined.writes_property_at_build_time(carrier),
        }) {
            return Some(FeatureSwitchRoute::TargetWrite { carrier });
        }
    }
    if let Some(&item) = FEATURE_SWITCH_ITEMS.iter().find(|item| {
        definitions.iter().any(|defined| match reach {
            SwitchReach::Named => defined.names_item(item),
            SwitchReach::May => defined.defines_item(item),
        })
    }) {
        return Some(FeatureSwitchRoute::Item { item });
    }
    match reach {
        SwitchReach::Named => None,
        SwitchReach::May => parsed
            .hidden_content
            .clone()
            .map(FeatureSwitchRoute::Hidden),
    }
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
    let set_globally = globals
        .keys()
        .any(|name| is_selector(name) || name.to_ascii_lowercase().ends_with(TARGET_GRAPH_SUFFIX));
    if set_in_environment
        || set_globally
        || parsed.hidden_content.is_some()
        || !parsed.sdk_files_imported_from_outside.is_empty()
    {
        return None;
    }
    let chooses = |defined: &borzoi_msbuild::ForeignDefinitions| {
        COMPILER_SELECTORS
            .iter()
            .any(|name| defined.defines_property(name))
            || defined.defines_property_where(|name| name.ends_with(TARGET_GRAPH_SUFFIX))
            || defined.defines_target(COMPILE_TARGET)
            || defined.defines_task(COMPILE_TASK)
            || !defined.target_selections.is_empty()
    };
    // A workload manifest is the install's own build code, held to what it
    // touches; anything else outside the SDK may not run build code at all.
    let foreign = &parsed.foreign_definitions;
    if chooses(foreign) || foreign.defines_build_code() || chooses(&parsed.workload_definitions) {
        return None;
    }
    let sdk = entry_sdk_version(parsed.resolved_sdk_root.as_deref()?)?;
    SdkLanguageFacts::for_sdk(&sdk)?;
    // A value the walk trusts, or `None`: unset, untrusted, or one the real
    // build may hold and the walk does not (a refused write among them).
    let trusted = |name: &str| parsed.property(name).value().map(str::to_string);
    let names_own = |name: &str, file: &str| {
        trusted(name).and_then(|value| sdk_version_of_sdk_file(&value, &["FSharp", file]))
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
    // Only the SDK's props can have written it (nothing outside the SDK
    // defines a selector, checked above), and they name their own, so a value
    // the walk holds, trusted or not, must say so. A write it holds no value
    // for, undecided or refused, is the SDK's by the same argument, which
    // rests on what the build cannot be told rather than on the value: the
    // trust-blind table is the right question here.
    let holds_compiler_path = parsed
        .properties
        .keys()
        .any(|written| written.eq_ignore_ascii_case("DotnetFscCompilerPath"));
    if holds_compiler_path && !names_own("DotnetFscCompilerPath", "fsc.dll") {
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
    /// The evaluated values show the version may be another
    /// ([`lang_version_value_doubt`]).
    Provenance(UntrustedCause),
    /// The project's compiler refuses its `<LangVersion>`, so the build checks
    /// at no version.
    Refused(LangVersionRefusal),
    /// The evaluated values show the build may switch a language feature apart
    /// from the version ([`feature_switch_evidence`]), so the compiler may
    /// check by rules no version has.
    FeatureSwitch(FeatureSwitchRoute),
}

impl LangVersionDoubt {
    /// The doubt over `parsed`'s language version, if any. The value's own
    /// doubt comes first: a refusal read from a doubted value is itself a
    /// guess. A feature switch comes last, as the build may pass one whatever
    /// the version; the fold reads it from [`feature_switch_evidence`] itself
    /// whichever doubt this names.
    pub fn of(parsed: &ParsedProject, selection: &LangVersionSelection) -> Option<Self> {
        if let Some(cause) = lang_version_value_doubt(parsed) {
            return Some(LangVersionDoubt::Provenance(cause));
        }
        if let Some(refusal) = selection.refusal.clone() {
            return Some(LangVersionDoubt::Refused(refusal));
        }
        feature_switch_evidence(parsed).map(LangVersionDoubt::FeatureSwitch)
    }
}

/// The properties `CoreCompile` hands the compiler its language version
/// through: `$(LangVersion)`, and `$(OtherFlags)` (as `$(FscOtherFlags)`),
/// appended after it, where a `--langversion` or a response file overrides it.
pub const LANG_VERSION_CARRIERS: [&str; 3] = ["LangVersion", "OtherFlags", "FscOtherFlags"];

/// Why the version the compiler checks at may not be the one the evaluated
/// `$(LangVersion)` names, as far as the evaluated values themselves show: its
/// provenance is untrusted, it carries surrounding whitespace (the task hands
/// it on as it stands), it is `?` (the compiler's version query), or
/// `$(OtherFlags)` may name another (`langversion`, or an `@` response file).
/// These doubt the version the files parse at ([`LangVersionDoubt`]).
///
/// What could change the value after evaluation (a target, or content the walk
/// did not enter) does not: the files parse at the evaluated version under the
/// boundary the module docs state. It does withhold a refusal
/// ([`lang_version_untrusted_cause`]).
pub fn lang_version_value_doubt(parsed: &ParsedProject) -> Option<UntrustedCause> {
    if let Some(cause) = evaluated_value_doubt(parsed, "LangVersion") {
        return Some(cause);
    }
    // The effective values, globals and the environment included.
    // `ParsedProject::lang_version` is trimmed, but the task hands the
    // compiler the value as it stands.
    let lang_version = parsed.lang_version_untrimmed.as_deref();
    if lang_version.is_some_and(|value| value.trim() != value) {
        return Some(UntrustedCause::Unentered(
            "a `$(LangVersion)` with surrounding whitespace, which the compiler is handed as \
             it stands"
                .into(),
        ));
    }
    // `--langversion:?` asks the compiler to list its versions, and it checks
    // nothing.
    if lang_version == Some("?") {
        return Some(UntrustedCause::Unentered(
            "`$(LangVersion)` `?`, the compiler's version query".into(),
        ));
    }
    let other_flags = parsed
        .other_flags
        .as_deref()
        .unwrap_or_default()
        .to_ascii_lowercase();
    // A quote may splice a switch together (`--lang""version:7.0`): the `Fsc`
    // task strips it before the compiler reads the switch.
    if other_flags.contains("langversion") || other_flags.contains(['@', '"']) {
        return Some(UntrustedCause::Unentered(
            "`$(OtherFlags)`, which may name a language version after `$(LangVersion)`".into(),
        ));
    }
    None
}

/// Why the evaluation's read of `name` may not be the value the build
/// evaluates: a value the walk holds and may have wrong, or a name the real
/// build defines and the walk does not (a refused write, or the environment).
/// A name undefined only because the walk did not enter some content is not
/// doubted here: that content is [`ParsedProject::hidden_content`], which
/// [`lang_version_untrusted_cause`] reads on its own account.
fn evaluated_value_doubt(parsed: &ParsedProject, name: &str) -> Option<UntrustedCause> {
    match parsed.property(name) {
        PropertyRead::Untrusted(cause) => Some(cause),
        PropertyRead::UnsetInexact(
            why @ (InexactUnset::Refused | InexactUnset::Environment | InexactUnset::Rejected(_)),
        ) => Some(why.cause(name)),
        PropertyRead::Value(_)
        | PropertyRead::Unset
        | PropertyRead::UnsetInexact(
            InexactUnset::Toolset | InexactUnset::Opaque(_) | InexactUnset::ConsumerCarveOut,
        ) => None,
    }
}

/// Why the evaluated `$(LangVersion)` may not be the version the compiler is
/// handed, or `None` when it is established well enough to claim the build
/// fails on it. Besides [`lang_version_value_doubt`]: an untrusted
/// `$(OtherFlags)`, a target outside the SDK (or in a workload manifest) that
/// may write one of [`LANG_VERSION_CARRIERS`] before `CoreCompile` reads it
/// ([`ForeignDefinitions`], whose computed names match every query), and
/// content the walk did not enter. The SDK writes `LangVersion` only at
/// evaluation.
///
/// [`ForeignDefinitions`]: borzoi_msbuild::ForeignDefinitions
pub fn lang_version_untrusted_cause(parsed: &ParsedProject) -> Option<UntrustedCause> {
    if let Some(cause) = lang_version_value_doubt(parsed) {
        return Some(cause);
    }
    if let Some(cause) = evaluated_value_doubt(parsed, "OtherFlags") {
        return Some(cause);
    }
    if let Some(carrier) = LANG_VERSION_CARRIERS.iter().find(|carrier| {
        [&parsed.foreign_definitions, &parsed.workload_definitions]
            .iter()
            .any(|defined| defined.writes_property_at_build_time(carrier))
    }) {
        return Some(UntrustedCause::Unentered(
            format!("a target that may write `{carrier}` before `CoreCompile` reads it").into(),
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
            &borzoi_msbuild::ProjectFile::buffer(
                std::path::Path::new("/w/App.fsproj"),
                format!("<Project><PropertyGroup>{body}</PropertyGroup></Project>"),
            )
            .expect("a project path spelt as its full path"),
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
            parsed.properties.insert(name.to_string(), value.clone());
            parsed
                .property_reads
                .named
                .insert(name.to_ascii_lowercase(), PropertyRead::Value(value));
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
        parsed.hidden_content = Some(UntrustedCause::Unentered("an import".into()));
        assert_eq!(compiler_of(&parsed, &[]), None, "content unseen");

        // `read` is what the evaluation publishes for `name`; a `Value` is one
        // the walk holds too.
        let with_read = |name: &str, read: PropertyRead| {
            let mut parsed = on_sdk("10.0.401");
            if let PropertyRead::Value(value) = &read {
                parsed.properties.insert(name.to_string(), value.clone());
            }
            parsed
                .property_reads
                .named
                .insert(name.to_ascii_lowercase(), read);
            parsed
        };
        let with =
            |name: &str, value: &str| with_read(name, PropertyRead::Value(value.to_string()));
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
        parsed.property_reads.named.remove("fsharptargetsshim");
        assert_eq!(compiler_of(&parsed, &[]), None, "no targets shim");
        let untrusted = PropertyRead::Untrusted(UntrustedCause::Unentered("a gate".into()));
        assert_eq!(
            compiler_of(&with_read("FSharpPropsShim", untrusted), &[]),
            None,
            "untrusted props shim"
        );
        let refused = PropertyRead::UnsetInexact(InexactUnset::Refused);
        assert_eq!(
            compiler_of(&with_read("FSharpPropsShim", refused), &[]),
            None,
            "refused props shim"
        );
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

    /// A guessed version need only be right from the compiler's floor up, and
    /// the floor is above the bottom of the ladder only for a compiler with a
    /// graded row that keeps it: 10.0.1xx's compiler checks at F# 4.6, and
    /// `SKIP_VERSION_SUPPORTED_CHECK=1` lifts 10.0.4xx's.
    #[test]
    fn a_guess_is_held_to_the_floor_only_of_a_compiler_that_enforces_it() {
        let floor = |version: &str, support_check_skipped| {
            ProjectCompiler {
                sdk: sdk(version),
                support_check_skipped,
            }
            .floor()
        };
        assert_eq!(floor("10.0.401", false), V8_0);
        assert_eq!(floor("10.0.499", false), V8_0);
        assert_eq!(floor("10.0.401", true), LanguageVersion::MIN);
        assert_eq!(floor("10.0.112", false), LanguageVersion::MIN);
        for ungraded in ["10.0.300", "11.0.100", "9.0.100", "10.0.400-rc.1.1"] {
            assert_eq!(floor(ungraded, false), LanguageVersion::MIN, "{ungraded}");
        }
        // Through the evaluation: the environment it saw decides.
        let checked = |parsed: &ParsedProject, environment: &HashMap<String, String>| {
            checked_floor(
                parsed,
                project_compiler(parsed, environment, &HashMap::new()).as_ref(),
            )
        };
        let parsed = on_sdk("10.0.401");
        assert_eq!(checked_floor(&parsed, None), LanguageVersion::MIN);
        let skipping =
            HashMap::from([("SKIP_VERSION_SUPPORTED_CHECK".to_string(), "1".to_string())]);
        assert_eq!(checked(&parsed, &HashMap::new()), V8_0);
        assert_eq!(checked(&parsed, &skipping), LanguageVersion::MIN);
        assert_eq!(
            checked(&on_sdk("10.0.112"), &HashMap::new()),
            LanguageVersion::MIN
        );
    }

    /// A build that may switch a language feature apart from the version may
    /// parse by a rule from below the compiler's floor, so a guess is held to
    /// the whole ladder: a carrier that names a feature switch or a response
    /// file, one the walk does not hold exactly, and one a target may write.
    #[test]
    fn a_feature_switch_keeps_the_whole_ladder() {
        let with_read = |name: &str, read: PropertyRead| {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .property_reads
                .named
                .insert(name.to_ascii_lowercase(), read);
            parsed
        };
        let with =
            |name: &str, value: &str| with_read(name, PropertyRead::Value(value.to_string()));
        let checked = |parsed: &ParsedProject| {
            checked_floor(
                parsed,
                project_compiler(parsed, &HashMap::new(), &HashMap::new()).as_ref(),
            )
        };
        for (name, value, expected) in [
            ("OtherFlags", "--warnon:3390 --nowarn:FS0044", V8_0),
            ("OtherFlags", "--langversion:9.0", V8_0),
            ("OtherFlags", "--strict-indentation-", LanguageVersion::MIN),
            ("OtherFlags", "-STRICT-INDENTATION+", LanguageVersion::MIN),
            (
                "OtherFlags",
                "--disableLanguageFeature:NullnessChecking",
                LanguageVersion::MIN,
            ),
            ("OtherFlags", "@/w/more.rsp", LanguageVersion::MIN),
            (
                "OtherFlags",
                "--strict-\"\"indentation-",
                LanguageVersion::MIN,
            ),
            ("OtherFlags", "-d:FOO", LanguageVersion::MIN),
            ("OtherFlags", "Extra.fs", LanguageVersion::MIN),
            (
                "OtherFlags",
                "--warnon:3390\t--debug+\n--optimize- --keyfile:/k.snk",
                V8_0,
            ),
            ("OtherFlags", "  ", V8_0),
            // A property of the item's name passes nothing.
            ("DisabledLanguageFeatures", "NullnessChecking", V8_0),
        ] {
            assert_eq!(checked(&with(name, value)), expected, "{name}={value:?}");
        }
        for carrier in FEATURE_SWITCH_CARRIERS {
            let untrusted = PropertyRead::Untrusted(UntrustedCause::Unentered("a gate".into()));
            assert_eq!(
                checked(&with_read(carrier, untrusted)),
                LanguageVersion::MIN
            );
            let refused = PropertyRead::UnsetInexact(InexactUnset::Refused);
            assert_eq!(checked(&with_read(carrier, refused)), LanguageVersion::MIN);
            let mut parsed = on_sdk("10.0.401");
            parsed
                .workload_definitions
                .build_time_properties
                .entry(carrier.to_ascii_lowercase())
                .or_default()
                .insert("/d/sdk-manifests/x/WorkloadManifest.targets".into());
            assert_eq!(checked(&parsed), LanguageVersion::MIN, "{carrier} written");
        }
        for item in FEATURE_SWITCH_ITEMS {
            for definitions in ["foreign", "workload"] {
                let mut parsed = on_sdk("10.0.401");
                let defined = if definitions == "foreign" {
                    &mut parsed.foreign_definitions
                } else {
                    &mut parsed.workload_definitions
                };
                defined
                    .items
                    .entry(item.to_ascii_lowercase())
                    .or_default()
                    .insert("/w/Directory.Build.props".into());
                assert_eq!(
                    checked(&parsed),
                    LanguageVersion::MIN,
                    "{item} ({definitions})"
                );
            }
        }
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .items
            .entry("compile".to_string())
            .or_default()
            .insert("/w/App.fsproj".into());
        assert_eq!(checked(&parsed), V8_0, "an item of another type");
    }

    /// What the evaluation shows of a feature switch doubts a trusted version
    /// ([`LangVersionDoubt::FeatureSwitch`]); a name the build computes and
    /// content the walk did not enter hold only a guess to the whole ladder.
    /// Whatever is evidence is also doubt, so a switch that doubts a trusted
    /// version always widens a guessed one too.
    #[test]
    fn a_feature_switch_the_evaluation_shows_doubts_a_trusted_version() {
        use std::collections::{BTreeMap, BTreeSet};
        use std::path::PathBuf;
        let doubt = |parsed: &ParsedProject| {
            let compiler = project_compiler(parsed, &HashMap::new(), &HashMap::new());
            LangVersionDoubt::of(parsed, &LangVersionSelection::of(parsed, compiler.as_ref()))
        };
        let with_read = |read: PropertyRead| {
            let mut parsed = on_sdk("10.0.401");
            parsed
                .property_reads
                .named
                .insert("otherflags".to_string(), read);
            parsed
        };
        let defined =
            |table: fn(&mut ParsedProject) -> &mut BTreeMap<String, BTreeSet<PathBuf>>,
             name: &str| {
                let mut parsed = on_sdk("10.0.401");
                table(&mut parsed)
                    .entry(name.to_string())
                    .or_default()
                    .insert("/w/Directory.Build.targets".into());
                parsed
            };
        let mut hidden = on_sdk("10.0.401");
        hidden.hidden_content = Some(UntrustedCause::Unentered("an import".into()));
        let flags = |value: &str| {
            let mut parsed = with_read(PropertyRead::Value(value.to_string()));
            parsed.other_flags = Some(value.to_string());
            parsed
        };
        // (case, the evidence's route, whether the broader doubt sees a route)
        let cases: Vec<(&str, ParsedProject, Option<FeatureSwitchRoute>, bool)> = vec![
            ("nothing", on_sdk("10.0.401"), None, false),
            (
                "neutral flags",
                flags("--warnon:3390 --optimize-"),
                None,
                false,
            ),
            (
                "strict indentation",
                flags("--strict-indentation-"),
                Some(FeatureSwitchRoute::Flags {
                    carrier: "OtherFlags",
                    value: "--strict-indentation-".to_string(),
                }),
                true,
            ),
            (
                "a quoted splice",
                flags("--strict-\"\"indentation-"),
                Some(FeatureSwitchRoute::Flags {
                    carrier: "OtherFlags",
                    value: "--strict-\"\"indentation-".to_string(),
                }),
                true,
            ),
            (
                "an untrusted read",
                with_read(PropertyRead::Untrusted(UntrustedCause::Unentered(
                    "a gate".into(),
                ))),
                Some(FeatureSwitchRoute::Untrusted {
                    carrier: "OtherFlags",
                    cause: UntrustedCause::Unentered("a gate".into()),
                }),
                true,
            ),
            (
                "a refused write",
                with_read(PropertyRead::UnsetInexact(InexactUnset::Refused)),
                Some(FeatureSwitchRoute::Untrusted {
                    carrier: "OtherFlags",
                    cause: InexactUnset::Refused.cause("OtherFlags"),
                }),
                true,
            ),
            (
                "unset behind hidden content",
                with_read(PropertyRead::UnsetInexact(InexactUnset::Opaque(
                    UntrustedCause::Unentered("an import".into()),
                ))),
                None,
                true,
            ),
            (
                "a target writing the carrier",
                defined(
                    |p| &mut p.foreign_definitions.build_time_properties,
                    "otherflags",
                ),
                Some(FeatureSwitchRoute::TargetWrite {
                    carrier: "OtherFlags",
                }),
                true,
            ),
            (
                "a workload target writing the carrier",
                defined(
                    |p| &mut p.workload_definitions.build_time_properties,
                    "otherflags",
                ),
                Some(FeatureSwitchRoute::TargetWrite {
                    carrier: "OtherFlags",
                }),
                true,
            ),
            (
                "a target writing a computed name",
                defined(
                    |p| &mut p.foreign_definitions.build_time_properties,
                    "%(nbgv_propertyitems.identity)",
                ),
                None,
                true,
            ),
            (
                "an item of the type",
                defined(
                    |p| &mut p.foreign_definitions.items,
                    "disabledlanguagefeatures",
                ),
                Some(FeatureSwitchRoute::Item {
                    item: "DisabledLanguageFeatures",
                }),
                true,
            ),
            (
                "an item of a computed type",
                defined(|p| &mut p.foreign_definitions.items, "$(itemtype)"),
                None,
                true,
            ),
            (
                "an item of another type",
                defined(|p| &mut p.foreign_definitions.items, "compile"),
                None,
                false,
            ),
            ("hidden content", hidden, None, true),
        ];
        for (case, parsed, evidence, doubted) in cases {
            assert_eq!(feature_switch_evidence(&parsed), evidence, "{case}");
            assert_eq!(feature_switch_doubt(&parsed).is_some(), doubted, "{case}");
            assert!(evidence.is_none() || doubted, "{case}: evidence is doubt");
            // A quote also doubts the version `$(OtherFlags)` may name.
            let expected = lang_version_value_doubt(&parsed)
                .map(LangVersionDoubt::Provenance)
                .or(evidence.map(LangVersionDoubt::FeatureSwitch));
            assert_eq!(doubt(&parsed), expected, "{case}");
        }
        // A doubted value and a refusal each come first: either already
        // makes the version a guess.
        let mut parsed = flags("--strict-indentation- --langversion:9.0");
        assert!(matches!(
            doubt(&parsed),
            Some(LangVersionDoubt::Provenance(_))
        ));
        parsed.lang_version = Some("4.6".to_string());
        parsed.lang_version_untrimmed = Some("4.6".to_string());
        parsed.property_reads.named.insert(
            "otherflags".to_string(),
            PropertyRead::Value("--strict-indentation-".into()),
        );
        parsed.other_flags = Some("--strict-indentation-".to_string());
        assert!(matches!(doubt(&parsed), Some(LangVersionDoubt::Refused(_))));
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
        for flags in [
            "--warnon:3390",
            "--LangVersion:8.0",
            "@/w/more.rsp",
            r#"--lang""version:8.0"#,
        ] {
            let mut parsed = on_sdk("10.0.401");
            parsed.other_flags = Some(flags.to_string());
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
            assert_eq!(
                lang_version_value_doubt(&parsed),
                None,
                "{carrier}: the files still parse at the evaluated version"
            );
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
        parsed.hidden_content = Some(UntrustedCause::Unentered("an import".into()));
        assert!(doubted(&parsed), "content unseen");
        assert_eq!(
            lang_version_value_doubt(&parsed),
            None,
            "the files still parse at it"
        );
        for value in [" 7.0", "8.0 ", "\t11", "?"] {
            let mut parsed = on_sdk("10.0.401");
            parsed.lang_version_untrimmed = Some(value.to_string());
            assert!(doubted(&parsed), "{value:?}");
        }
        let mut parsed = on_sdk("10.0.401");
        parsed.lang_version_untrimmed = Some("8.0".to_string());
        assert!(!doubted(&parsed));
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
            ("selections", "initialtargets", None),
        ] {
            let mut parsed = on_sdk("10.0.401");
            let workload = &mut parsed.workload_definitions;
            let table = match table {
                "targets" => &mut workload.targets,
                "tasks" => &mut workload.tasks,
                "selections" => &mut workload.target_selections,
                _ => &mut workload.properties,
            };
            table
                .entry(name.to_string())
                .or_default()
                .insert("/d/sdk-manifests/x/WorkloadManifest.targets".into());
            assert_eq!(compiler_of(&parsed, &[]), expected, "{name}");
        }
    }

    /// A target graph reshaped by a global, and the SDK's own files imported by
    /// a project, decline.
    #[test]
    fn a_global_graph_or_an_sdk_file_imported_by_the_project_declines() {
        let globals = HashMap::from([("BuildDependsOn".to_string(), "Clean".to_string())]);
        assert_eq!(
            project_compiler(&on_sdk("10.0.401"), &HashMap::new(), &globals),
            None
        );
        let mut parsed = on_sdk("10.0.401");
        parsed
            .sdk_files_imported_from_outside
            .insert("/d/sdk/10.0.401/Microsoft.CSharp.targets".into());
        assert_eq!(compiler_of(&parsed, &[]), None);
    }

    /// A project that selects its own targets may not run the compiler.
    #[test]
    fn a_target_selection_outside_the_sdk_declines() {
        let mut parsed = on_sdk("10.0.401");
        parsed
            .foreign_definitions
            .target_selections
            .entry("defaulttargets".to_string())
            .or_default()
            .insert("/w/App.fsproj".into());
        assert_eq!(compiler_of(&parsed, &[]), None);
    }
}
