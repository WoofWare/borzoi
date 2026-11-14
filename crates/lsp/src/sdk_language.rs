//! What the F# compiler a project builds with makes of its `<LangVersion>`.
//!
//! The compiler that checks an SDK project is, by default, the `fsc.dll` in
//! the .NET SDK the project resolves (honouring `global.json`, through
//! [`SdkDiscovery`]): `Microsoft.FSharp.NetSdk.props` points
//! `$(DotnetFscCompilerPath)` at the one beside itself, `<root>/sdk/<version>/FSharp/fsc.dll`.
//! [`compiler_sdk`] reads that SDK's version off the evaluation, and declines
//! wherever the project or its environment chooses another compiler. Four facts about `<LangVersion>` vary by compiler:
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

/// The properties a build's choice of compiler reads besides the SDK's own
/// defaults: `Microsoft.FSharp.NetSdk.props` writes `DotnetFscCompilerPath`
/// (with `FscToolPath`/`FscToolExe`, the `dotnet` host that runs it) only
/// where it is empty, and not at all under `DisableAutoSetFscCompilerPath`.
const COMPILER_SELECTORS: [&str; 4] = [
    "DotnetFscCompilerPath",
    "DisableAutoSetFscCompilerPath",
    "FscToolPath",
    "FscToolExe",
];

/// The SDK whose compiler builds `parsed`, evaluated under `environment` (the
/// process environment its evaluation saw), or `None` when it cannot be said.
///
/// A real `dotnet build` runs with `DOTNET_HOST_PATH` set, under which
/// `Microsoft.FSharp.NetSdk.props` sets `$(DotnetFscCompilerPath)` to the
/// `fsc.dll` beside itself unless something set it first. So:
///
/// - An environment variable naming any of [`COMPILER_SELECTORS`] chooses the
///   compiler in a way the evaluation does not see (it outranks the SDK's
///   conditional writes): unknown. So does an untrusted selector, which the
///   real build may write whether or not the evaluation did.
/// - A written `$(DotnetFscCompilerPath)` decides, if it names an SDK's own
///   `fsc.dll`. (The evaluation writes it itself when the
///   server's environment carries `DOTNET_HOST_PATH`.)
/// - Otherwise a written `DisableAutoSetFscCompilerPath`, `FscToolPath` or
///   `FscToolExe` takes the build off the SDK's default: unknown.
/// - Otherwise the compiler is the one beside the F# props the SDK imports:
///   `$(FSharpPropsShim)`, under `$(UseBundledFSharpTargets)` = `true`, both
///   trusted, naming an SDK's own `FSharp/Microsoft.FSharp.NetSdk.props`.
pub fn compiler_sdk(
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
) -> Option<SdkVersion> {
    let set_in_environment = environment.iter().any(|(name, value)| {
        !value.is_empty()
            && COMPILER_SELECTORS
                .iter()
                .any(|selector| name.eq_ignore_ascii_case(selector))
    });
    // An untrusted selector may be written in the real build whether or not the
    // evaluation wrote it.
    if set_in_environment
        || COMPILER_SELECTORS
            .iter()
            .any(|name| parsed.property_provenance_untrusted(name))
    {
        return None;
    }
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
    if written("DotnetFscCompilerPath").is_some() {
        return sdk_version_of_sdk_file(written("DotnetFscCompilerPath")?, &["FSharp", "fsc.dll"]);
    }
    if COMPILER_SELECTORS[1..]
        .iter()
        .any(|name| written(name).is_some_and(|v| !v.trim().is_empty()))
    {
        return None;
    }
    if !trusted("UseBundledFSharpTargets")?
        .trim()
        .eq_ignore_ascii_case("true")
    {
        return None;
    }
    sdk_version_of_sdk_file(
        trusted("FSharpPropsShim")?,
        &["FSharp", "Microsoft.FSharp.NetSdk.props"],
    )
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
                self.text,
                self.sdk,
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
    /// The selection for `parsed`, built by the compiler of `compiler_sdk`
    /// ([`compiler_sdk`]'s answer): that compiler's reading of its
    /// `$(LangVersion)` when its SDK has a graded row, else the pinned
    /// compiler's.
    pub fn of(parsed: &ParsedProject, compiler_sdk: Option<&SdkVersion>) -> LangVersionSelection {
        let text = parsed.lang_version.as_deref();
        let Some((sdk, facts)) =
            compiler_sdk.and_then(|sdk| SdkLanguageFacts::for_sdk(sdk).map(|f| (sdk, f)))
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
                sdk: sdk.clone(),
                text: text.unwrap_or_default().to_string(),
                kind,
            })
        };
        match facts.reading(text) {
            LangVersionReading::Checks(version) => LangVersionSelection {
                version,
                refusal: None,
            },
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
    /// The evaluation cannot pin the `$(LangVersion)` write.
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
        if let Some(cause) = parsed.property_untrusted_cause("LangVersion") {
            return Some(LangVersionDoubt::Provenance(cause.clone()));
        }
        selection.refusal.clone().map(LangVersionDoubt::Refused)
    }
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

    const FSC: &str =
        r#"<DotnetFscCompilerPath>"/d/sdk/10.0.401/FSharp/fsc.dll"</DotnetFscCompilerPath>"#;
    const SHIM: &str = "<UseBundledFSharpTargets>true</UseBundledFSharpTargets>\
         <FSharpPropsShim>/d/sdk/10.0.112/FSharp/Microsoft.FSharp.NetSdk.props</FSharpPropsShim>";

    /// Each route [`compiler_sdk`] takes, and each way off the SDK's default
    /// compiler it declines on.
    #[test]
    fn the_compiler_sdk_follows_the_build_s_choice_of_compiler() {
        let none = HashMap::new();
        let cases: &[(String, &HashMap<String, String>, Option<&str>)] = &[
            (FSC.to_string(), &none, Some("10.0.401")),
            (SHIM.to_string(), &none, Some("10.0.112")),
            // A written compiler path outranks the shim.
            (format!("{SHIM}{FSC}"), &none, Some("10.0.401")),
            (
                format!("{SHIM}<DotnetFscCompilerPath>/opt/fsc.dll</DotnetFscCompilerPath>"),
                &none,
                None,
            ),
            (
                format!("{SHIM}<FscToolPath>/opt</FscToolPath>"),
                &none,
                None,
            ),
            (
                format!(
                    "{SHIM}<DisableAutoSetFscCompilerPath>true</DisableAutoSetFscCompilerPath>"
                ),
                &none,
                None,
            ),
            (SHIM.replace(">true<", ">false<"), &none, None),
            (
                format!(
                    r#"{SHIM}<DotnetFscCompilerPath Condition="'@(Nothing)' == ''">"/d/sdk/10.0.401/FSharp/fsc.dll"</DotnetFscCompilerPath>"#
                ),
                &none,
                None,
            ),
            (String::new(), &none, None),
        ];
        for (body, environment, expected) in cases {
            assert_eq!(
                compiler_sdk(&evaluate(body), environment),
                expected.map(sdk),
                "{body}"
            );
        }
        // A selector written under a gate the evaluation cannot decide, whichever
        // way the evaluation took it.
        for op in ["==", "!="] {
            let body = format!(
                r#"{SHIM}<FscToolPath Condition="'@(Nothing)' {op} ''">/opt</FscToolPath>"#
            );
            let parsed = evaluate(&body);
            assert!(
                parsed.property_provenance_untrusted("FscToolPath"),
                "{body}"
            );
            assert_eq!(compiler_sdk(&parsed, &none), None, "{body}");
        }
        for selector in COMPILER_SELECTORS {
            let environment = HashMap::from([(selector.to_ascii_lowercase(), "x".to_string())]);
            assert_eq!(
                compiler_sdk(&evaluate(SHIM), &environment),
                None,
                "{selector}"
            );
        }
    }

    /// A compiler with no row reads the value as the pinned compiler does and
    /// claims no floor.
    #[test]
    fn an_sdk_with_no_row_gets_the_pinned_reading_and_no_floor() {
        let parsed = evaluate("<LangVersion>4.6</LangVersion>");
        let selection = LangVersionSelection::of(&parsed, Some(&sdk("9.0.100")));
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
        let refused = LangVersionSelection::of(
            &evaluate("<LangVersion>4.6</LangVersion>"),
            Some(&sdk("10.0.401")),
        );
        assert_eq!(refused.version, V4_6);
        assert_eq!(
            refused.refusal.map(|r| r.kind),
            Some(RefusalKind::OutOfSupport { floor: V8_0 })
        );
    }
}
