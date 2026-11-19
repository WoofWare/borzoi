//! Hostile environments ([`Kind::Environment`]).
//!
//! An entry is a set of variables to add to the environment a tool is
//! started with (or an evaluation is handed). Every variable is a property
//! to MSBuild, and several choose what the toolchain runs, so an environment
//! is an input like any other: a subject that reads one must be graded under
//! each, and an oracle child must be started under the same one.
//!
//! No entry stops a tool from starting at all (a variable that makes MSBuild
//! wait for a debugger, say): such a value says nothing about the subject.

use std::sync::OnceLock;

use super::{Alphabet, Dimension, Entry, Kind};

/// Variables to add to an environment: names and values.
pub type Variables = &'static [(&'static str, &'static str)];

/// A path no machine has.
const NOWHERE: &str = "/nonexistent/borzoi-hostile";

const TABLE: &[(Dimension, Variables, &str)] = &[
    // Names of properties MSBuild reads.
    (
        Dimension::PropertyName,
        &[("Configuration", "FromEnvironment")],
        "the configuration, which most conditions read",
    ),
    (
        Dimension::PropertyName,
        &[("Platform", "x64")],
        "the platform",
    ),
    (
        Dimension::PropertyName,
        &[("AssemblyName", "Evil")],
        "the assembly's name, which a project that sets none takes from here",
    ),
    (
        Dimension::PropertyName,
        &[("TargetFramework", "net472")],
        "the target framework",
    ),
    (
        Dimension::PropertyName,
        &[("LangVersion", "4.6")],
        "the language version",
    ),
    (
        Dimension::PropertyName,
        &[("OtherFlags", "--out:obj/Evil.dll")],
        "compiler flags",
    ),
    (
        Dimension::PropertyName,
        &[("DefineConstants", "EVIL")],
        "conditional-compilation symbols",
    ),
    (
        Dimension::PropertyName,
        &[("BaseIntermediateOutputPath", "evil/")],
        "the directory the restore writes to and the build imports from",
    ),
    (
        Dimension::PropertyName,
        &[("ImportDirectoryBuildProps", "false")],
        "a switch on an import the SDK makes",
    ),
    (
        Dimension::PropertyName,
        &[("OS", "Windows_NT")],
        "the operating system's name, which conditions throughout the SDK compare",
    ),
    (
        Dimension::PropertyName,
        &[("MSBuildProjectDirectory", NOWHERE)],
        "a reserved property's name, which the environment cannot set",
    ),
    // Variables the toolchain reads.
    (
        Dimension::ToolchainVariable,
        &[("DOTNET_ROOT", NOWHERE)],
        "where the host looks for runtimes and SDKs",
    ),
    (
        Dimension::ToolchainVariable,
        &[("DOTNET_MSBUILD_SDK_RESOLVER_SDKS_DIR", NOWHERE)],
        "where the SDK resolver looks for SDKs",
    ),
    (
        Dimension::ToolchainVariable,
        &[("DOTNET_MSBUILD_SDK_RESOLVER_CLI_DIR", NOWHERE)],
        "the dotnet directory the SDK resolver starts from",
    ),
    (
        Dimension::ToolchainVariable,
        &[("MSBuildSDKsPath", NOWHERE)],
        "the directory SDK imports resolve in",
    ),
    (
        Dimension::ToolchainVariable,
        &[("MSBuildExtensionsPath", NOWHERE)],
        "the directory extension imports resolve in",
    ),
    (
        Dimension::ToolchainVariable,
        &[("MSBUILDENABLEALLPROPERTYFUNCTIONS", "1")],
        "lets a property function call any method",
    ),
    (
        Dimension::ToolchainVariable,
        &[("MSBUILDLOGTASKINPUTS", "1")],
        "logs task inputs, and is visible to a project as a property",
    ),
    (
        Dimension::ToolchainVariable,
        &[("NUGET_PACKAGES", NOWHERE)],
        "the global packages folder",
    ),
    (
        Dimension::ToolchainVariable,
        &[("NUGET_FALLBACK_PACKAGES", NOWHERE)],
        "the fallback packages folders",
    ),
    (
        Dimension::ToolchainVariable,
        &[("HOME", NOWHERE)],
        "the home directory, which holds the user's NuGet configuration and workload manifests",
    ),
    (
        Dimension::ToolchainVariable,
        &[("DOTNET_CLI_HOME", NOWHERE)],
        "the dotnet CLI's own home",
    ),
    // Variables that name the compiler.
    (
        Dimension::CompilerSelector,
        &[("FscToolPath", NOWHERE)],
        "the directory the Fsc task runs its tool from",
    ),
    (
        Dimension::CompilerSelector,
        &[("FscToolExe", "evil-fsc")],
        "the tool the Fsc task runs",
    ),
    (
        Dimension::CompilerSelector,
        &[(
            "DotnetFscCompilerPath",
            "/nonexistent/borzoi-hostile/fsc.dll",
        )],
        "the compiler the Fsc task hands dotnet",
    ),
    (
        Dimension::CompilerSelector,
        &[(
            "FSharpTargetsPath",
            "/nonexistent/borzoi-hostile/Microsoft.FSharp.Targets",
        )],
        "the F# targets the SDK imports",
    ),
    (
        Dimension::CompilerSelector,
        &[("DOTNET_HOST_PATH", "/nonexistent/borzoi-hostile/dotnet")],
        "the muxer tasks start the compiler with",
    ),
    // Variables the build process sets for itself.
    (
        Dimension::BuildSetVariable,
        &[("_MSBUILDTLENABLED", "1")],
        "MSBuild's command line overwrites it: an inherited value is not the build's",
    ),
    (
        Dimension::BuildSetVariable,
        &[("MSBuildLoadMicrosoftTargetsReadOnly", "false")],
        "MSBuild's command line sets it to true",
    ),
    (
        Dimension::BuildSetVariable,
        &[("MSBUILDUSESERVER", "1")],
        "the dotnet CLI sets it when it is unset, and leaves a caller's value",
    ),
    // Culture.
    (
        Dimension::Locale,
        &[("LC_ALL", "tr_TR.UTF-8")],
        "Turkish case mapping: `i` and `I` are not a case pair",
    ),
    (
        Dimension::Locale,
        &[("LANG", "tr_TR.UTF-8")],
        "the same culture by the weaker variable",
    ),
    (Dimension::Locale, &[("LC_ALL", "C")], "no culture at all"),
    (
        Dimension::Locale,
        &[("DOTNET_SYSTEM_GLOBALIZATION_INVARIANT", "1")],
        ".NET's invariant mode: every culture-aware comparison becomes ordinal",
    ),
    (
        Dimension::Locale,
        &[("DOTNET_CLI_UI_LANGUAGE", "tr")],
        "the language of the messages an oracle parses",
    ),
    // Set and empty.
    (
        Dimension::EmptyValue,
        &[("Configuration", "")],
        "a property set to nothing: unlike an unset one to a reader that asks which",
    ),
    (
        Dimension::EmptyValue,
        &[("NUGET_PACKAGES", "")],
        "an empty folder override, which NuGet treats as unset",
    ),
    (
        Dimension::EmptyValue,
        &[("DOTNET_ROOT", "")],
        "an empty root",
    ),
    // Hostile values.
    (
        Dimension::HostileValue,
        &[("OtherFlags", "x\r\n--out:obj/Evil.dll")],
        "a line break and an option",
    ),
    (
        Dimension::HostileValue,
        &[("DefineConstants", "A;B,C")],
        "list separators",
    ),
    (
        Dimension::HostileValue,
        &[("AssemblyName", "Evil\tName\u{1b}[31m")],
        "control characters",
    ),
    (
        Dimension::HostileValue,
        &[("AssemblyName", "$(MSBuildProjectName)%41")],
        "an expansion and an escape, which MSBuild does not expand in an environment value",
    ),
    (
        Dimension::HostileValue,
        &[("NUGET_PACKAGES", "relative/packages")],
        "a relative path where an absolute one is expected",
    ),
    // Names that differ by case.
    (
        Dimension::CaseVariantName,
        &[("configuration", "lower"), ("Configuration", "Upper")],
        "two variables, one property: which value it takes is MSBuild's enumeration order",
    ),
    (
        Dimension::CaseVariantName,
        &[("nuget_packages", "/nonexistent/borzoi-hostile/lower")],
        "a toolchain variable's name in lower case, which Unix holds apart from it",
    ),
    // Names no property has.
    (
        Dimension::NotAPropertyName,
        &[("ProgramFiles(x86)", NOWHERE)],
        "parentheses, as Windows itself names a variable",
    ),
    (
        Dimension::NotAPropertyName,
        &[("1FOO", "x")],
        "a leading digit",
    ),
    (
        Dimension::NotAPropertyName,
        &[("A-B.C D", "x")],
        "a dot and a space",
    ),
];

/// The alphabet of hostile environments.
pub fn alphabet() -> &'static Alphabet<Variables> {
    static ALPHABET: OnceLock<Alphabet<Variables>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::Environment,
            TABLE
                .iter()
                .map(|(dimension, value, why)| Entry {
                    dimension: *dimension,
                    value: *value,
                    why,
                })
                .collect(),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_alphabet_covers_every_environment_dimension() {
        assert_eq!(alphabet().kind(), Kind::Environment);
    }

    /// Every variable can be handed to a child process: its name is not
    /// empty and holds no `=` or NUL, and its value holds no NUL.
    #[test]
    fn every_variable_can_be_set() {
        for entry in alphabet().entries() {
            assert!(!entry.value.is_empty(), "{}", entry.why);
            for (name, value) in entry.value {
                assert!(
                    !name.is_empty() && !name.contains(['=', '\0']) && !value.contains('\0'),
                    "{name:?}={value:?}"
                );
            }
            assert_eq!(
                entry.dimension == Dimension::EmptyValue,
                entry.value.iter().all(|(_, v)| v.is_empty()),
                "{}",
                entry.why
            );
        }
    }
}
