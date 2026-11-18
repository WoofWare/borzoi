//! What one evaluation says about the F# compiler's run: the properties that
//! choose the compiler ([`COMPILER_SELECTORS`]), and the name of the assembly
//! it compiles ([`compiled_assembly_name`]).
//!
//! The name is held to the real build by `tests/fsproj_assembly_name_generative_diff.rs`,
//! which reads the arguments MSBuild's `Fsc` task hands fsc (the oracle's
//! `fscArgs` op) and asks of each name committed here that it be the one
//! fsc's `-o:` names.

use std::collections::HashMap;
use std::path::{Component, Path};

use crate::{ForeignDefinitions, ParsedProject, PropertyRead};

/// The properties the F# SDK reads in choosing the compiler a build runs:
/// which F# props and targets the SDK imports, which assembly's `Fsc` task
/// runs, and the tool path, executable and compiler path that task is handed.
/// Inside the SDK only its own F# files write any of them (the LSP's
/// `sdk_language_diff` derives the set from each installed SDK's files and
/// fails on a name missing here).
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
/// the directory instead of the task's own). The LSP's `sdk_language_diff`
/// reads every variable-shaped string in each installed SDK's
/// `FSharp.Build.dll` and fails on one neither here nor known to choose
/// something else.
pub const COMPILER_ENVIRONMENT: &[&str] = &["FSHARP_COMPILER_BIN"];

/// The suffix of the properties a target's `DependsOnTargets` reads by
/// convention (`BuildDependsOn`, `CoreCompileDependsOn`, …): a write of one
/// reshapes which targets run.
pub const TARGET_GRAPH_SUFFIX: &str = "dependson";

/// The properties whose values reach fsc's response file as part of one
/// argument, unsplit: the SDK's `CoreCompile` hands each to an `Fsc` task
/// parameter the task appends verbatim (`--doc:$(DocumentationFile)`), or an
/// SDK target copies one into such a parameter's property at build time
/// (`AssemblyOriginatorKeyFile` into `KeyOriginatorFile`, `ApplicationManifest`
/// into `Win32Manifest`). The task writes its arguments to the response file
/// one per line, and fsc reads that file a line at a time, so a line break in
/// one of these values starts an argument of its own, which may be anything.
///
/// `DefineConstants` is one too (`--define:` and each `;`-separated piece),
/// read through [`ParsedProject::define_constants`]. The parameters the task
/// splits at line breaks itself (`NoWarn`, `WarnOn`, `WarningsAsErrors`,
/// `WarningsNotAsErrors`, `PathMap`, the reference path), or maps onto a fixed
/// vocabulary (`DebugType`, `Platform`, `OutputType`, the booleans), carry no
/// argument of their own. `OtherFlags` is read argument by argument
/// (`may_set_output`). `fsc_verbatim_properties_cover_the_sdk_fsc_task`
/// holds this list to the installed SDK's `<Fsc>` invocation.
pub const FSC_VERBATIM_PROPERTIES: &[&str] = &[
    "ApplicationIcon",
    "ApplicationManifest",
    "AssemblyOriginatorKeyFile",
    "BaseAddress",
    "CodePage",
    "DocumentationFile",
    "GenerateInterfaceFile",
    "KeyOriginatorFile",
    "LangVersion",
    "LCID",
    "PdbFile",
    "PreferredUILang",
    "SourceLink",
    "SubsystemVersion",
    "TargetProfile",
    "VersionFile",
    "WarningLevel",
    "Win32Manifest",
    "Win32Resource",
];

/// The properties the SDK builds `IntermediateOutputPath` from, after
/// `BaseIntermediateOutputPath`: every SDK write of it is
/// `$(BaseIntermediateOutputPath)` (or its own value) followed by some of
/// these, each segment ending in a separator.
/// `intermediate_output_path_is_built_from_the_listed_segments` holds the
/// list, and the separators, to the installed SDK's files.
pub const INTERMEDIATE_SEGMENTS: &[&str] = &[
    "ArtifactsPivots",
    "Configuration",
    "PlatformName",
    "RuntimeIdentifier",
    "TargetFramework",
    "_PlatformToAppendToOutputPath",
];

/// The properties that name the sources the SDK's targets add to the compile
/// (`GeneratedAssemblyInfoFile`, the target-framework attribute file), and
/// the pieces the SDK builds those names from after
/// `IntermediateOutputPath`. Each name is a line of fsc's response file, so
/// one set outside the SDK may start with an option or hold a line break.
/// `generated_sources_are_listed` holds the list to the installed SDKs'
/// targets.
pub const GENERATED_SOURCE_PROPERTIES: &[&str] = &[
    "AssemblyAttributesPath",
    "DefaultLanguageSourceExtension",
    "GeneratedAssemblyInfoFile",
    "GeneratedGlobalUsingsFile",
    "TargetFrameworkMoniker",
    "TargetFrameworkMonikerAssemblyAttributesPath",
];

/// The properties the SDK's targets read in adding `#if` symbols to
/// `DefineConstants` at build time (`AddImplicitDefineConstants` and the
/// targets it depends on), each of which fsc is handed as a `--define:`
/// argument of its own. `implicit_define_inputs_are_listed` holds the list
/// to the installed SDKs' targets.
pub const IMPLICIT_DEFINE_PROPERTIES: &[&str] = &[
    "BackwardsCompatFrameworkDefine",
    "EffectiveTargetPlatformVersion",
    "ImplicitFrameworkDefine",
    "TargetFrameworkIdentifier",
    "TargetFrameworkVersion",
    "TargetPlatformIdentifier",
    "TargetPlatformVersion",
    "VersionlessImplicitFrameworkDefine",
    "_FrameworkIdentifierForImplicitDefine",
    "_FrameworkVersionForImplicitDefine",
    "_PlatformIdentifierForImplicitDefine",
    "_PlatformVersionForImplicitDefine",
];

/// The item types the same targets read, whose identities become symbols.
pub const IMPLICIT_DEFINE_ITEMS: &[&str] = &[
    "SdkSupportedTargetPlatformVersion",
    "SupportedNETFrameworkTargetFramework",
    "SupportedNETStandardTargetFramework",
    "_CompatibleFrameworkVersions",
    "_DefineConstantsWithoutTrace",
    "_FormattedCompatibleFrameworkVersions",
    "_ImplicitDefineConstant",
    "_NETCoreAppVersionsForDefines",
    "_SupportedFrameworkVersions",
    "_SupportedPlatformCompatibleVersions",
];

/// The name of the assembly a project compiles to, as FCS names it: the name
/// of the file fsc's `-o:` argument names, up to its last dot
/// (`TcConfigBuilder.DecideNames`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledAssemblyName {
    /// The build's compiler compiles to exactly this name.
    Known(String),
    /// The name could be another, for this reason.
    Unknown(NameDecline),
}

/// Why [`compiled_assembly_name`] declines. Each is a route by which the real
/// build may name its output apart from what the evaluation shows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NameDecline {
    /// The walk did not see all of the build's content, or the SDK's own
    /// files were imported in an arrangement it did not choose.
    HiddenContent,
    /// Something other than the SDK may choose the compiler (a selector set
    /// in a document, the environment or a global), which may write any
    /// output; or a global reshapes the target graph.
    CompilerChosen,
    /// A document outside the SDK defines a target, registers a task or
    /// selects the targets a build runs: code the build runs, which may build
    /// the project again or rewrite anything.
    ForeignBuildCode,
    /// A document outside the SDK (or a workload manifest) defines the
    /// `IntermediateAssembly` item `-o:` names, `CoreCompile`, the `Fsc` task,
    /// a target-graph property, or writes one of the name's properties at
    /// build time.
    Overridden,
    /// `TargetName` is not a trusted literal file name: untrusted, empty or
    /// blank, or holding a character the item it lands in would split,
    /// expand or read as a directory.
    Name,
    /// `TargetExt` is not a trusted `.dll` or `.exe`.
    Extension,
    /// `IntermediateOutputPath`, which prefixes the name in `-o:` and the
    /// generated sources, may not end in a separator, or may hold something
    /// the item splits, expands or breaks a line at, or fsc might read a path
    /// starting with it as an option.
    IntermediateOutputPath,
    /// `OtherFlags`, which `Fsc` passes after its own `-o:`, is untrusted or
    /// may hold an argument fsc reads as an output switch or a response file.
    OtherFlags,
    /// A source file fsc may read as an option, Compile items the walk is not
    /// certain of, or a source the SDK generates named through one of
    /// [`GENERATED_SOURCE_PROPERTIES`] set outside it.
    Sources,
    /// One of [`FSC_VERBATIM_PROPERTIES`] is untrusted or holds a line break,
    /// or so may a `DefineConstants` symbol, or one the SDK adds at build
    /// time from [`IMPLICIT_DEFINE_PROPERTIES`] and [`IMPLICIT_DEFINE_ITEMS`]
    /// set outside it.
    VerbatimInput,
}

/// [`CompiledAssemblyName`] of the project at `project_path`, from one
/// evaluation of it under `environment` (the process environment it saw) and
/// the global properties `globals`.
///
/// The `-o:` the SDK's `CoreCompile` passes is the `IntermediateAssembly`
/// item, `$(IntermediateOutputPath)$(TargetName)$(TargetExt)`, which MSBuild
/// evaluates after every property, so the evaluation's final values are the
/// ones it reads. fsc honours the last output switch it reads, and reads its
/// arguments from a response file a line at a time, so `-o:` holds unless a
/// later line is an output switch too: one in `OtherFlags`, a source file
/// spelled as one, or a line break in a verbatim argument. The name is
/// [`CompiledAssemblyName::Known`] only when every input to that is trusted
/// and none of those can happen; any other route makes it
/// [`CompiledAssemblyName::Unknown`], since the compiled name could then be
/// any name:
///
/// - the SDK's compiler runs, chosen by nothing outside it (as for
///   the LSP's `sdk_language::project_compiler`), and no document outside the
///   SDK runs build code ([`NameDecline::ForeignBuildCode`]) or overrides the
///   compile ([`NameDecline::Overridden`]);
/// - `TargetName` is literal and `TargetExt` is `.dll` or `.exe`, so the
///   name is `TargetName` itself;
/// - `IntermediateOutputPath` ends in a separator, so it prefixes no part
///   of the file name;
/// - no argument after `-o:` sets the output.
///
/// When MSBuild rejects the project or fails the build before fsc runs there
/// is no assembly, and a name committed then is a name for nothing.
///
/// Not covered: a line break in an item spec the task passes verbatim (a
/// reference path, an embedded resource, an embedded file), which starts a
/// response-file line of its own; and an evaluation made before the project
/// was restored, which has not seen the package build files a real build
/// imports. Either may rename the output, and neither is visible here.
pub fn compiled_assembly_name(
    project_path: &Path,
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
) -> CompiledAssemblyName {
    match decide(project_path, parsed, environment, globals) {
        Ok(name) => CompiledAssemblyName::Known(name),
        Err(decline) => CompiledAssemblyName::Unknown(decline),
    }
}

fn decide(
    project_path: &Path,
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
) -> Result<String, NameDecline> {
    if parsed.hidden_content.is_some()
        || !parsed.sdk_files_imported_from_outside.is_empty()
        || parsed.resolved_sdk_root.is_none()
    {
        return Err(NameDecline::HiddenContent);
    }
    if compiler_chosen_outside(parsed, environment, globals) {
        return Err(NameDecline::CompilerChosen);
    }
    if parsed.foreign_definitions.defines_build_code() {
        return Err(NameDecline::ForeignBuildCode);
    }
    if overrides_compile(&parsed.foreign_definitions)
        || overrides_compile(&parsed.workload_definitions)
    {
        return Err(NameDecline::Overridden);
    }

    let name = match parsed.property("TargetName") {
        PropertyRead::Value(name) => name,
        _ => return Err(NameDecline::Name),
    };
    if !literal_file_name(&name) {
        return Err(NameDecline::Name);
    }
    if !matches!(parsed.property("TargetExt"), PropertyRead::Value(ext) if ext == ".dll" || ext == ".exe")
    {
        return Err(NameDecline::Extension);
    }
    if !intermediate_dir_is_safe(parsed, environment, globals) {
        return Err(NameDecline::IntermediateOutputPath);
    }
    match parsed.property("OtherFlags") {
        PropertyRead::Unset => {}
        PropertyRead::Value(flags) if !fsc_lines(&flags).iter().any(|l| may_set_output(l)) => {}
        _ => return Err(NameDecline::OtherFlags),
    }
    if !sources_read_as_files(project_path, parsed)
        || !set_outside_safely(
            parsed,
            GENERATED_SOURCE_PROPERTIES,
            environment,
            globals,
            true,
        )
    {
        return Err(NameDecline::Sources);
    }
    let verbatim_ok = FSC_VERBATIM_PROPERTIES
        .iter()
        .all(|name| match parsed.property(name) {
            PropertyRead::Unset => true,
            PropertyRead::Value(value) => !value.contains(['\r', '\n']),
            _ => false,
        });
    let defines_ok = !parsed.define_constants_uncertain
        && !parsed
            .define_constants
            .iter()
            .any(|symbol| symbol.contains(['\r', '\n']))
        && set_outside_safely(
            parsed,
            IMPLICIT_DEFINE_PROPERTIES,
            environment,
            globals,
            false,
        )
        && !IMPLICIT_DEFINE_ITEMS
            .iter()
            .any(|item| parsed.foreign_definitions.defines_item(item));
    // The project file's own name reaches fsc in the generated sources' paths.
    if !verbatim_ok || !defines_ok || project_path.to_string_lossy().contains(['\r', '\n']) {
        return Err(NameDecline::VerbatimInput);
    }
    Ok(name)
}

/// Whether something other than the SDK may choose the compiler or reshape the
/// target graph: a selector or a `…DependsOn` global, a selector (other than
/// `DOTNET_HOST_PATH`, which the `dotnet` host sets for every build) or one of
/// [`COMPILER_ENVIRONMENT`] set in the environment, or a selector defined in a
/// document outside the SDK or in a workload manifest.
fn compiler_chosen_outside(
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
) -> bool {
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
    let defined = |defs: &ForeignDefinitions| {
        COMPILER_SELECTORS
            .iter()
            .any(|name| defs.defines_property(name))
    };
    set_in_environment
        || set_globally
        || defined(&parsed.foreign_definitions)
        || defined(&parsed.workload_definitions)
}

/// Whether `defs` may change what `-o:` names or which compile runs: define the
/// `IntermediateAssembly` item, `CoreCompile`, the `Fsc` task or a target
/// graph property, select the targets a build runs, or write at build time one
/// of the properties the name is read from.
fn overrides_compile(defs: &ForeignDefinitions) -> bool {
    defs.defines_item("IntermediateAssembly")
        || defs.defines_target("CoreCompile")
        || defs.defines_task("Fsc")
        || !defs.target_selections.is_empty()
        || defs.defines_property_where(|name| name.ends_with(TARGET_GRAPH_SUFFIX))
        || [
            "TargetName",
            "TargetExt",
            "AssemblyName",
            "IntermediateOutputPath",
            "OtherFlags",
        ]
        .iter()
        .any(|name| defs.writes_property_at_build_time(name))
}

/// Whether `name`, landing in the `IntermediateAssembly` item's `Include`
/// between the intermediate directory and the extension, is the file's whole
/// name: not empty or blank, and holding no separator (which would make part
/// of it a directory, `\` included, which MSBuild turns into `/` on Unix), no
/// wildcard or `;` (which the item expands or splits), no `$`, `@` or `%`
/// (which it may yet expand or decode), and no line break.
fn literal_file_name(name: &str) -> bool {
    !name.trim().is_empty() && !name.contains(['/', '\\', '*', '?', ';', '%', '$', '@', '\r', '\n'])
}

/// Whether `IntermediateOutputPath` prefixes the output file and the generated
/// sources safely ([`prefixes_safely`]).
///
/// When the walk trusts its value, that value says. The walk often does not
/// (the SDK's own writes read it while it may be undefined), and then the SDK's
/// construction says, provided only the SDK writes it: no global (which the
/// SDK cannot overwrite), environment variable, or document outside the SDK
/// sets it. Every SDK write is `BaseIntermediateOutputPath` followed by
/// [`INTERMEDIATE_SEGMENTS`], each ending in a separator, so the path ends in
/// one, starts as `BaseIntermediateOutputPath` does (which must be trusted
/// and start safely), and holds nothing its pieces do not (each must be exact
/// and hold nothing the item splits, expands or breaks a line at). The pieces
/// must be written by nothing outside the SDK but the environment or a
/// global, since the path holds their values when the SDK copies them, not
/// their final ones.
fn intermediate_dir_is_safe(
    parsed: &ParsedProject,
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
) -> bool {
    const NAME: &str = "IntermediateOutputPath";
    if let PropertyRead::Value(path) = parsed.property(NAME) {
        return prefixes_safely(&path);
    }
    let named = |map: &HashMap<String, String>| map.keys().any(|k| k.eq_ignore_ascii_case(NAME));
    if named(globals) || named(environment) || defined_outside_the_sdk(parsed, NAME) {
        return false;
    }
    // The SDK copies its pieces into the path while it evaluates, so a value
    // a document outside the SDK writes over them later is not the one the
    // path holds: what the path holds is then unknown. `TargetFramework`,
    // which every project writes, is the exception: a write of it after the
    // SDK has read it (in `Directory.Build.targets`, or after an explicit
    // `Sdk.targets` import) is not seen here.
    if std::iter::once(&"BaseIntermediateOutputPath")
        .chain(INTERMEDIATE_SEGMENTS)
        .any(|name| *name != "TargetFramework" && defined_outside_the_sdk(parsed, name))
    {
        return false;
    }
    let base_ok = match parsed.property("BaseIntermediateOutputPath") {
        PropertyRead::Value(base) => {
            !base.starts_with(char::is_whitespace)
                && !base.contains(UNSAFE_IN_PATH)
                && !may_read_as_option(&format!("{base}a"))
        }
        _ => false,
    };
    let segments_ok = INTERMEDIATE_SEGMENTS
        .iter()
        .all(|name| match parsed.property(name) {
            PropertyRead::Unset => true,
            PropertyRead::Value(value) => !value.contains(UNSAFE_IN_PATH),
            _ => false,
        });
    base_ok && segments_ok
}

/// Whether a document outside the .NET install may write property `name`.
/// The install's workload manifests, which every SDK project imports, are its
/// own content, as the SDK's files are, and the differential grades them on
/// each installed SDK.
fn defined_outside_the_sdk(parsed: &ParsedProject, name: &str) -> bool {
    parsed.foreign_definitions.defines_property(name)
}

/// Whether every property in `names` that something outside the SDK may set
/// (a document, a workload manifest, the environment or a global) holds a
/// trusted value with no line break, and, with `heads` set, no start fsc
/// reads as an option ([`may_read_as_option`]). A property only the SDK
/// writes is the SDK's to vouch for.
fn set_outside_safely(
    parsed: &ParsedProject,
    names: &[&str],
    environment: &HashMap<String, String>,
    globals: &HashMap<String, String>,
    heads: bool,
) -> bool {
    let named = |map: &HashMap<String, String>, name: &str| {
        map.keys().any(|k| k.eq_ignore_ascii_case(name))
    };
    names.iter().all(|name| {
        let outside = defined_outside_the_sdk(parsed, name)
            || named(environment, name)
            || named(globals, name);
        !outside
            || match parsed.property(name) {
                PropertyRead::Unset => true,
                PropertyRead::Value(value) => {
                    !value.contains(['\r', '\n']) && !(heads && may_read_as_option(&value))
                }
                _ => false,
            }
    })
}

/// What a path landing in an item's `Include` must not hold: a wildcard or
/// `;` (which the item expands or splits), a `$`, `@` or `%` (which it may yet
/// expand or decode), or a line break (which splits fsc's response-file line).
const UNSAFE_IN_PATH: [char; 8] = ['*', '?', ';', '%', '$', '@', '\r', '\n'];

/// Whether `path`, as the intermediate directory, prefixes the output file and
/// the generated sources' paths without changing what fsc reads them as: it
/// ends in a separator (else its last segment would prefix the file name),
/// starts with no white space (which the item's `Include` trims, and fsc
/// trims off a response-file line), holds nothing the item would split,
/// expand or decode, and no line break; and a path starting with it is not a
/// line fsc reads as an option, a response file or a comment.
fn prefixes_safely(path: &str) -> bool {
    (path.ends_with('/') || path.ends_with('\\'))
        && !path.starts_with(char::is_whitespace)
        && !path.contains(UNSAFE_IN_PATH)
        && !may_read_as_option(&format!("{path}a"))
}

/// Whether fsc may read a line starting `line` (trimmed) as something other
/// than a source file: an option (a leading `-`, or a leading `/` that fsc
/// takes for one: no other `/` after it, or a `:` third), a response file
/// (`@`) or a comment (`#`). `CompilerOptions.fs`, `parseOption` and
/// `isSlashOpt`.
fn may_read_as_option(line: &str) -> bool {
    let line = line.trim();
    match line.chars().next() {
        Some('-' | '@' | '#') => true,
        Some('/') => !line[1..].contains('/') || line.chars().nth(2) == Some(':'),
        _ => false,
    }
}

/// Whether fsc reads every Compile item as a source file: the walk is certain
/// of the items, and none is spelled so that fsc reads it as anything else
/// ([`may_read_as_option`], judged on its path from the project directory,
/// every component of it, or the whole path where it lies elsewhere) or holds
/// a line break.
fn sources_read_as_files(project_path: &Path, parsed: &ParsedProject) -> bool {
    if parsed.items_uncertain {
        return false;
    }
    let dir = project_path.parent().unwrap_or(Path::new(""));
    parsed.items.iter().all(|item| {
        let text = item.include.to_string_lossy();
        if text.contains(['\r', '\n']) {
            return false;
        }
        match item.include.strip_prefix(dir) {
            Ok(relative) => relative.components().all(|component| match component {
                Component::Normal(part) => {
                    let part = part.to_string_lossy();
                    !may_read_as_option(&part) && !part.contains(':')
                }
                _ => true,
            }),
            Err(_) => !may_read_as_option(&text),
        }
    })
}

/// The lines fsc reads from `flags`, as the `Fsc` task passes them: split
/// into arguments as the task splits `OtherFlags` (at white space outside
/// double quotes, the quotes removed: `FSharpCommandLineBuilder`'s
/// `ParseCommandLineArgs`), each argument then split again at line breaks,
/// as fsc reads its response file (`\r\n`, `\r` or `\n`), each line trimmed,
/// and blank lines dropped. A line starting `#` is a comment to fsc; it is
/// kept, since only its untrimmed spelling decides that.
fn fsc_lines(flags: &str) -> Vec<String> {
    let mut arguments: Vec<String> = Vec::new();
    let mut current = String::new();
    let mut started = false;
    let mut quoted = false;
    for c in flags.chars() {
        match c {
            '"' => {
                quoted = !quoted;
                started = true;
            }
            c if c.is_whitespace() && !quoted => {
                if started {
                    arguments.push(std::mem::take(&mut current));
                    started = false;
                }
            }
            c => {
                current.push(c);
                started = true;
            }
        }
    }
    if started {
        arguments.push(current);
    }
    arguments
        .iter()
        .flat_map(|argument| argument.split("\r\n").flat_map(|l| l.split(['\r', '\n'])))
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

/// Whether fsc may read `line` (one of [`fsc_lines`]) as setting its output:
/// a response file (`@`), which may hold anything, or an option whose name,
/// once its leading `-` and `/` are stripped, is `o` or `out` (fsc compares
/// option names case-sensitively, and `-O` optimises). fsc's own rule
/// (`parseOption`) takes fewer spellings: `--o:` and `-out:` are not
/// switches to it. A line starting `#` is a comment.
fn may_set_output(line: &str) -> bool {
    if line.starts_with('@') {
        return true;
    }
    if line.starts_with('#') {
        return false;
    }
    let Some(rest) = line.strip_prefix(['-', '/']) else {
        return false;
    };
    let name = rest
        .trim_start_matches(['-', '/'])
        .split([':', '='])
        .next()
        .unwrap_or("");
    name == "o" || name == "out"
}

#[cfg(test)]
mod tests {
    use super::{fsc_lines, may_read_as_option, may_set_output};

    fn sets(flags: &str) -> bool {
        fsc_lines(flags).iter().any(|l| may_set_output(l))
    }

    #[test]
    fn output_switches_are_found_in_every_spelling() {
        for flags in [
            "-o:Friend.dll",
            "--out:Friend.dll",
            "/out:Friend.dll",
            "/o:dir/Friend.dll",
            "--warnon:3390 -o Friend.dll",
            "\"--out:a b.dll\"",
            "--o\"\"ut:Friend.dll",
            "\" --out:Friend.dll\"",
            "\"--warnon:1\n--out:Friend.dll\"",
            "\"--warnon:1\r--out:Friend.dll\"",
            "@extra.rsp",
            "\"@extra.rsp\"",
        ] {
            assert!(sets(flags), "{flags:?}");
        }
        for flags in [
            "",
            "-O",
            "--OUT:Friend.dll",
            "--optimize+",
            "--warnon:3390",
            "--nowarn:44 --define:OUTER",
            "--doc:\"API out docs.xml\"",
            "out",
            "#--out:Friend.dll",
            "--warnon:1\n--nowarn:2",
        ] {
            assert!(!sets(flags), "{flags:?}");
        }
    }

    #[test]
    fn option_shaped_lines() {
        for line in ["-o:x", "@x", "#x", "/x", "/x:/y", " -x"] {
            assert!(may_read_as_option(line), "{line:?}");
        }
        for line in ["obj/x", "/abs/obj/x", "x", "./-x"] {
            assert!(!may_read_as_option(line), "{line:?}");
        }
    }
}
