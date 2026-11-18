//! Generative differential: **certainty implies exactness** for the name of
//! the assembly a project compiles to
//! ([`borzoi_msbuild::fsc::compiled_assembly_name`]).
//!
//! FCS names a project's assembly after the file fsc's `-o:` argument names,
//! up to its last dot (`TcConfigBuilder.DecideNames`), and a friend
//! assembly's `InternalsVisibleTo` is matched against that name. Our side
//! derives it from one evaluation; MSBuild's side is the arguments the real
//! `Fsc` task hands fsc, read by the oracle's `fscArgs` op (restore, then a
//! real `Build`'s targets through `Compile` with the compiler's run skipped).
//! [`fsc_output_name`] reads those arguments as fsc reads them: as the lines
//! of its response file, trimmed, the last output switch winning.
//! `fsc_args_oracle_calibration` holds that reading, and the op, to the file a
//! real compiling build writes.
//!
//! The contract, per case:
//!
//! - we commit a name ⟹ either MSBuild fails the build before fsc runs (so
//!   there is no assembly to name), or the oracle answers, the compiler it
//!   would run is the SDK's own, and fsc's output is a file of exactly that
//!   name;
//! - we decline ⟹ no claim, counted in the census by the reason we gave.
//!
//! ## The generated space
//!
//! Every route a review of the derivation found the build changing the name
//! by, as a dimension, crossed with the others:
//!
//! - `AssemblyName` and `TargetName` over an alphabet of spellings the item
//!   `-o:` comes from would split, expand, decode or read as a directory
//!   (`*`, `;`, `%41`, `%2541`, `/`, `\`, `$(…)`, `@(…)`), and harmless ones
//!   (dots, a trailing dot, padding, a colon, non-ASCII);
//! - `TargetExt` and `OutputType`;
//! - `OtherFlags` carrying an output switch in each spelling fsc reads one
//!   (`-o:`, `--out:`, `/out:`, `/o:`), padded inside quotes, after a line
//!   break inside quotes, behind a response file, mis-cased, commented out,
//!   split from its argument, or nothing of the kind;
//! - `IntermediateOutputPath` with and without its trailing separator,
//!   spelled as an option, padded, holding a `;`;
//! - each property written in the project body, `Directory.Build.props`,
//!   `Directory.Build.targets` (after the SDK's own fix-ups), after an
//!   explicit `Sdk.targets` import, as a global, or in the environment;
//! - build code outside the SDK: an inert target, a target rewriting the name
//!   or `OtherFlags` or the `IntermediateAssembly` item at build time, an
//!   evaluation-time `IntermediateAssembly` override, a replaced `CoreCompile`
//!   or `Build`, a re-invoked build, an extended `CoreCompileDependsOn`;
//! - a Compile item spelled as an output switch;
//! - a line break, followed by an output switch, in an argument the task
//!   passes verbatim (`DocumentationFile`, `DefineConstants`, `LangVersion`);
//! - the properties the SDK builds `IntermediateOutputPath` from
//!   (`Configuration`, `Platform`, `BaseIntermediateOutputPath`) holding a
//!   wildcard, a line break, or an option-shaped or padded start, or written
//!   unsafely before the SDK copies them and safely after;
//! - an escaped line break in a property the SDK turns into `#if` symbols at
//!   build time (`BackwardsCompatFrameworkDefine` on `netstandard2.1`), and
//!   the names of the sources the SDK generates spelled as options;
//! - `FscToolPath` in the environment (another compiler), and project files
//!   whose names carry dots, spaces and dashes.
//!
//! The corners ([`corners`]) pin each route once; the sweep crosses them.
//! The common SDK project (no name, or a plain `AssemblyName`, from the body
//! or `Directory.Build.props`) is a per-point must-commit, so the gate cannot
//! pass by declining everything.

mod common;

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use borzoi_msbuild::fsc::{
    CompiledAssemblyName, FSC_VERBATIM_PROPERTIES, NameDecline, compiled_assembly_name,
};
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::{glob_resolver, resolve_sdk, workloads};
use common::fsc_reading::fsc_output_name_in;
use common::{FscInvocation, Oracle, SplitMix64, parse_fsproj_with_imports};

// ---------------------------------------------------------------------------
// Cases.
// ---------------------------------------------------------------------------

/// Where a property write lands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    Body,
    DirectoryBuildProps,
    DirectoryBuildTargets,
    /// After an explicit `Sdk.targets` import, at the end of the project.
    AfterSdkTargets,
    Global,
    Environment,
}

const PLACES: &[Place] = &[
    Place::Body,
    Place::Body,
    Place::Body,
    Place::DirectoryBuildProps,
    Place::DirectoryBuildTargets,
    Place::AfterSdkTargets,
    Place::Global,
    Place::Environment,
];

/// One generated project.
#[derive(Debug, Clone, Default)]
struct Case {
    label: String,
    /// The project file's name.
    project: String,
    /// Property writes, as `(place, name, value)`, values unescaped (the
    /// renderer escapes them for XML).
    writes: Vec<(Place, String, String)>,
    /// Further raw XML: in the body, in `Directory.Build.targets`.
    body_xml: String,
    targets_xml: String,
    /// Extra Compile includes, before `A.fs`.
    compile: Vec<String>,
    /// Further files, `(relative path, contents)`.
    files: Vec<(String, String)>,
    /// Further environment variables (a selector, say).
    env: Vec<(String, String)>,
    /// The name we must commit, and MSBuild with it.
    must_commit: Option<String>,
}

impl Case {
    fn new(label: impl Into<String>) -> Case {
        Case {
            label: label.into(),
            project: "Demo.fsproj".into(),
            ..Case::default()
        }
    }
    fn write(mut self, place: Place, name: &str, value: &str) -> Case {
        self.writes.push((place, name.into(), value.into()));
        self
    }
    fn must(mut self, name: &str) -> Case {
        self.must_commit = Some(name.into());
        self
    }
    fn body(mut self, xml: &str) -> Case {
        self.body_xml.push_str(xml);
        self
    }
    fn targets(mut self, xml: &str) -> Case {
        self.targets_xml.push_str(xml);
        self
    }
    fn env(mut self, name: &str, value: &str) -> Case {
        self.env.push((name.into(), value.into()));
        self
    }
    fn compile(mut self, include: &str) -> Case {
        self.compile.push(include.into());
        self
    }

    fn globals(&self) -> Vec<(String, String)> {
        self.at(Place::Global)
    }

    fn environment(&self) -> Vec<(String, String)> {
        let mut env = self.at(Place::Environment);
        env.extend(self.env.iter().cloned());
        env
    }

    fn at(&self, place: Place) -> Vec<(String, String)> {
        self.writes
            .iter()
            .filter(|(p, _, _)| *p == place)
            .map(|(_, n, v)| (n.clone(), v.clone()))
            .collect()
    }

    fn group(&self, place: Place) -> String {
        let props: String = self
            .at(place)
            .iter()
            .map(|(n, v)| format!("<{n}>{}</{n}>", xml_text(v)))
            .collect();
        if props.is_empty() {
            String::new()
        } else {
            format!("<PropertyGroup>{props}</PropertyGroup>")
        }
    }

    fn project_xml(&self) -> String {
        let compile: String = self
            .compile
            .iter()
            .chain(std::iter::once(&"A.fs".to_string()))
            .map(|c| format!("<Compile Include=\"{}\" />", xml_text(c)))
            .collect();
        let middle = format!(
            "<PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>{}{}\
             <ItemGroup>{compile}</ItemGroup>",
            self.group(Place::Body),
            self.body_xml
        );
        let after = self.group(Place::AfterSdkTargets);
        if after.is_empty() {
            format!("<Project Sdk=\"Microsoft.NET.Sdk\">{middle}</Project>\n")
        } else {
            format!(
                "<Project><Import Project=\"Sdk.props\" Sdk=\"Microsoft.NET.Sdk\" />{middle}\
                 <Import Project=\"Sdk.targets\" Sdk=\"Microsoft.NET.Sdk\" />{after}</Project>\n"
            )
        }
    }

    /// Write the case's files under `dir`; the project file's path.
    fn lay_out(&self, dir: &Path) -> PathBuf {
        std::fs::create_dir_all(dir).unwrap();
        let project = dir.join(&self.project);
        std::fs::write(&project, self.project_xml()).unwrap();
        std::fs::write(dir.join("A.fs"), "module A\nlet x = 1\n").unwrap();
        let props = self.group(Place::DirectoryBuildProps);
        if !props.is_empty() {
            std::fs::write(
                dir.join("Directory.Build.props"),
                format!("<Project>{props}</Project>\n"),
            )
            .unwrap();
        }
        let targets = format!(
            "{}{}",
            self.group(Place::DirectoryBuildTargets),
            self.targets_xml
        );
        if !targets.is_empty() {
            std::fs::write(
                dir.join("Directory.Build.targets"),
                format!("<Project>{targets}</Project>\n"),
            )
            .unwrap();
        }
        for (name, contents) in &self.files {
            std::fs::write(dir.join(name), contents).unwrap();
        }
        project
    }
}

/// `s` as XML text or attribute content: markup escaped, and every line break
/// and tab as a character reference, which MSBuild reads as itself.
fn xml_text(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\n', "&#10;")
        .replace('\r', "&#13;")
        .replace('\t', "&#9;")
}

/// Spellings of a file name the `IntermediateAssembly` item lands it in.
const NAMES: &[&str] = &[
    "Friend",
    "My.Friend",
    "Name.",
    " Padded ",
    "Colon:Name",
    "\u{dc}n\u{ef}code",
    "with space",
    "-o:Dash",
    "#Hash",
    "Glob*",
    "Semi;Colon",
    "sub/Dir",
    "back\\slash",
    "%41scaped",
    "%2541",
    "$(MSBuildProjectName).Core",
    "@(Compile)",
    "   ",
];

const EXTENSIONS: &[&str] = &[".dll", ".exe", ".DLL", ".bin", "", ".x.dll", "dll"];

const OUTPUT_TYPES: &[&str] = &["Exe", "Library", "WinExe", "Module"];

/// `OtherFlags` values: an output switch in every spelling fsc reads one, and
/// spellings that only look like one.
const OTHER_FLAGS: &[&str] = &[
    "--warnon:3390",
    "--nowarn:44 --define:OUTER",
    "--out:obj/Other.dll",
    "-o:obj/Other.dll",
    "/out:Other.dll",
    "/o:obj/Other.dll",
    "\"--warnon:1\n--out:obj/Other.dll\"",
    "\" --out:obj/Other.dll\"",
    "@extra.rsp",
    "--OUT:obj/Other.dll",
    "#--out:obj/Other.dll",
    "-o obj/Other.dll",
    "--o:obj/Other.dll",
    "--doc:\"out docs.xml\"",
    "--out:\"obj/Spaced Other.dll\"",
    "--o\"\"ut:obj/Other.dll",
    "$(Unset)--out:obj/Other.dll",
];

const INTERMEDIATE: &[&str] = &[
    "obj/custom/",
    "obj/custom",
    "obj\\win\\",
    "obj/a.b/",
    "-o:Evil/",
    "--out:obj/Evil.dll/",
    " obj/lead/",
    "obj/semi;colon/",
];

/// Writes of the properties the SDK builds `IntermediateOutputPath` from: a
/// wildcard (which leaves `-o:` naming nothing, so fsc names its output after
/// the last source), a line break, an option-shaped or padded start, and a
/// missing separator.
const SEGMENTS: &[(&str, &str)] = &[
    ("Configuration", "Release"),
    ("Configuration", "My*Config"),
    ("Configuration", "Deb\nug"),
    ("Configuration", "-o:Evil"),
    ("Platform", "x64"),
    ("BaseIntermediateOutputPath", "build/obj/"),
    ("BaseIntermediateOutputPath", "build/obj"),
    ("BaseIntermediateOutputPath", "-o:Evil/"),
    ("BaseIntermediateOutputPath", " lead/"),
    ("BaseIntermediateOutputPath", "b\nase/"),
];

/// Build code outside the SDK.
const BUILD_CODE: &[(&str, &str)] = &[
    (
        "inert target",
        "<Target Name=\"Hello\" BeforeTargets=\"CoreCompile\"><Message Text=\"hi\" /></Target>",
    ),
    (
        "build-time TargetName",
        "<Target Name=\"Rename\" BeforeTargets=\"CoreCompile\"><PropertyGroup><TargetName>Late</TargetName></PropertyGroup></Target>",
    ),
    (
        "build-time OtherFlags",
        "<Target Name=\"Flag\" BeforeTargets=\"CoreCompile\"><PropertyGroup><OtherFlags>$(OtherFlags) --out:obj/Late.dll</OtherFlags></PropertyGroup></Target>",
    ),
    (
        "build-time IntermediateAssembly",
        "<Target Name=\"Redirect\" BeforeTargets=\"CoreCompile\"><ItemGroup><IntermediateAssembly Remove=\"@(IntermediateAssembly)\" /><IntermediateAssembly Include=\"obj/Late.dll\" /></ItemGroup></Target>",
    ),
    (
        "evaluation-time IntermediateAssembly",
        "<ItemGroup><IntermediateAssembly Remove=\"@(IntermediateAssembly)\" /><IntermediateAssembly Include=\"obj/Swapped.dll\" /></ItemGroup>",
    ),
    ("replaced CoreCompile", "<Target Name=\"CoreCompile\" />"),
    ("replaced Build", "<Target Name=\"Build\" />"),
    (
        "re-invoked build",
        "<Target Name=\"Again\" BeforeTargets=\"CoreCompile\"><MSBuild Projects=\"$(MSBuildProjectFullPath)\" Targets=\"CoreCompile\" Properties=\"AssemblyName=Again\" /></Target>",
    ),
    (
        "extended CoreCompileDependsOn",
        "<PropertyGroup><CoreCompileDependsOn>$(CoreCompileDependsOn);Hello</CoreCompileDependsOn></PropertyGroup><Target Name=\"Hello\"><Message Text=\"hi\" /></Target>",
    ),
];

/// Arguments the `Fsc` task passes verbatim, each with a line break before an
/// output switch.
const VERBATIM: &[(&str, &str)] = &[
    ("DocumentationFile", "doc.xml\n--out:obj/Doc.dll"),
    ("DefineConstants", "$(DefineConstants);A\n--out:obj/Def.dll"),
    ("LangVersion", "latest\n--out:obj/Lang.dll"),
    // An escaped line break, in a property the SDK turns into `#if` symbols
    // at build time (for a target framework old enough to read it).
    ("BackwardsCompatFrameworkDefine", "A%0A--out:obj/Def2.dll"),
    ("ImplicitFrameworkDefine", "A%0A--out:obj/Def3.dll"),
    // The names of the sources the SDK generates, spelled as options.
    ("GeneratedAssemblyInfoFile", "--out:obj/Info.dll"),
    (
        "TargetFrameworkMonikerAssemblyAttributesPath",
        "--out:obj/Attr.dll",
    ),
    ("TargetFrameworkMoniker", "x\n--out:obj/Tfm.dll"),
];

/// Target frameworks other than the default `net10.0`, whose SDK paths
/// differ: `netstandard2.1` reads `BackwardsCompatFrameworkDefine`.
const FRAMEWORKS: &[&str] = &["netstandard2.1", "net9.0"];

const PROJECT_FILES: &[&str] = &[
    "Demo.fsproj",
    "My.Lib.fsproj",
    "With Space.fsproj",
    "Dash-Name.fsproj",
];

/// One route each, by name.
fn corners() -> Vec<Case> {
    use Place::*;
    let mut cases = vec![
        Case::new("plain").must("Demo"),
        Case::new("plain AssemblyName")
            .write(Body, "AssemblyName", "Friend")
            .must("Friend"),
        Case::new("AssemblyName in Directory.Build.props")
            .write(DirectoryBuildProps, "AssemblyName", "Friend")
            .must("Friend"),
        Case::new("dotted AssemblyName")
            .write(Body, "AssemblyName", "My.Friend")
            .must("My.Friend"),
        Case::new("harmless OtherFlags")
            .write(Body, "OtherFlags", "--warnon:3390")
            .must("Demo"),
        Case::new("TargetName").write(Body, "TargetName", "File"),
        Case::new("TargetExt .exe").write(Body, "TargetExt", ".exe"),
        Case::new("TargetExt .bin").write(Body, "TargetExt", ".bin"),
        Case::new("TargetExt in Directory.Build.targets").write(
            DirectoryBuildTargets,
            "TargetExt",
            ".x.dll",
        ),
        Case::new("OutputType Exe").write(Body, "OutputType", "Exe"),
        Case::new("OutputType Module").write(Body, "OutputType", "Module"),
        Case::new("IntermediateOutputPath without separator, late").write(
            DirectoryBuildTargets,
            "IntermediateOutputPath",
            "obj/custom",
        ),
        Case::new("IntermediateOutputPath without separator, global").write(
            Global,
            "IntermediateOutputPath",
            "obj/g",
        ),
        Case::new("IntermediateOutputPath as an option, late").write(
            DirectoryBuildTargets,
            "IntermediateOutputPath",
            "--out:obj/Evil.dll/",
        ),
        Case::new("AssemblyName after Sdk.targets").write(AfterSdkTargets, "AssemblyName", "Late"),
        Case::new("TargetName after Sdk.targets").write(AfterSdkTargets, "TargetName", "Late"),
        Case::new("AssemblyName global").write(Global, "AssemblyName", "GlobalName"),
        Case::new("AssemblyName in the environment").write(Environment, "AssemblyName", "EnvName"),
        Case::new("OtherFlags in the environment").write(
            Environment,
            "OtherFlags",
            "--out:obj/Env.dll",
        ),
        Case::new("compiler from the environment")
            .write(Body, "AssemblyName", "Friend")
            .env("FscToolPath", "/nonexistent-fsc"),
        Case::new("Compile item spelled as a switch").compile("--out:obj/Src.dll"),
        Case::new("glob AssemblyName").write(Body, "AssemblyName", "Glob*"),
        Case::new("AssemblyName with a separator").write(Body, "AssemblyName", "sub/Dir"),
        Case::new("AssemblyName with a backslash").write(Body, "AssemblyName", "back\\slash"),
    ];
    for flags in OTHER_FLAGS {
        let mut case = Case::new(format!("OtherFlags {flags:?}")).write(Body, "OtherFlags", flags);
        if flags.contains("@extra.rsp") {
            case.files
                .push(("extra.rsp".into(), "--out:obj/Rsp.dll\n".into()));
        }
        cases.push(case);
    }
    for (what, xml) in BUILD_CODE {
        cases.push(Case::new(format!("build code: {what}")).targets(xml));
    }
    for (name, value) in VERBATIM {
        cases.push(Case::new(format!("line break in {name}")).write(Body, name, value));
    }
    for (name, value) in VERBATIM {
        cases.push(
            Case::new(format!("{name} {value:?} on netstandard2.1"))
                .write(Body, "TargetFramework", "netstandard2.1")
                .write(Body, name, value),
        );
    }
    for (name, value) in SEGMENTS {
        cases.push(Case::new(format!("{name} {value:?}")).write(Body, name, value));
        cases.push(Case::new(format!("{name} {value:?}, global")).write(Global, name, value));
    }
    // A piece of the intermediate directory written unsafely before the SDK
    // copies it, and safely after.
    cases.push(
        Case::new("BaseIntermediateOutputPath written twice")
            .write(Body, "BaseIntermediateOutputPath", "--out:obj/")
            .write(DirectoryBuildTargets, "BaseIntermediateOutputPath", "obj/"),
    );
    cases.push(
        Case::new("Configuration written twice")
            .write(Body, "Configuration", "Deb\nug")
            .write(DirectoryBuildTargets, "Configuration", "Debug"),
    );
    for framework in FRAMEWORKS {
        cases.push(Case::new(*framework).write(Body, "TargetFramework", framework));
    }
    for project in PROJECT_FILES {
        let mut case = Case::new(format!("project file {project:?}"));
        case.project = (*project).into();
        if *project == "My.Lib.fsproj" {
            case = case.must("My.Lib");
        }
        cases.push(case);
    }
    cases
}

/// One generated case: each dimension present with some probability, so the
/// common shapes recur and every pair of routes meets.
fn generated(rng: &mut SplitMix64, index: usize) -> Case {
    let mut case = Case::new(format!("generated #{index}"));
    let chance = |rng: &mut SplitMix64, in_eight: usize| rng.below(8) < in_eight;
    if chance(rng, 1) {
        case.project = (*rng.pick(PROJECT_FILES)).into();
    }
    if chance(rng, 4) {
        let place = *rng.pick(PLACES);
        case = case.write(place, "AssemblyName", rng.pick(NAMES));
    }
    if chance(rng, 2) {
        let place = *rng.pick(PLACES);
        case = case.write(place, "TargetName", rng.pick(NAMES));
    }
    if chance(rng, 2) {
        let place = *rng.pick(PLACES);
        case = case.write(place, "TargetExt", rng.pick(EXTENSIONS));
    }
    if chance(rng, 2) {
        let place = *rng.pick(PLACES);
        case = case.write(place, "OutputType", rng.pick(OUTPUT_TYPES));
    }
    if chance(rng, 3) {
        let place = *rng.pick(PLACES);
        let flags = *rng.pick(OTHER_FLAGS);
        case = case.write(place, "OtherFlags", flags);
        if flags.contains("@extra.rsp") {
            case.files
                .push(("extra.rsp".into(), "--out:obj/Rsp.dll\n".into()));
        }
    }
    if chance(rng, 2) {
        let place = *rng.pick(PLACES);
        case = case.write(place, "IntermediateOutputPath", rng.pick(INTERMEDIATE));
    }
    if chance(rng, 2) {
        let (_, xml) = *rng.pick(BUILD_CODE);
        if chance(rng, 4) {
            case = case.targets(xml);
        } else {
            case = case.body(xml);
        }
    }
    if chance(rng, 1) {
        let (name, value) = *rng.pick(VERBATIM);
        case = case.write(Place::Body, name, value);
    }
    if chance(rng, 1) {
        case = case.write(Place::Body, "TargetFramework", rng.pick(FRAMEWORKS));
    }
    if chance(rng, 2) {
        let (name, value) = *rng.pick(SEGMENTS);
        let place = *rng.pick(PLACES);
        case = case.write(place, name, value);
    }
    if chance(rng, 1) {
        case = case.compile("--out:obj/Src.dll");
    }
    if chance(rng, 1) {
        case = case.env("FscToolPath", "/nonexistent-fsc");
    }
    case
}

// ---------------------------------------------------------------------------
// The two sides.
// ---------------------------------------------------------------------------

/// The reads our verdict rests on, for a failure message.
const READS: &[&str] = &[
    "TargetName",
    "TargetExt",
    "IntermediateOutputPath",
    "OtherFlags",
    "AssemblyName",
];

/// Our verdict on the case laid out at `project`, the reads of [`READS`]
/// and [`FSC_VERBATIM_PROPERTIES`] it rests on, and the SDK version
/// directory our evaluation resolved (`<dotnet>/sdk/<version>`).
fn ours(case: &Case, project: &Path) -> (CompiledAssemblyName, String, Option<PathBuf>) {
    let globals: HashMap<String, String> = case.globals().into_iter().collect();
    let mut environment = common::oracle_environment();
    environment.extend(case.environment());
    let dotnet_root = common::dotnet_root_from_env();
    let (user_dotnet_root, overrides_present) = common::workload_env_from_process();
    let resolver = |name: &str, observer: &borzoi_msbuild::observed::Observer| {
        resolve_sdk(
            &dotnet_root,
            None,
            name,
            None,
            None,
            &workloads::WorkloadEnvironment {
                user_dotnet_root: user_dotnet_root.as_deref(),
                overrides_present,
                global_json: Default::default(),
                process_architecture: None,
            },
            observer,
        )
    };
    let source = host_fs::read_to_string(project).unwrap();
    let parsed = parse_fsproj_with_imports(
        &source,
        project,
        &globals,
        &environment,
        Some(&resolver),
        Some(&glob_resolver::resolve as &borzoi_msbuild::GlobResolver<'_>),
    )
    .unwrap_or_else(|e| panic!("{}: our evaluation failed: {e}", case.label));
    let reads = READS
        .iter()
        .chain(FSC_VERBATIM_PROPERTIES)
        .map(|name| format!("{name}: {:?}", parsed.property(name)))
        .collect::<Vec<_>>()
        .join("\n");
    // `<dotnet>/sdk/<version>/Sdks/Microsoft.NET.Sdk/Sdk`.
    let sdk = parsed
        .resolved_sdk_root
        .as_deref()
        .and_then(|root| root.ancestors().nth(3))
        .map(Path::to_path_buf);
    (
        compiled_assembly_name(project, &parsed, &environment, &globals),
        reads,
        sdk,
    )
}

/// Whether `invocation` runs the compiler of the SDK at `sdk` (the one our
/// evaluation resolved): that SDK's `FSharp.Build.dll` ran the `Fsc` task,
/// and handed that SDK's `fsc.dll` to the `dotnet` host of the installation
/// the tests run on, each compared as canonical paths (the devshell reaches
/// one installation through more than one tree of links).
fn runs_sdk_compiler(invocation: &FscInvocation, sdk: Option<&Path>) -> bool {
    let Some(sdk) = sdk else {
        return false;
    };
    let canonical = |path: &Path| host_fs::canonicalize(path).ok();
    let same = |a: &Path, b: &Path| canonical(a).is_some() && canonical(a) == canonical(b);
    let compiler = |name: &str| invocation.compiler.get(name).map(String::as_str);
    let fsc = compiler("DotnetFscCompilerPath")
        .and_then(|quoted| quoted.strip_prefix('"')?.strip_suffix('"'));
    same(
        Path::new(&invocation.task_assembly),
        &sdk.join("FSharp/FSharp.Build.dll"),
    ) && fsc.is_some_and(|fsc| same(Path::new(fsc), &sdk.join("FSharp/fsc.dll")))
        && compiler("ToolExe") == Some("dotnet")
        && compiler("ToolPath")
            .is_some_and(|dir| same(Path::new(dir), &common::dotnet_root_from_env()))
}

/// MSBuild's side of a case.
#[derive(Debug)]
enum Theirs {
    /// The SDK's own compiler compiles to this name.
    Name(String),
    /// MSBuild rejects the project, or fails the build before fsc runs:
    /// there is no assembly, so no name to hold ours to.
    NoBuild(Vec<String>),
    /// fsc runs, but the oracle cannot say what it compiles to: another
    /// compiler, a build it does not take for a real one, a response file it
    /// cannot read.
    Unknown(String),
}

/// How the oracle's `fscArgs` op says MSBuild built nothing: it rejected the
/// project, or failed the restore or the build before fsc ran.
const NO_BUILD: &[&str] = &[
    "MSBuild rejects the project",
    "the restore failed",
    "the build failed",
];

fn theirs(invocation: &Result<FscInvocation, Vec<String>>, sdk: Option<&Path>) -> Theirs {
    let invocation = match invocation {
        Ok(invocation) => invocation,
        Err(errors)
            if errors
                .first()
                .is_some_and(|e| NO_BUILD.contains(&e.as_str())) =>
        {
            return Theirs::NoBuild(errors.clone());
        }
        Err(errors) => return Theirs::Unknown(format!("the oracle declined: {errors:?}")),
    };
    if !runs_sdk_compiler(invocation, sdk) {
        return Theirs::Unknown(format!(
            "another compiler: {} {:?}",
            invocation.task_assembly, invocation.compiler
        ));
    }
    match fsc_output_name_in(&invocation.response_file) {
        Ok(Some(name)) => Theirs::Name(name),
        Ok(None) => Theirs::Unknown("no output switch".into()),
        Err(why) => Theirs::Unknown(why),
    }
}

/// The arguments worth showing beside a disagreement: the output switches
/// and anything after the last `-r:`.
fn interesting(invocation: &Result<FscInvocation, Vec<String>>) -> Vec<String> {
    match invocation {
        Ok(inv) => inv
            .args
            .iter()
            .filter(|a| !a.starts_with("-r:") && !a.starts_with("--define:"))
            .cloned()
            .collect(),
        Err(errors) => errors.clone(),
    }
}

#[derive(Default)]
struct Census {
    /// Commits MSBuild agreed with.
    commits: usize,
    /// Commits where MSBuild built nothing to compare with.
    commits_without_build: usize,
    declines: BTreeMap<NameDecline, usize>,
    /// Declines where the oracle had a name to give.
    declined_with_answer: BTreeMap<NameDecline, usize>,
    /// Cases MSBuild gave no name for.
    oracle_declines: usize,
}

impl Census {
    fn print(&self, what: &str) {
        let declines: usize = self.declines.values().sum();
        println!(
            "{what}: {} commits MSBuild agrees with, {} where it builds nothing, {declines} \
             declines ({} of the cases MSBuild gave no name for)",
            self.commits, self.commits_without_build, self.oracle_declines
        );
        for (reason, n) in &self.declines {
            println!(
                "  {reason:?}: {n} ({} with a name from MSBuild)",
                self.declined_with_answer.get(reason).copied().unwrap_or(0)
            );
        }
    }
}

/// Run `cases`, asserting the contract on each, and return the census.
fn run(cases: &[Case]) -> Census {
    let tmp = tempfile::TempDir::new().unwrap();
    let root = host_fs::canonicalize(tmp.path()).unwrap();
    // The oracle reads its process environment, so cases run grouped by the
    // environment they add, with one oracle alive at a time.
    let mut order: Vec<usize> = (0..cases.len()).collect();
    order.sort_by_key(|&i| cases[i].environment());
    let mut oracle: Option<(Vec<(String, String)>, Oracle)> = None;
    let mut census = Census::default();
    for i in order {
        let case = &cases[i];
        let dir = root.join(format!("case{i}"));
        let project = case.lay_out(&dir);
        let env = case.environment();
        if oracle.as_ref().is_none_or(|(current, _)| *current != env) {
            oracle = Some((env.clone(), Oracle::spawn_in_dir_with_env(&root, &env)));
        }
        let (_, oracle) = oracle.as_mut().expect("spawned above");
        let invocation = oracle.fsc_args(&project, &case.globals());
        let (verdict, reads, sdk) = ours(case, &project);
        let answer = theirs(&invocation, sdk.as_deref());
        let context = || {
            format!(
                "case {:?}\n--- project ---\n{}\n--- writes ---\n{:?}\n--- targets ---\n{}\n\
                 --- env ---\n{:?}\n--- fsc ---\n{:?}\n--- our reads ---\n{reads}",
                case.label,
                case.project_xml(),
                case.writes,
                case.targets_xml,
                case.env,
                interesting(&invocation)
            )
        };
        if std::env::var_os("BORZOI_ASSEMBLY_NAME_VERBOSE").is_some() {
            println!("{:?}: ours {verdict:?}, MSBuild {answer:?}", case.label);
        }
        if !matches!(answer, Theirs::Name(_)) {
            census.oracle_declines += 1;
        }
        match &verdict {
            CompiledAssemblyName::Known(name) => match &answer {
                Theirs::Name(theirs) => {
                    assert_eq!(
                        name,
                        theirs,
                        "certain-implies-exact violated: we commit {name:?}, fsc compiles \
                         {theirs:?}\n{}",
                        context()
                    );
                    census.commits += 1;
                }
                Theirs::NoBuild(errors) => {
                    println!(
                        "{:?}: we commit {name:?}, MSBuild builds nothing: {errors:?}",
                        case.label
                    );
                    census.commits_without_build += 1;
                }
                Theirs::Unknown(why) => panic!(
                    "certain-implies-exact violated: we commit {name:?}, but fsc runs and MSBuild \
                     cannot say what it compiles to ({why})\n{}",
                    context()
                ),
            },
            CompiledAssemblyName::Unknown(reason) => {
                *census.declines.entry(*reason).or_default() += 1;
                if matches!(answer, Theirs::Name(_)) {
                    *census.declined_with_answer.entry(*reason).or_default() += 1;
                }
            }
        }
        if let Some(expected) = &case.must_commit {
            assert!(
                verdict == CompiledAssemblyName::Known(expected.clone())
                    && matches!(&answer, Theirs::Name(theirs) if theirs == expected),
                "a must-commit point declined, moved, or went ungraded: we say {verdict:?}, \
                 MSBuild {answer:?}\n{}",
                context()
            );
        }
    }
    census
}

#[test]
fn every_route_is_exact_or_declined() {
    let census = run(&corners());
    census.print("corners");
}

#[test]
fn generated_projects_are_exact_or_declined() {
    let mut rng = SplitMix64(0x6173_6d6e_616d_6531);
    let cases: Vec<Case> = (0..40).map(|i| generated(&mut rng, i)).collect();
    let census = run(&cases);
    census.print("generated");
    assert!(
        census.commits > 0,
        "the sweep committed nothing, so it graded nothing"
    );
}

/// The sweep at volume, from a fresh seed (`BORZOI_MSBUILD_SOAK_SEED`,
/// `BORZOI_MSBUILD_SOAK_CASES`).
#[test]
#[ignore]
fn generated_projects_soak() {
    let (seed, n) = common::soak_parameters("assembly name", 400);
    let mut rng = SplitMix64(seed);
    let cases: Vec<Case> = (0..n).map(|i| generated(&mut rng, i)).collect();
    run(&cases).print("soak");
}
