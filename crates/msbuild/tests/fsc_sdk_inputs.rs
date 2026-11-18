//! The installed SDKs' files, read for the facts
//! [`borzoi_msbuild::fsc::compiled_assembly_name`] rests on that its
//! differential (`fsproj_assembly_name_generative_diff`) samples rather than
//! enumerates: which properties reach fsc's response file unsplit, and which
//! properties the SDK builds `IntermediateOutputPath` from. Each test fails,
//! naming the file and the property, when an SDK adds a route the lists do
//! not cover.

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use borzoi_msbuild::document;
use borzoi_msbuild::fsc::{
    FSC_VERBATIM_PROPERTIES, GENERATED_SOURCE_PROPERTIES, IMPLICIT_DEFINE_ITEMS,
    IMPLICIT_DEFINE_PROPERTIES, INTERMEDIATE_SEGMENTS,
};
use borzoi_msbuild::observed::host_fs::{self, HostPath};
use borzoi_msbuild::test_support::property_references;

/// Every installed SDK's version directory (`$DOTNET_ROOT/sdk/<version>`).
fn sdk_dirs() -> Vec<PathBuf> {
    let sdk = common::dotnet_root_from_env().join("sdk");
    let mut dirs: Vec<PathBuf> = host_fs::read_dir(&sdk)
        .unwrap_or_else(|e| panic!("read {}: {e}", sdk.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.join("FSharp").host_is_dir())
        .collect();
    dirs.sort();
    assert!(!dirs.is_empty(), "no SDK with F# under {}", sdk.display());
    dirs
}

/// The `.props` and `.targets` an F# project may import from `sdk`: all of
/// them but the C# and Visual Basic ones. The extension is matched in any
/// case: the F# SDK's own file is `Microsoft.FSharp.Targets`.
fn fsharp_reachable_files(sdk: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = host_fs::read_dir(dir) else {
            return;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            let Ok(kind) = entry.file_type() else {
                continue;
            };
            if kind.is_dir() {
                walk(&path, out);
            } else if kind.is_file() {
                let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
                if ext.eq_ignore_ascii_case("props") || ext.eq_ignore_ascii_case("targets") {
                    out.push(path);
                }
            }
        }
    }
    let mut files = Vec::new();
    walk(sdk, &mut files);
    files.retain(|path| {
        let text = path.to_string_lossy();
        !text.contains("/Roslyn/") && !text.contains("CSharp") && !text.contains("VisualBasic")
    });
    assert!(
        files.len() > 100,
        "{}: {} files",
        sdk.display(),
        files.len()
    );
    files
}

/// The `Fsc` task's parameters it appends to fsc's arguments verbatim, one
/// argument each (`FSharp.Build/Fsc.fs`, `generateCommandLineBuilder`:
/// `AppendSwitchIfNotNull`).
const VERBATIM_PARAMETERS: &[&str] = &[
    "BaseAddress",
    "CodePage",
    "DocumentationFile",
    "GenerateInterfaceFile",
    "KeyFile",
    "LangVersion",
    "LCID",
    "PdbFile",
    "PreferredUILang",
    "SourceLink",
    "SubsystemVersion",
    "TargetProfile",
    "VersionFile",
    "WarningLevel",
    "Win32IconFile",
    "Win32ManifestFile",
    "Win32ResourceFile",
];

/// The rest of the task's parameters, each with why it carries no argument
/// of its own the name could be read from.
const OTHER_PARAMETERS: &[(&str, &str)] = &[
    ("Condition", "not a parameter"),
    ("ChecksumAlgorithm", "mapped onto a fixed vocabulary"),
    ("CompressMetadata", "a boolean"),
    ("DebugSymbols", "a boolean"),
    ("DebugType", "mapped onto a fixed vocabulary"),
    ("DelaySign", "a boolean"),
    ("Deterministic", "a boolean"),
    ("DisabledWarnings", "split at line breaks by the task"),
    ("EmbedAllSources", "a boolean"),
    ("HighEntropyVA", "a boolean"),
    ("NoFramework", "a boolean"),
    ("NoInterfaceData", "a boolean"),
    ("NoOptimizationData", "a boolean"),
    ("Optimize", "a boolean"),
    ("ReflectionFree", "a boolean"),
    ("ParallelCompilation", "a boolean"),
    ("PathMap", "split at line breaks by the task"),
    ("Platform", "mapped onto a fixed vocabulary"),
    ("Prefer32Bit", "a boolean"),
    ("ProvideCommandLineArgs", "a boolean"),
    ("PublicSign", "a boolean"),
    ("AlwaysInline", "a boolean"),
    ("RealSig", "a boolean"),
    ("ReferencePath", "split at line breaks by the task"),
    ("RefOnly", "a boolean"),
    ("SkipCompilerExecution", "a boolean"),
    ("Tailcalls", "a boolean"),
    ("TargetType", "mapped onto a fixed vocabulary"),
    ("TreatWarningsAsErrors", "a boolean"),
    ("UseStandardResourceNames", "a boolean"),
    ("Utf8Output", "a boolean"),
    ("VisualStudioStyleErrors", "a boolean"),
    ("WarningsAsErrors", "split at line breaks by the task"),
    ("WarningsNotAsErrors", "split at line breaks by the task"),
    ("WarnOn", "split at line breaks by the task"),
    ("Nullable", "mapped onto a fixed vocabulary"),
    (
        "DefineConstants",
        "read through `ParsedProject::define_constants`",
    ),
    ("OtherFlags", "read argument by argument"),
    ("OutputAssembly", "the `-o:` itself"),
    (
        "ToolExe",
        "a compiler selector, which `compiled_assembly_name` declines on",
    ),
    (
        "ToolPath",
        "a compiler selector, which `compiled_assembly_name` declines on",
    ),
    (
        "DotnetFscCompilerPath",
        "a compiler selector, which `compiled_assembly_name` declines on",
    ),
    (
        "References",
        "item specs (resolved reference paths): see the derivation's residuals",
    ),
    (
        "Resources",
        "item specs (resource files): see the derivation's residuals",
    ),
    (
        "Embed",
        "item specs (embedded files): see the derivation's residuals",
    ),
    (
        "CompilerTools",
        "item specs (compiler tools): see the derivation's residuals",
    ),
    (
        "DisabledLanguageFeatures",
        "item specs (feature names): see the derivation's residuals",
    ),
    (
        "OutputRefAssembly",
        "the `IntermediateRefAssembly` item: `IntermediateOutputPath` and the name",
    ),
    (
        "Sources",
        "the Compile items, which `compiled_assembly_name` reads",
    ),
];

/// Every `<Fsc>` invocation in `sdk`'s F# targets.
fn fsc_invocations(sdk: &Path) -> Vec<(PathBuf, Vec<(String, String)>)> {
    let mut found = Vec::new();
    for path in fsharp_reachable_files(sdk) {
        let text = host_fs::read_to_string(&path).unwrap();
        let Ok(doc) = document::parse(&text) else {
            continue;
        };
        for node in doc.descendants().filter(|n| n.tag_name().name() == "Fsc") {
            let attributes = node
                .attributes()
                .map(|a| {
                    let value = document::attribute(node, a.name()).unwrap_or_default();
                    (a.name().to_string(), value.into_owned())
                })
                .collect();
            found.push((path.clone(), attributes));
        }
    }
    found
}

#[test]
fn fsc_verbatim_properties_cover_the_sdk_fsc_task() {
    let verbatim: BTreeSet<String> = FSC_VERBATIM_PROPERTIES
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    for sdk in sdk_dirs() {
        let invocations = fsc_invocations(&sdk);
        assert!(
            !invocations.is_empty(),
            "no <Fsc> invocation under {}",
            sdk.display()
        );
        for (file, attributes) in invocations {
            for (name, value) in attributes {
                if VERBATIM_PARAMETERS.contains(&name.as_str()) {
                    for property in property_references(&value) {
                        assert!(
                            verbatim.contains(&property.to_ascii_lowercase()),
                            "{}: <Fsc {name}=\"{value}\"> reads $({property}), which \
                             FSC_VERBATIM_PROPERTIES lacks",
                            file.display()
                        );
                    }
                } else {
                    assert!(
                        OTHER_PARAMETERS.iter().any(|(other, _)| *other == name),
                        "{}: <Fsc> parameter {name}=\"{value}\" is unclassified: is it \
                         appended verbatim?",
                        file.display()
                    );
                }
            }
        }
    }
}

/// The build-time writes, in the SDK files an F# project imports, of a
/// property in [`FSC_VERBATIM_PROPERTIES`], each with the property its value
/// comes from (which must be in the list too, or be one the derivation checks
/// otherwise).
const BUILD_TIME_VERBATIM_WRITES: &[(&str, &str, &str)] = &[
    (
        "Microsoft.Common.CurrentVersion.targets",
        "KeyOriginatorFile",
        "AssemblyOriginatorKeyFile, through ResolveKeySource",
    ),
    (
        "Microsoft.Common.CurrentVersion.targets",
        "Win32Manifest",
        "ApplicationManifest, or the SDK's default manifest",
    ),
    (
        "Microsoft.SourceLink.Common.targets",
        "SourceLink",
        "a file under IntermediateOutputPath named for the project",
    ),
];

#[test]
fn build_time_writes_of_verbatim_properties_are_listed() {
    let verbatim: BTreeSet<String> = FSC_VERBATIM_PROPERTIES
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    for sdk in sdk_dirs() {
        let mut seen = BTreeSet::new();
        for path in fsharp_reachable_files(&sdk) {
            let text = host_fs::read_to_string(&path).unwrap();
            let Ok(doc) = document::parse(&text) else {
                continue;
            };
            let file_name = path.file_name().unwrap().to_string_lossy().into_owned();
            for target in doc
                .descendants()
                .filter(|n| n.tag_name().name() == "Target")
            {
                for node in target.descendants() {
                    let written =
                        if node.parent().map(|p| p.tag_name().name()) == Some("PropertyGroup") {
                            Some(node.tag_name().name().to_string())
                        } else if node.tag_name().name() == "Output" {
                            document::attribute(node, "PropertyName").map(|n| n.into_owned())
                        } else {
                            None
                        };
                    let Some(written) = written else { continue };
                    if !verbatim.contains(&written.to_ascii_lowercase()) {
                        continue;
                    }
                    assert!(
                        BUILD_TIME_VERBATIM_WRITES
                            .iter()
                            .any(|(file, name, _)| *file == file_name
                                && name.eq_ignore_ascii_case(&written)),
                        "{}: a target writes {written}, which reaches fsc verbatim; list it in \
                         BUILD_TIME_VERBATIM_WRITES with where its value comes from",
                        path.display()
                    );
                    seen.insert((file_name.clone(), written));
                }
            }
        }
        for (file, name, _) in BUILD_TIME_VERBATIM_WRITES {
            assert!(
                seen.iter()
                    .any(|(f, n)| f == file && n.eq_ignore_ascii_case(name)),
                "{}: no target in {file} writes {name} any more; drop it from \
                 BUILD_TIME_VERBATIM_WRITES",
                sdk.display()
            );
        }
    }
}

#[test]
fn intermediate_output_path_is_built_from_the_listed_segments() {
    let allowed: BTreeSet<String> = INTERMEDIATE_SEGMENTS
        .iter()
        .chain(&["IntermediateOutputPath", "BaseIntermediateOutputPath"])
        .map(|n| n.to_ascii_lowercase())
        .collect();
    for sdk in sdk_dirs() {
        let mut writes = 0;
        for path in fsharp_reachable_files(&sdk) {
            let text = host_fs::read_to_string(&path).unwrap();
            let Ok(doc) = document::parse(&text) else {
                continue;
            };
            for node in doc.descendants().filter(|n| {
                n.tag_name()
                    .name()
                    .eq_ignore_ascii_case("IntermediateOutputPath")
            }) {
                let in_target = node.ancestors().any(|a| a.tag_name().name() == "Target");
                assert!(
                    !in_target,
                    "{}: a target writes IntermediateOutputPath",
                    path.display()
                );
                let body: String = node
                    .children()
                    .filter_map(|c| document::text(c).map(|t| t.into_owned()))
                    .collect();
                let body = body.trim();
                writes += 1;
                for property in property_references(body) {
                    assert!(
                        allowed.contains(&property.to_ascii_lowercase()),
                        "{}: IntermediateOutputPath is built from $({property}), which \
                         INTERMEDIATE_SEGMENTS lacks: {body:?}",
                        path.display()
                    );
                }
                assert!(
                    body.ends_with('\\') || body.ends_with('/'),
                    "{}: an IntermediateOutputPath write ends in no separator: {body:?}",
                    path.display()
                );
                assert!(
                    body.starts_with("$(BaseIntermediateOutputPath)")
                        || body.starts_with("$(IntermediateOutputPath)"),
                    "{}: an IntermediateOutputPath write starts with neither \
                     $(BaseIntermediateOutputPath) nor its own value: {body:?}",
                    path.display()
                );
            }
        }
        assert!(
            writes > 0,
            "no SDK write of IntermediateOutputPath under {}",
            sdk.display()
        );
    }
}

/// The text of `node` that is not a condition: its attributes but
/// `Condition`, and its own text, and its descendants'. A reference in a
/// condition decides whether a write happens, but puts no text in it.
fn unconditional_text(node: roxmltree::Node<'_, '_>) -> String {
    let mut text = String::new();
    for n in node.descendants() {
        for a in n.attributes().filter(|a| a.name() != "Condition") {
            if let Some(value) = document::attribute(n, a.name()) {
                text.push_str(&value);
                text.push(' ');
            }
        }
        if let Some(t) = document::text(n) {
            text.push_str(&t);
            text.push(' ');
        }
    }
    text
}

/// The item types `text` references (`@(Name)`, `@(Name->…)`).
fn item_references(text: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    let mut rest = text;
    while let Some(at) = rest.find("@(") {
        rest = &rest[at + 2..];
        let name: String = rest
            .trim_start()
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '-')
            .collect();
        let name = name.trim_end_matches('-');
        if !name.is_empty() {
            found.insert(name.to_ascii_lowercase());
        }
    }
    found
}

/// What a target body writes: property and item element names, and task
/// outputs' names, lowercased.
fn writes_of(target: roxmltree::Node<'_, '_>) -> BTreeSet<String> {
    let mut written = BTreeSet::new();
    for n in target.descendants() {
        let parent = n.parent().map(|p| p.tag_name().name());
        if n.is_element() && matches!(parent, Some("PropertyGroup" | "ItemGroup")) {
            written.insert(n.tag_name().name().to_ascii_lowercase());
        }
        if n.tag_name().name() == "Output" {
            for name in ["PropertyName", "ItemName"] {
                if let Some(v) = document::attribute(n, name) {
                    written.insert(v.to_ascii_lowercase());
                }
            }
        }
    }
    written
}

/// What a target that writes `DefineConstants` reads besides the symbols'
/// own lists: `DefineConstants` itself, and the Visual Basic spelling of it.
const DEFINE_TARGET_SELF: &[&str] = &["DefineConstants", "FinalDefineConstants", "Language"];

#[test]
fn implicit_define_inputs_are_listed() {
    let listed: BTreeSet<String> = IMPLICIT_DEFINE_PROPERTIES
        .iter()
        .chain(DEFINE_TARGET_SELF)
        .map(|n| n.to_ascii_lowercase())
        .collect();
    let items: BTreeSet<String> = IMPLICIT_DEFINE_ITEMS
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    for sdk in sdk_dirs() {
        let mut writers = 0;
        for path in fsharp_reachable_files(&sdk) {
            let text = host_fs::read_to_string(&path).unwrap();
            let Ok(doc) = document::parse(&text) else {
                continue;
            };
            for target in doc
                .descendants()
                .filter(|n| n.tag_name().name() == "Target")
            {
                let written = writes_of(target);
                if !written.contains("defineconstants")
                    && !written.contains("_implicitdefineconstant")
                {
                    continue;
                }
                writers += 1;
                let name = document::attribute(target, "Name").unwrap_or_default();
                let body = unconditional_text(target);
                for property in property_references(&body) {
                    assert!(
                        listed.contains(&property.to_ascii_lowercase()),
                        "{}: target {name}, which adds #if symbols, reads $({property}), \
                         which IMPLICIT_DEFINE_PROPERTIES lacks",
                        path.display()
                    );
                }
                for item in item_references(&body) {
                    assert!(
                        items.contains(&item),
                        "{}: target {name}, which adds #if symbols, reads @({item}), which \
                         IMPLICIT_DEFINE_ITEMS lacks",
                        path.display()
                    );
                }
            }
        }
        assert!(
            writers > 0,
            "no target adds #if symbols under {}",
            sdk.display()
        );
    }
}

/// Every construct in the SDK files an F# project imports that adds a
/// Compile item, by file and the item list or property it adds, with why
/// fsc reads what it adds as a source. A property head must also be in
/// [`GENERATED_SOURCE_PROPERTIES`].
const COMPILE_ADDITIONS: &[(&str, &str, &str)] = &[
    (
        "Microsoft.Common.CurrentVersion.targets",
        "$(AssemblyAttributesPath)",
        "a generated source named from IntermediateOutputPath (older SDKs)",
    ),
    (
        "Microsoft.Common.CurrentVersion.targets",
        "%(EmbeddedResource.StronglyTypedFileName)",
        "an item's metadata: an item spec, among the derivation's residuals",
    ),
    (
        "Microsoft.NET.Sdk.DefaultItems.props",
        "**/*$(DefaultLanguageSourceExtension)",
        "evaluation-time Compile items, which the derivation reads",
    ),
    (
        "Microsoft.Common.CurrentVersion.targets",
        "$(TargetFrameworkMonikerAssemblyAttributesPath)",
        "a generated source named from IntermediateOutputPath",
    ),
    (
        "Microsoft.FSharp.Targets",
        "$(TargetFrameworkMonikerAssemblyAttributesPath)",
        "a generated source named from IntermediateOutputPath",
    ),
    (
        "Microsoft.FSharp.Targets",
        "@(_FsGeneratedResXSource)",
        "sources generated under IntermediateOutputPath from resources",
    ),
    (
        "Microsoft.FSharp.Targets",
        "@(_FsGeneratedTxtSource)",
        "sources generated under IntermediateOutputPath from resources",
    ),
    (
        "Microsoft.FSharp.Targets",
        "@(__Sources)",
        "the Compile items themselves, reordered",
    ),
    (
        "Microsoft.NET.GenerateGlobalUsings.targets",
        "$(GeneratedGlobalUsingsFile)",
        "a generated source named from IntermediateOutputPath",
    ),
    (
        "Microsoft.NET.Sdk.DefaultItems.Shared.targets",
        "@(DeduplicatedCompileItems)",
        "the Compile items themselves, deduplicated",
    ),
    (
        "Microsoft.NET.GenerateAssemblyInfo.targets",
        "$(GeneratedAssemblyInfoFile)",
        "the AssemblyInfo source, written by WriteCodeFragment",
    ),
];

#[test]
fn generated_sources_are_listed() {
    let heads: BTreeSet<String> = GENERATED_SOURCE_PROPERTIES
        .iter()
        .map(|n| n.to_ascii_lowercase())
        .collect();
    let mut unlisted = BTreeSet::new();
    for sdk in sdk_dirs() {
        for path in fsharp_reachable_files(&sdk) {
            // The Razor SDK's additions are gated on a language other than F#.
            if path.to_string_lossy().contains("Microsoft.NET.Sdk.Razor") {
                continue;
            }
            let text = host_fs::read_to_string(&path).unwrap();
            let Ok(doc) = document::parse(&text) else {
                continue;
            };
            let file_name = path.file_name().unwrap().to_string_lossy().into_owned();
            for node in doc.descendants() {
                let added = if node.tag_name().name() == "Compile"
                    && node.parent().map(|p| p.tag_name().name()) == Some("ItemGroup")
                {
                    document::attribute(node, "Include").map(|v| v.into_owned())
                } else if node.tag_name().name() == "Output"
                    && document::attribute(node, "ItemName").as_deref() == Some("Compile")
                {
                    // A task's output: name it by the parameter the task
                    // writes it from, as its invocation binds it.
                    let parameter = document::attribute(node, "TaskParameter").unwrap_or_default();
                    node.parent()
                        .and_then(|task| document::attribute(task, &parameter))
                        .map(|v| v.into_owned())
                } else {
                    None
                };
                let Some(added) = added else { continue };
                let added = added.trim();
                if !COMPILE_ADDITIONS
                    .iter()
                    .any(|(file, what, _)| *file == file_name && *what == added)
                {
                    unlisted.insert(format!("({file_name:?}, {added:?})"));
                }
                if let Some(rest) = added.strip_prefix("$(") {
                    let name = rest.trim_end_matches(')').to_ascii_lowercase();
                    assert!(
                        heads.contains(&name),
                        "{}: a generated source named by $({name}), which \
                         GENERATED_SOURCE_PROPERTIES lacks",
                        path.display()
                    );
                }
            }
        }
    }
    assert!(
        unlisted.is_empty(),
        "constructs adding Compile items that COMPILE_ADDITIONS does not list, with why fsc \
         reads what they add as a source:\n{}",
        unlisted.into_iter().collect::<Vec<_>>().join("\n")
    );
}
