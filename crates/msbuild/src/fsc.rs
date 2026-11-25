//! The name of the assembly a project compiles to, from one evaluation of it
//! ([`compiled_assembly_name`]), certified over a **positive domain**.
//!
//! The name is what FCS names the assembly: the name of the file fsc's `-o:`
//! argument names, up to its last dot (`TcConfigBuilder.DecideNames`). The
//! SDK's `CoreCompile` passes `-o:$(IntermediateOutputPath)$(TargetName)$(TargetExt)`,
//! but a project can move it by many routes: an output switch in
//! `OtherFlags`, a line break in any argument fsc reads from its response
//! file, a replaced `CoreCompile`, a source spelled as an option, another
//! compiler. Listing those routes and declining each never converged: every
//! review found one more. So the derivation commits only inside a domain it
//! can state positively: every name a project sets from outside the .NET
//! install, as a property, an item type, an item's metadata, a global or an
//! environment variable, is one on an allow-list here, and each allowed
//! property's value matches the grammar listed beside it. Anything else is
//! [`CompiledAssemblyName::Unknown`]. The evaluation must be one made after
//! the project's restore (the build evaluates it again after restoring), and
//! no response file may hand the build switches the evaluation did not see.
//!
//! Each allowed name is held to the real build by
//! `tests/fsproj_assembly_name_perturbation_diff.rs`: it sets the name, at
//! each place it can be set from, to line-break and option-shaped values,
//! and asks of every name committed here that it be the one fsc's `-o:`
//! names in a real build (`borzoi_oracle_harness::msbuild_oracle::fsc_args`).
//! A name goes on a list only with that grading.
//!
//! The build's own environment ([`toolchain_variable`]) is the toolchain's,
//! which the grading holds fixed rather than perturbs: a variable there that
//! chooses another compiler is outside what is graded.
//!
//! **The register is keyed by what fsc receives.** Everything fsc is handed
//! arrives through a parameter of the SDK's `<Fsc>` invocation, a finite set
//! fixed per SDK. [`FSC_PARAMETERS`] lists each one and what feeds it (item
//! types, properties, or a literal), and [`BUILD_TIME_SITES`] every place the
//! SDK's targets add to those at build time, each with the [`Gate`] that keeps
//! it within the domain. `tests/fsc_parameter_register.rs` reads each verified
//! SDK's targets and fails on a parameter, a feed or a build-time site the
//! register does not hold, so a new SDK, or a source nobody accounted for,
//! fails a test. The gates the derivation applies to what feeds them:
//!
//! | Feed | Gate |
//! |---|---|
//! | A property, and every value it held | a name set outside the install is on `ALLOWED_PROPERTIES` (from documents, globals or variables) or `RESTORE_PROPERTIES` (from NuGet's own file only); every value it held, each write outside the install, its final value, its global and its variable, is in its grammar; any other only the SDK writes |
//! | An item type's declarations | item types on `ALLOWED_ITEM_TYPES` (`RESTORE_ITEM_TYPES` from NuGet's file only), metadata names on `ALLOWED_METADATA` (`RESTORE_METADATA` from NuGet's file only); Compile items read as source files (not as options, assemblies or resources) |
//! | The default item globs | every file under the project's directory but `bin/`, `obj/` and hidden directories ([`default_item_files`]) has a name without control characters or `%` (which MSBuild decodes as an escape) |
//! | The reference set | every path the caller builds its assembly env from ([`ReferencePaths`]) is absolute, without control characters, not option-shaped |
//! | Package content files | every build action is on [`ADMITTED_CONTENT_ACTIONS`] ([`ContentFiles`]) |
//! | Documents | no build code outside the install; no condition outside the install but in NuGet's restore files (#993: the walk cannot tell every value a condition compares, MSBuild respelling a backslash by its working directory); no item wildcard outside the install (a glob's match keeps the glob's spelling, which the walk's path does not); no expansion (`$(`, `@(`, `%(`) outside the install but in NuGet's restore files (MSBuild sets properties the walk takes for unset, `_MSBUILDTLENABLED`); no response file beside MSBuild, beside the project or above it ([`crate::AutoResponseFile::Absent`]); no `NotImported` site's file imported; no workload manifest from outside the install, and none a grading run of the SDK did not load ([`verified_manifests`]: manifests change apart from the SDK); the project's path without control characters |
//! | The environment | each variable as [`classify_variable`] finds it: the toolchain's own ([`toolchain_variable`]) held fixed; others on `ALLOWED_ENVIRONMENT` or `ALLOWED_PROPERTIES` ([`environment_decline`]) |
//! | The SDK | fixed per install; only an SDK a whole sweep has graded commits ([`verified_sdks`]) |
//!
//! Assumed rather than checked: that the assets file is the restore of the
//! project's current inputs, as the LSP's assembly env assumes it (#1044).
//!
//! A finding that names an input reaching fsc other than through a registered
//! parameter and its sites means the coverage test is wrong: fix the test
//! first, then the register.

use std::collections::{BTreeSet, HashMap};
use std::path::{Component, Path, PathBuf};

use crate::observed::Observer;
use crate::{AutoResponseFile, ParsedProject, PropertyRead};

/// What a value must look like.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grammar {
    /// `true` or `false`, in any case.
    Bool,
    /// One of these, in any case.
    OneOf(&'static [&'static str]),
    /// A target framework: an ASCII letter, then ASCII letters, digits, `.`
    /// and `-`.
    Framework,
    /// Target frameworks, separated by `;` (each trimmed).
    Frameworks,
    /// A file name fsc reads as nothing else: an ASCII letter, digit or `_`,
    /// then those, `.` and `-`, not ending in `.`.
    FileName,
    /// A dotted identifier: ASCII letters, digits, `_` and `.`, not starting
    /// with a digit or `.`.
    DottedIdentifier,
    /// Diagnostic codes: ASCII letters, digits, `;`, `,` and spaces.
    Codes,
    /// A version: ASCII letters, digits, `.`, `+` and `-`.
    Version,
    /// Text with no control character (a line break among them).
    Text,
    /// A path: no control character or `;`, and no start fsc reads as an
    /// option, a response file or a comment (`-`, `@`, `#`).
    Path,
    /// Paths of [`Grammar::Path`], separated by `;` (each trimmed).
    Paths,
    /// fsc options, separated by spaces: each `-` or `--`, a lower-case name
    /// (ASCII letters and digits, starting with a letter), then nothing, `+`,
    /// `-`, or `:` and ASCII letters, digits, `.`, `,`, `;`, `_` and `-`; and
    /// no name `o` or `out`, which set the output.
    FscOptions,
}

impl Grammar {
    /// Whether `value` is in the grammar.
    pub fn admits(self, value: &str) -> bool {
        let ascii = |c: char, extra: &str| c.is_ascii_alphanumeric() || extra.contains(c);
        match self {
            Grammar::Bool => {
                value.eq_ignore_ascii_case("true") || value.eq_ignore_ascii_case("false")
            }
            Grammar::OneOf(values) => values.iter().any(|v| v.eq_ignore_ascii_case(value)),
            Grammar::Framework => {
                value.starts_with(|c: char| c.is_ascii_alphabetic())
                    && value.chars().all(|c| ascii(c, ".-"))
            }
            Grammar::Frameworks => value
                .split(';')
                .map(str::trim)
                .filter(|f| !f.is_empty())
                .all(|f| Grammar::Framework.admits(f)),
            Grammar::FileName => {
                value.starts_with(|c: char| ascii(c, "_"))
                    && !value.ends_with('.')
                    && value.chars().all(|c| ascii(c, "_.-"))
            }
            Grammar::DottedIdentifier => {
                value.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
                    && value.chars().all(|c| ascii(c, "_."))
            }
            Grammar::Codes => value.chars().all(|c| ascii(c, ";, ")),
            Grammar::Version => !value.is_empty() && value.chars().all(|c| ascii(c, ".+-")),
            Grammar::Text => !value.chars().any(char::is_control),
            Grammar::Path => {
                !value.trim().is_empty()
                    && !value.chars().any(|c| c.is_control() || c == ';')
                    && !value.trim_start().starts_with(['-', '@', '#'])
            }
            Grammar::Paths => value
                .split(';')
                .map(str::trim)
                .filter(|p| !p.is_empty())
                .all(|p| Grammar::Path.admits(p)),
            Grammar::FscOptions => value.split(' ').filter(|t| !t.is_empty()).all(fsc_option),
        }
    }
}

/// What may follow an option of [`FSC_OPTIONS`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptionTail {
    /// Nothing: a build handing fsc `-O+` or `-g-` fails, though `-O` and
    /// `-g` compile (measured on the verified SDK).
    Bare,
    /// Nothing, `+` or `-`.
    Switch,
    /// `:` and warning numbers (digits, each optionally led by `FS`),
    /// comma-separated.
    Codes,
    /// [`Self::Switch`] or [`Self::Codes`].
    SwitchOrCodes,
    /// `:` and a conditional-compilation symbol (an ASCII identifier).
    Symbol,
}

impl OptionTail {
    /// The tails `fsproj_assembly_name_perturbation_diff` builds an option
    /// with, one of each form the tail admits.
    pub fn samples(self) -> &'static [&'static str] {
        match self {
            OptionTail::Bare => &[""],
            OptionTail::Switch => &["", "+", "-"],
            OptionTail::Codes => &[":1182", ":FS0040,1182"],
            OptionTail::SwitchOrCodes => &["", "+", "-", ":1182"],
            OptionTail::Symbol => &[":BORZOI"],
        }
    }

    fn admits(self, tail: &str) -> bool {
        let switch = matches!(tail, "" | "+" | "-");
        let codes = || {
            tail.strip_prefix(':').is_some_and(|codes| {
                codes.split(',').all(|code| {
                    let digits = code.strip_prefix("FS").unwrap_or(code);
                    !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
                })
            })
        };
        match self {
            OptionTail::Bare => tail.is_empty(),
            OptionTail::Switch => switch,
            OptionTail::Codes => codes(),
            OptionTail::SwitchOrCodes => switch || codes(),
            OptionTail::Symbol => tail.strip_prefix(':').is_some_and(|symbol| {
                symbol.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
                    && symbol
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_')
            }),
        }
    }
}

/// The options [`Grammar::FscOptions`] admits, each spelt as fsc reads it
/// (`CompilerOptions.fs`: a long option behind `--`, the one-letter ones
/// behind `-`), with what may follow. None names the output, a response file
/// or a source. `fsproj_assembly_name_perturbation_diff` builds a project
/// with each in every form [`OptionTail::samples`] gives and requires fsc to
/// compile it to the name the derivation commits to.
pub const FSC_OPTIONS: &[(&str, OptionTail)] = &[
    ("--checked", OptionTail::Switch),
    ("--crossoptimize", OptionTail::Switch),
    ("--debug", OptionTail::Switch),
    ("--define", OptionTail::Symbol),
    ("--deterministic", OptionTail::Switch),
    ("--nowarn", OptionTail::Codes),
    ("--optimize", OptionTail::Switch),
    ("--tailcalls", OptionTail::Switch),
    ("--warnaserror", OptionTail::SwitchOrCodes),
    ("--warnon", OptionTail::Codes),
    ("-O", OptionTail::Bare),
    ("-d", OptionTail::Symbol),
    ("-g", OptionTail::Bare),
];

/// Whether `token` is one fsc option of [`Grammar::FscOptions`]: an
/// [`FSC_OPTIONS`] spelling followed by a tail it admits.
fn fsc_option(token: &str) -> bool {
    FSC_OPTIONS.iter().any(|(spelling, tail)| {
        token
            .strip_prefix(spelling)
            .is_some_and(|rest| tail.admits(rest))
    })
}

/// The properties a project may set from outside the .NET install (in a
/// document, as a global or as an environment variable) and stay in the
/// domain, each with the grammar its evaluated value must match.
pub const ALLOWED_PROPERTIES: &[(&str, Grammar)] = &[
    ("AssemblyName", Grammar::FileName),
    ("Authors", Grammar::Text),
    ("Configuration", Grammar::DottedIdentifier),
    (
        "DebugType",
        Grammar::OneOf(&["portable", "embedded", "full", "pdbonly", "none"]),
    ),
    ("Description", Grammar::Text),
    ("Deterministic", Grammar::Bool),
    ("GenerateDocumentationFile", Grammar::Bool),
    ("IsPackable", Grammar::Bool),
    ("IsTestProject", Grammar::Bool),
    ("LangVersion", Grammar::Version),
    ("NoWarn", Grammar::Codes),
    ("Nullable", Grammar::OneOf(&["enable", "disable"])),
    ("Optimize", Grammar::Bool),
    ("OtherFlags", Grammar::FscOptions),
    ("OutputType", Grammar::OneOf(&["Exe", "Library", "WinExe"])),
    (
        "Platform",
        Grammar::OneOf(&["AnyCPU", "x64", "x86", "arm64"]),
    ),
    ("RootNamespace", Grammar::DottedIdentifier),
    ("TargetFramework", Grammar::Framework),
    ("TargetFrameworks", Grammar::Frameworks),
    ("TreatWarningsAsErrors", Grammar::Bool),
    ("Version", Grammar::Version),
    ("WarnOn", Grammar::Codes),
    ("WarningsAsErrors", Grammar::Codes),
];

/// The item types a document outside the .NET install may define and stay in
/// the domain. Compile items are further held to read as source files.
pub const ALLOWED_ITEM_TYPES: &[&str] = &["Compile", "Content", "None", "PackageReference"];

/// The properties NuGet's restore writes into the project's
/// `obj/<project file>.nuget.g.props` ([`restore_props`]), with their
/// grammars. Each stays in the domain only when that file alone defines it,
/// never set in another document, as a global or in the environment: a
/// project cannot then supply the evidence that it was restored
/// (`RestoreSuccess`) itself.
pub const RESTORE_PROPERTIES: &[(&str, Grammar)] = &[
    ("NuGetPackageFolders", Grammar::Paths),
    ("NuGetPackageRoot", Grammar::Path),
    ("NuGetProjectStyle", Grammar::OneOf(&["PackageReference"])),
    ("NuGetToolVersion", Grammar::Version),
    ("ProjectAssetsFile", Grammar::Path),
    ("RestoreSuccess", Grammar::Bool),
    ("RestoreTool", Grammar::OneOf(&["NuGet"])),
];

/// The prefix of the properties NuGet's restore writes for a package's folder
/// (`PkgFSharp_Core`), held as [`RESTORE_PROPERTIES`] are, with
/// [`Grammar::Path`].
pub const RESTORE_PROPERTY_PREFIX: &str = "Pkg";

/// The item types NuGet's restore writes into the same file, held as
/// [`RESTORE_PROPERTIES`] are.
pub const RESTORE_ITEM_TYPES: &[&str] = &["SourceRoot"];

/// The item metadata NuGet's restore writes into the same file on the items it
/// declares for the packages' content files, held as [`RESTORE_PROPERTIES`]
/// are.
pub const RESTORE_METADATA: &[&str] = &[
    "NuGetItemType",
    "NuGetPackageId",
    "NuGetPackageVersion",
    "Pack",
    "Private",
];

/// The file NuGet's restore writes for the project at `project_path`:
/// `obj/<project file>.nuget.g.props` beside it. `BaseIntermediateOutputPath`,
/// which moves it, is on no list.
pub fn restore_props(project_path: &Path) -> Option<PathBuf> {
    let name = project_path.file_name()?.to_str()?;
    Some(
        project_path
            .parent()?
            .join("obj")
            .join(format!("{name}.nuget.g.props")),
    )
}

/// The item metadata a document outside the .NET install may set and stay in
/// the domain.
pub const ALLOWED_METADATA: &[&str] = &[
    "CopyToOutputDirectory",
    "ExcludeAssets",
    "IncludeAssets",
    "Link",
    "PrivateAssets",
    "Version",
    "Visible",
];

/// Environment variables beyond the build's own ([`toolchain_variable`]) and
/// the [`ALLOWED_PROPERTIES`] that may be set and stay in the domain.
pub const ALLOWED_ENVIRONMENT: &[&str] = &[
    "EDITOR", "LANG", "LC_ALL", "LC_CTYPE", "LOGNAME", "OLDPWD", "PAGER", "PWD", "SHELL", "SHLVL",
    "TERM", "TZ", "USER",
];

/// Whether `name` is one of the variables the build's own environment holds,
/// which the grading holds fixed: `PATH`, `HOME`, `TMPDIR`, `RestoreSources`,
/// the `DOTNET_*` and `NUGET_*` variables, and `MSBuildUserExtensionsPath`,
/// which MSBuild computes for itself and an evaluation is handed as a
/// variable (one of that name displaces the computed value).
pub fn toolchain_variable(name: &str) -> bool {
    matches!(
        name,
        "PATH" | "HOME" | "TMPDIR" | "RestoreSources" | "MSBuildUserExtensionsPath"
    ) || name.starts_with("DOTNET_")
        || name.starts_with("NUGET_")
}

/// What an environment variable is to the derivation ([`classify_variable`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableClass {
    /// One of the build's own ([`toolchain_variable`]), held fixed.
    Toolchain,
    /// One of [`ALLOWED_PROPERTIES`] (in any case), whose value must match
    /// this grammar.
    AllowedProperty(Grammar),
    /// One of [`ALLOWED_ENVIRONMENT`] (in any case).
    Graded,
    /// On no list: declined.
    Unlisted,
}

impl VariableClass {
    /// Whether a variable of this class keeps the evaluation in the domain
    /// (an allowed property's value aside, which the derivation checks with
    /// the rest).
    pub fn admitted(self) -> bool {
        self != VariableClass::Unlisted
    }
}

/// What the variable `name` is to the derivation: the toolchain's own, an
/// allowed property, one of [`ALLOWED_ENVIRONMENT`], or on no list, in that
/// order.
pub fn classify_variable(name: &str) -> VariableClass {
    if toolchain_variable(name) {
        VariableClass::Toolchain
    } else if let Some(grammar) = allowed_property(name) {
        VariableClass::AllowedProperty(grammar)
    } else if on_list(ALLOWED_ENVIRONMENT, name) {
        VariableClass::Graded
    } else {
        VariableClass::Unlisted
    }
}

/// Why the environment `environment` takes an evaluation out of the domain,
/// or `None` when it does not (an allowed property's value aside): a
/// variable [`classify_variable`] does not admit.
pub fn environment_decline(environment: &HashMap<String, String>) -> Option<NameDecline> {
    environment
        .keys()
        .find(|name| !classify_variable(name).admitted())
        .map(|name| NameDecline::Environment(name.clone()))
}

/// The name of the assembly a project compiles to, as FCS names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledAssemblyName {
    /// The build's compiler compiles to exactly this name.
    Known(String),
    /// The project is outside the domain, for this reason.
    Unknown(NameDecline),
}

/// Why [`compiled_assembly_name`] declines.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum NameDecline {
    /// The walk did not see all of the build's content, or the SDK's own
    /// files were imported in an arrangement it did not choose: which.
    HiddenContent(String),
    /// The SDK the evaluation resolved is not one the derivation has been
    /// graded against ([`verified_sdks`]): its version directory.
    UngradedSdk(String),
    /// The evaluation is the outer build of a multi-targeted project, which
    /// compiles nothing itself, or the walk cannot tell whether it is.
    OuterBuild,
    /// The evaluation was made before the project was restored (no trusted
    /// `RestoreSuccess` from NuGet's `obj/*.nuget.g.props`). The build
    /// evaluates the project again after its restore, which may see files
    /// this evaluation did not.
    Unrestored,
    /// A response file (one beside MSBuild, a project-local `MSBuild.rsp`, a
    /// `Directory.Build.rsp`)
    /// holds switches the build's command line reads and the evaluation did
    /// not (a global, say), or the evaluation did not look for one.
    ResponseFile,
    /// A document outside the .NET install defines a target, registers a
    /// task, selects the targets a build runs, or writes a property from a
    /// target.
    BuildCode,
    /// A document outside the .NET install, other than NuGet's restore files,
    /// holds a condition: which. MSBuild may compare a value the walk holds
    /// differently (a backslash MSBuild respells by its working directory,
    /// #993), and so choose a write, an item or an import the walk does not.
    Conditional(String),
    /// A document outside the .NET install, other than NuGet's restore files,
    /// expands a property, an item or metadata: which. MSBuild sets
    /// properties the walk takes for unset (`_MSBUILDTLENABLED`, from the
    /// command line), so an expansion may read a value the walk does not.
    Expansion(String),
    /// A document outside the .NET install has an item operation with a
    /// wildcard: which. An item a glob matched keeps the glob's spelling of
    /// its directory, which is what fsc reads (`@sub/../Args.fs`, a response
    /// file), and the walk's resolved path does not.
    Glob(String),
    /// A property not on [`ALLOWED_PROPERTIES`] is set outside the .NET
    /// install, or as a global or an environment variable.
    Property(String),
    /// An item type not on [`ALLOWED_ITEM_TYPES`] is defined outside the .NET
    /// install.
    ItemType(String),
    /// Item metadata not on [`ALLOWED_METADATA`] is set outside the .NET
    /// install.
    Metadata(String),
    /// An environment variable on no list is set ([`classify_variable`]).
    Environment(String),
    /// An allowed property held a value outside its grammar, or one the walk
    /// is not certain of, at some point of the evaluation (its final value,
    /// any write a document outside the install made, its global or its
    /// environment variable): the property, and the value.
    Value(String, String),
    /// A file the SDK's default item globs can match has a name outside the
    /// path grammar, or the files were not listed: which.
    FileName(String),
    /// A path fsc is handed as a reference is not absolute, holds a control
    /// character or starts like an option, or the references were not read:
    /// which.
    ReferencePath(String),
    /// A package content file has a build action that reaches fsc, or the
    /// content files were not read: which.
    ContentFile(String),
    /// The evaluation imported an SDK file whose build-time additions the
    /// register holds unreached ([`Gate::NotImported`]): which.
    NotImported(String),
    /// The evaluation loaded a workload manifest from outside the .NET install
    /// (a user-local one), or one no grading run of the SDK loaded
    /// ([`verified_manifests`]): which.
    WorkloadManifest(String),
    /// The project's path holds a control character: the SDK spells its
    /// directory into fsc's arguments (`--pathmap:`), and its name into the
    /// generated sources'.
    ProjectPath,
    /// `TargetName` is not a trusted [`Grammar::FileName`], or `TargetExt` not
    /// a trusted `.dll` or `.exe`.
    Name,
    /// The walk is not certain of the Compile items, or fsc may read one as
    /// something other than a source file.
    Sources,
}

/// The files under a project's directory that the SDK's default item globs
/// can match ([`default_item_files`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefaultItemFiles {
    /// Not listed.
    Unread,
    /// The walk could not list them, for this reason.
    Declined(String),
    /// These, as absolute paths.
    Listed(Vec<PathBuf>),
}

/// The files the SDK's default item globs can match for the project at
/// `project_path`: every file under its directory (`**/*`, the default `None`
/// glob, a superset of the default `EmbeddedResource` glob `**/*.resx`, whose
/// items reach fsc as `--resource:` arguments), but for the SDK's fixed
/// excludes, which the walk does not enter: `bin/` and `obj/` beside the
/// project and every hidden directory. Listed through `observer`. A link
/// declines: the globs follow one, and it may lead anywhere.
pub fn default_item_files(project_path: &Path, observer: &Observer) -> DefaultItemFiles {
    // MSBuild folds `..` in the project's path before it enumerates the
    // directory; reading through `link/..` would list the link's target's
    // parent instead. A path without a root would be read against this
    // process's working directory, and lose a leading `..`.
    if !project_path.has_root() {
        return DefaultItemFiles::Unread;
    }
    let project_path = lexical(project_path);
    let Some(dir) = project_path.parent() else {
        return DefaultItemFiles::Unread;
    };
    let mut files = Vec::new();
    let mut pending = vec![(dir.to_path_buf(), true)];
    while let Some((dir, top)) = pending.pop() {
        let entries = match crate::observed::read_dir(observer, &dir) {
            Ok(entries) => entries,
            Err(e) => return DefaultItemFiles::Declined(format!("{}: {e:?}", dir.display())),
        };
        for entry in entries {
            let entry = match entry {
                Ok(entry) => entry,
                Err(e) => return DefaultItemFiles::Declined(format!("{}: {e:?}", dir.display())),
            };
            let name = entry.name.to_string_lossy();
            match entry.kind {
                Ok(crate::observed::EntryKind::Dir) => {
                    let excluded =
                        name.starts_with('.') || (top && (name == "bin" || name == "obj"));
                    if !excluded {
                        pending.push((entry.path, false));
                    }
                }
                Ok(crate::observed::EntryKind::File) => files.push(entry.path),
                other => {
                    return DefaultItemFiles::Declined(format!(
                        "{} is {other:?}",
                        entry.path.display()
                    ));
                }
            }
        }
    }
    files.sort();
    DefaultItemFiles::Listed(files)
}

/// The paths fsc is handed as references (`-r:`) for the project: the set the
/// caller builds its assembly env from, the assets file's package and
/// framework compile assets. (Project references are outside the domain: the
/// `ProjectReference` item type is on no list.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReferencePaths {
    /// Not read.
    Unread,
    /// These.
    Listed(Vec<PathBuf>),
}

/// The content files the project's packages contribute, by the assets file's
/// `contentFiles` entries: each one's path and build action. The SDK's
/// `RunProduceContentAssets` adds each to the item type its build action
/// names, so one whose action is `Compile` or `EmbeddedResource` reaches fsc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContentFiles {
    /// Not read.
    Unread,
    /// These, as `(path, build action)`.
    Listed(Vec<(String, String)>),
}

/// The content-file build actions the domain admits: those naming an item
/// type no `Fsc` parameter is fed from ([`FSC_PARAMETERS`]). A package content
/// file with any other action declines.
pub const ADMITTED_CONTENT_ACTIONS: &[&str] = &["None", "Content"];

/// What the caller hands the derivation beside the evaluation: what the
/// evaluation saw of the process, and what it reads from the file system and
/// the assets file for the same project.
#[derive(Debug, Clone, Copy)]
pub struct NameInputs<'a> {
    /// The process environment the evaluation saw.
    pub environment: &'a HashMap<String, String>,
    /// The global properties it was made under.
    pub globals: &'a HashMap<String, String>,
    /// The files the SDK's default item globs can match.
    pub files: &'a DefaultItemFiles,
    /// The reference set the caller builds its assembly env from.
    pub references: &'a ReferencePaths,
    /// The packages' content files.
    pub content: &'a ContentFiles,
}

/// What feeds one parameter of the SDK's `<Fsc>` invocation in
/// `FSharp/Microsoft.FSharp.Targets`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Feed {
    /// A literal the invocation spells out.
    Literal,
    /// These properties' values. A property the domain admits is held to its
    /// grammar over every value it held; any other only the SDK writes. Each
    /// write the SDK's targets make at build time is a [`BuildTimeSite`].
    Properties(&'static [&'static str]),
    /// These item types' items. An item type the domain admits is held to its
    /// rules; any other only the SDK declares. Each addition the SDK's targets
    /// make at build time is a [`BuildTimeSite`].
    Items(&'static [&'static str]),
}

/// One parameter of the SDK's `<Fsc>` invocation, and what feeds it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FscParameter {
    /// The parameter's name, as the invocation spells it.
    pub name: &'static str,
    /// Its value exactly as MSBuild decodes it: the whole
    /// expression, so an input [`Self::feed`] does not name (item metadata, a
    /// property function) is a difference.
    pub expression: &'static str,
    /// What feeds it.
    pub feed: Feed,
}

/// What a [`BuildTimeSite`] writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SiteKind {
    /// Items of an item type.
    Item,
    /// A property.
    Property,
}

/// Why a [`BuildTimeSite`] cannot move what fsc is handed past the domain's
/// gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gate {
    /// It re-adds, reorders or re-labels the type's own items.
    Restates,
    /// It adds a file the SDK writes under `IntermediateOutputPath`, named from
    /// properties the domain holds to grammars or only the SDK writes.
    Generated,
    /// It adds the packages' content files under the item types their build
    /// actions name: [`ContentFiles`], of which the domain admits only
    /// [`ADMITTED_CONTENT_ACTIONS`].
    PackageContent,
    /// It adds items made from `EmbeddedResource` items: the default `.resx`
    /// glob's (held to the file-name grammar, [`default_item_files`]), and the
    /// packages' content files' ([`Gate::PackageContent`]). A project's own are
    /// on no list.
    EmbeddedResources,
    /// It adds the reference set: [`ReferencePaths`].
    References,
    /// It selects from the Compile items, which the item rule holds (SourceLink
    /// embedding the sources source control does not track).
    FromCompile,
    /// It runs only for project references, whose item type is on no list.
    ProjectReferences,
    /// It is in a file an F# project of the domain does not import: another
    /// language's or another SDK's targets. The derivation declines an
    /// evaluation that imported one, by the file's canonical place in the SDK
    /// ([`crate::ParsedProject::imported_sdk_files`]).
    NotImported,
    /// It writes the property from properties alone, which the property rule
    /// covers.
    Properties,
    /// It writes `PathMap` from the `SourceRoot` items: the restore's package
    /// folder (held to its grammar) and SourceLink's repository root (an
    /// ancestor of the project's directory, held to the project-path rule).
    SourceRoots,
    /// It runs only under this, which no project of the domain can set.
    Unreachable(&'static str),
}

/// One write the SDK's targets make, at build time (inside a `<Target>`), to an
/// item type or property an [`FscParameter`] is fed from: each write its own
/// row, so a new one in a target the register already names is unregistered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuildTimeSite {
    /// What it writes.
    pub kind: SiteKind,
    /// The item type or property, as spelled; a computed name (holding `%(`,
    /// `$(` or `@(`) may stand for any.
    pub name: &'static str,
    /// The file, relative to the SDK's version directory.
    pub file: &'static str,
    /// The target it is in.
    pub target: &'static str,
    /// The write itself, each value exactly as MSBuild decodes it: an item's operation and value,
    /// its other attributes sorted and its metadata elements
    /// (`Include=@(Embed) KeepDuplicates=false`); a property's value; or a
    /// task output's task, its inputs sorted, and the output parameter
    /// (`CreateItem(Include=@(_ProcessedContentItems)) Output=Include`).
    pub write: &'static str,
    /// Every condition it runs under, outermost first, each exactly as
    /// written: its target's, its group's or its task's, and its own.
    pub conditions: &'static [&'static str],
    /// Why it stays within the domain.
    pub gate: Gate,
}

/// **The register.** Every parameter the verified SDKs' `<Fsc>` invocation
/// passes, and what feeds it: everything fsc receives arrives through one of
/// them. `tests/fsc_parameter_register.rs` reads each verified SDK's targets
/// and fails if a parameter, its expression or its feed differs from this.
pub const FSC_PARAMETERS: &[FscParameter] = &[
    FscParameter {
        name: "BaseAddress",
        expression: r#"$(BaseAddress)"#,
        feed: Feed::Properties(&["BaseAddress"]),
    },
    FscParameter {
        name: "ChecksumAlgorithm",
        expression: r#"$(PdbChecksumAlgorithm)"#,
        feed: Feed::Properties(&["PdbChecksumAlgorithm"]),
    },
    FscParameter {
        name: "CodePage",
        expression: r#"$(CodePage)"#,
        feed: Feed::Properties(&["CodePage"]),
    },
    FscParameter {
        name: "CompilerTools",
        expression: r#"@(FscCompilerTools)"#,
        feed: Feed::Items(&["FscCompilerTools"]),
    },
    FscParameter {
        name: "CompressMetadata",
        expression: r#"$(CompressMetadata)"#,
        feed: Feed::Properties(&["CompressMetadata"]),
    },
    FscParameter {
        name: "DebugSymbols",
        expression: r#"$(DebugSymbols)"#,
        feed: Feed::Properties(&["DebugSymbols"]),
    },
    FscParameter {
        name: "DebugType",
        expression: r#"$(DebugType)"#,
        feed: Feed::Properties(&["DebugType"]),
    },
    FscParameter {
        name: "DefineConstants",
        expression: r#"$(DefineConstants)"#,
        feed: Feed::Properties(&["DefineConstants"]),
    },
    FscParameter {
        name: "DelaySign",
        expression: r#"$(DelaySign)"#,
        feed: Feed::Properties(&["DelaySign"]),
    },
    FscParameter {
        name: "Deterministic",
        expression: r#"$(Deterministic)"#,
        feed: Feed::Properties(&["Deterministic"]),
    },
    FscParameter {
        name: "DisabledWarnings",
        expression: r#"$(NoWarn)"#,
        feed: Feed::Properties(&["NoWarn"]),
    },
    FscParameter {
        name: "DocumentationFile",
        expression: r#"$(DocumentationFile)"#,
        feed: Feed::Properties(&["DocumentationFile"]),
    },
    FscParameter {
        name: "DotnetFscCompilerPath",
        expression: r#"$(DotnetFscCompilerPath)"#,
        feed: Feed::Properties(&["DotnetFscCompilerPath"]),
    },
    FscParameter {
        name: "EmbedAllSources",
        expression: r#"$(EmbedAllSources)"#,
        feed: Feed::Properties(&["EmbedAllSources"]),
    },
    FscParameter {
        name: "Embed",
        expression: r#"@(EmbeddedFiles)"#,
        feed: Feed::Items(&["EmbeddedFiles"]),
    },
    FscParameter {
        name: "GenerateInterfaceFile",
        expression: r#"$(GenerateInterfaceFile)"#,
        feed: Feed::Properties(&["GenerateInterfaceFile"]),
    },
    FscParameter {
        name: "HighEntropyVA",
        expression: r#"$(HighEntropyVA)"#,
        feed: Feed::Properties(&["HighEntropyVA"]),
    },
    FscParameter {
        name: "KeyFile",
        expression: r#"$(KeyOriginatorFile)"#,
        feed: Feed::Properties(&["KeyOriginatorFile"]),
    },
    FscParameter {
        name: "LangVersion",
        expression: r#"$(LangVersion)"#,
        feed: Feed::Properties(&["LangVersion"]),
    },
    FscParameter {
        name: "DisabledLanguageFeatures",
        expression: r#"@(DisabledLanguageFeatures)"#,
        feed: Feed::Items(&["DisabledLanguageFeatures"]),
    },
    FscParameter {
        name: "LCID",
        expression: r#"$(LCID)"#,
        feed: Feed::Properties(&["LCID"]),
    },
    FscParameter {
        name: "NoFramework",
        expression: r#"true"#,
        feed: Feed::Literal,
    },
    FscParameter {
        name: "NoInterfaceData",
        expression: r#"$(NoInterfaceData)"#,
        feed: Feed::Properties(&["NoInterfaceData"]),
    },
    FscParameter {
        name: "NoOptimizationData",
        expression: r#"$(NoOptimizationData)"#,
        feed: Feed::Properties(&["NoOptimizationData"]),
    },
    FscParameter {
        name: "Optimize",
        expression: r#"$(Optimize)"#,
        feed: Feed::Properties(&["Optimize"]),
    },
    FscParameter {
        name: "ReflectionFree",
        expression: r#"$(ReflectionFree)"#,
        feed: Feed::Properties(&["ReflectionFree"]),
    },
    FscParameter {
        name: "OtherFlags",
        expression: r#"$(FscOtherFlags)"#,
        feed: Feed::Properties(&["FscOtherFlags"]),
    },
    FscParameter {
        name: "OutputAssembly",
        expression: r#"@(IntermediateAssembly)"#,
        feed: Feed::Items(&["IntermediateAssembly"]),
    },
    FscParameter {
        name: "OutputRefAssembly",
        expression: r#"@(IntermediateRefAssembly)"#,
        feed: Feed::Items(&["IntermediateRefAssembly"]),
    },
    FscParameter {
        name: "ParallelCompilation",
        expression: r#"$(ParallelCompilation)"#,
        feed: Feed::Properties(&["ParallelCompilation"]),
    },
    FscParameter {
        name: "PathMap",
        expression: r#"$(PathMap)"#,
        feed: Feed::Properties(&["PathMap"]),
    },
    FscParameter {
        name: "PdbFile",
        expression: r#"$(PdbFile)"#,
        feed: Feed::Properties(&["PdbFile"]),
    },
    FscParameter {
        name: "Platform",
        expression: r#"$(PlatformTarget)"#,
        feed: Feed::Properties(&["PlatformTarget"]),
    },
    FscParameter {
        name: "Prefer32Bit",
        expression: r#"$(Actual32Bit)"#,
        feed: Feed::Properties(&["Actual32Bit"]),
    },
    FscParameter {
        name: "PreferredUILang",
        expression: r#"$(PreferredUILang)"#,
        feed: Feed::Properties(&["PreferredUILang"]),
    },
    FscParameter {
        name: "ProvideCommandLineArgs",
        expression: r#"$(ProvideCommandLineArgs)"#,
        feed: Feed::Properties(&["ProvideCommandLineArgs"]),
    },
    FscParameter {
        name: "PublicSign",
        expression: r#"$(PublicSign)"#,
        feed: Feed::Properties(&["PublicSign"]),
    },
    FscParameter {
        name: "AlwaysInline",
        expression: r#"$(AlwaysInline)"#,
        feed: Feed::Properties(&["AlwaysInline"]),
    },
    FscParameter {
        name: "RealSig",
        expression: r#"$(RealSig)"#,
        feed: Feed::Properties(&["RealSig"]),
    },
    FscParameter {
        name: "References",
        expression: r#"@(ReferencePathWithRefAssemblies)"#,
        feed: Feed::Items(&["ReferencePathWithRefAssemblies"]),
    },
    FscParameter {
        name: "ReferencePath",
        expression: r#"$(ReferencePathWithRefAssemblies)"#,
        feed: Feed::Properties(&["ReferencePathWithRefAssemblies"]),
    },
    FscParameter {
        name: "RefOnly",
        expression: r#"$(ProduceOnlyReferenceAssembly)"#,
        feed: Feed::Properties(&["ProduceOnlyReferenceAssembly"]),
    },
    FscParameter {
        name: "Resources",
        expression: r#"@(ActualEmbeddedResources)"#,
        feed: Feed::Items(&["ActualEmbeddedResources"]),
    },
    FscParameter {
        name: "SkipCompilerExecution",
        expression: r#"$(SkipCompilerExecution)"#,
        feed: Feed::Properties(&["SkipCompilerExecution"]),
    },
    FscParameter {
        name: "SourceLink",
        expression: r#"$(SourceLink)"#,
        feed: Feed::Properties(&["SourceLink"]),
    },
    FscParameter {
        name: "Sources",
        expression: r#"@(Compile)"#,
        feed: Feed::Items(&["Compile"]),
    },
    FscParameter {
        name: "SubsystemVersion",
        expression: r#"$(SubsystemVersion)"#,
        feed: Feed::Properties(&["SubsystemVersion"]),
    },
    FscParameter {
        name: "Tailcalls",
        expression: r#"$(Tailcalls)"#,
        feed: Feed::Properties(&["Tailcalls"]),
    },
    FscParameter {
        name: "TargetType",
        expression: r#"$(OutputType)"#,
        feed: Feed::Properties(&["OutputType"]),
    },
    FscParameter {
        name: "TargetProfile",
        expression: r#"$(TargetProfile)"#,
        feed: Feed::Properties(&["TargetProfile"]),
    },
    FscParameter {
        name: "ToolExe",
        expression: r#"$(FscToolExe)"#,
        feed: Feed::Properties(&["FscToolExe"]),
    },
    FscParameter {
        name: "ToolPath",
        expression: r#"$(FscToolPath)"#,
        feed: Feed::Properties(&["FscToolPath"]),
    },
    FscParameter {
        name: "TreatWarningsAsErrors",
        expression: r#"$(TreatWarningsAsErrors)"#,
        feed: Feed::Properties(&["TreatWarningsAsErrors"]),
    },
    FscParameter {
        name: "UseStandardResourceNames",
        expression: r#"$(UseStandardResourceNames)"#,
        feed: Feed::Properties(&["UseStandardResourceNames"]),
    },
    FscParameter {
        name: "Utf8Output",
        expression: r#"$(Utf8Output)"#,
        feed: Feed::Properties(&["Utf8Output"]),
    },
    FscParameter {
        name: "VersionFile",
        expression: r#"$(VersionFile)"#,
        feed: Feed::Properties(&["VersionFile"]),
    },
    FscParameter {
        name: "VisualStudioStyleErrors",
        expression: r#"$(VisualStudioStyleErrors)"#,
        feed: Feed::Properties(&["VisualStudioStyleErrors"]),
    },
    FscParameter {
        name: "WarningLevel",
        expression: r#"$(WarningLevel)"#,
        feed: Feed::Properties(&["WarningLevel"]),
    },
    FscParameter {
        name: "WarningsAsErrors",
        expression: r#"$(WarningsAsErrors)"#,
        feed: Feed::Properties(&["WarningsAsErrors"]),
    },
    FscParameter {
        name: "WarningsNotAsErrors",
        expression: r#"$(WarningsNotAsErrors)"#,
        feed: Feed::Properties(&["WarningsNotAsErrors"]),
    },
    FscParameter {
        name: "WarnOn",
        expression: r#"$(WarnOn)"#,
        feed: Feed::Properties(&["WarnOn"]),
    },
    FscParameter {
        name: "Win32IconFile",
        expression: r#"$(ApplicationIcon)"#,
        feed: Feed::Properties(&["ApplicationIcon"]),
    },
    FscParameter {
        name: "Win32ManifestFile",
        expression: r#"$(Win32Manifest)"#,
        feed: Feed::Properties(&["Win32Manifest"]),
    },
    FscParameter {
        name: "Win32ResourceFile",
        expression: r#"$(Win32Resource)"#,
        feed: Feed::Properties(&["Win32Resource"]),
    },
    FscParameter {
        name: "Nullable",
        expression: r#"$(Nullable)"#,
        feed: Feed::Properties(&["Nullable"]),
    },
];

/// Every build-time addition the verified SDKs' targets make to what
/// [`FSC_PARAMETERS`] is fed from, with its gate. The same test scans every
/// `.targets` and `.props` file of each verified SDK and fails on a site not
/// here, or one here it does not find.
pub const BUILD_TIME_SITES: &[BuildTimeSite] = &[
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"%(_MSBuildProjectReferenceExistent.OutputItemType)"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "ResolveProjectReferences",
        write: r#"MSBuild(BuildInParallel=$(BuildInParallel), ContinueOnError=!$(BuildingProject), Projects=@(_MSBuildProjectReferenceExistent), Properties=%(_MSBuildProjectReferenceExistent.SetConfiguration); %(_MSBuildProjectReferenceExistent.SetPlatform); %(_MSBuildProjectReferenceExistent.SetTargetFramework), RemoveProperties=%(_MSBuildProjectReferenceExistent.GlobalPropertiesToRemove)$(_GlobalPropertiesToRemoveFromProjectReferences), Targets=GetTargetPath) Output=TargetOutputs"#,
        conditions: &[
            r#"'%(_MSBuildProjectReferenceExistent.BuildReference)' == 'true' and '@(ProjectReferenceWithConfiguration)' != '' and ('$(BuildingInsideVisualStudio)' == 'true' or '$(BuildProjectReferences)' != 'true') and '$(VisualStudioVersion)' != '10.0' and '@(_MSBuildProjectReferenceExistent)' != ''"#,
            r#"'%(_MSBuildProjectReferenceExistent.OutputItemType)' != ''"#,
        ],
        gate: Gate::ProjectReferences,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"%(_MSBuildProjectReferenceExistent.OutputItemType)"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "ResolveProjectReferences",
        write: r#"MSBuild(BuildInParallel=$(BuildInParallel), ContinueOnError=$(ContinueOnError), Projects=@(_MSBuildProjectReferenceExistent), Properties=%(_MSBuildProjectReferenceExistent.SetConfiguration); %(_MSBuildProjectReferenceExistent.SetPlatform);  %(_MSBuildProjectReferenceExistent.SetTargetFramework), RemoveProperties=%(_MSBuildProjectReferenceExistent.GlobalPropertiesToRemove)$(_GlobalPropertiesToRemoveFromProjectReferences), Targets=%(_MSBuildProjectReferenceExistent.Targets)) Output=TargetOutputs"#,
        conditions: &[
            r#"'%(_MSBuildProjectReferenceExistent.BuildReference)' == 'true' and '@(ProjectReferenceWithConfiguration)' != '' and '$(BuildingInsideVisualStudio)' != 'true' and '$(BuildProjectReferences)' == 'true' and '@(_MSBuildProjectReferenceExistent)' != ''"#,
            r#"'%(_MSBuildProjectReferenceExistent.OutputItemType)' != ''"#,
        ],
        gate: Gate::ProjectReferences,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"%(_ProcessedContentItems.ProcessedItemType)"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.PackageDependencyResolution.targets",
        target: "RunProduceContentAssets",
        write: r#"CreateItem(Include=@(_ProcessedContentItems)) Output=Include"#,
        conditions: &[
            r#"'@(_ContentFilesToPreprocess)' != '' and '$(_CleaningWithoutRebuilding)' != 'true'"#,
            r#"'@(_ProcessedContentItems)' != ''"#,
        ],
        gate: Gate::PackageContent,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ActualEmbeddedResources"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"Include=@(_CoreCompileResourceInputs);@(CompiledLicenseFile);@(AdditionalEmbeddedResource)"#,
        conditions: &[r#" '$(UsingXBuild)' != 'true'"#],
        gate: Gate::EmbeddedResources,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ActualEmbeddedResources"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"Include=@(_CoreCompileResourceInputs);@(ManifestResourceWithNoCulture);@(ManifestNonResxWithNoCultureOnDisk);@(CompiledLicenseFile);@(AdditionalEmbeddedResource)"#,
        conditions: &[r#" '$(UsingXBuild)' == 'true'"#],
        gate: Gate::EmbeddedResources,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Overrides.NetSdk.targets",
        target: "CoreGenerateAssemblyInfo",
        write: r#"Remove=$(GeneratedAssemblyInfoFile)"#,
        conditions: &[r#"'$(Language)'=='F#'"#],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "FSharpSourceCodeCompileOrder",
        write: r#"Include=@(__Sources)"#,
        conditions: &[],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "FSharpSourceCodeCompileOrder",
        write: r#"Remove=@(Compile)"#,
        conditions: &[],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "GenerateFSharpTextResources",
        write: r#"Include=@(_FsGeneratedResXSource) CompileOrder=CompileBefore"#,
        conditions: &[],
        gate: Gate::EmbeddedResources,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "GenerateFSharpTextResources",
        write: r#"Include=@(_FsGeneratedTxtSource) CompileOrder=CompileBefore"#,
        conditions: &[],
        gate: Gate::EmbeddedResources,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "GenerateTargetFrameworkMonikerAttribute",
        write: r#"Include=$(TargetFrameworkMonikerAssemblyAttributesPath) <CompileOrder>=CompileBefore"#,
        conditions: &[
            r#"'$(GenerateTargetFrameworkAttribute)' == 'true'"#,
            r#"'$(AdditionalSourcesText)' != ''"#,
        ],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "CoreResGen",
        write: r#"GenerateResource(AdditionalInputs=$(MSBuildAllProjects), EnvironmentVariables=$(ResGenEnvironment), ExecuteAsTool=$(ResGenExecuteAsTool), MSBuildArchitecture=$(GenerateResourceMSBuildArchitecture), MSBuildRuntime=$(GenerateResourceMSBuildRuntime), NeverLockTypeAssemblies=$(GenerateResourceNeverLockTypeAssemblies), OutputResources=@(EmbeddedResource->'$(IntermediateOutputPath)%(ManifestResourceName).resources'), PublicClass=%(EmbeddedResource.PublicClass), References=@(ReferencePathWithRefAssemblies), SdkToolsPath=$(ResgenToolPath), Sources=@(EmbeddedResource), StateFile=$(IntermediateOutputPath)$(MSBuildProjectFile).GenerateResource.cache, StronglyTypedClassName=%(EmbeddedResource.StronglyTypedClassName), StronglyTypedFileName=%(EmbeddedResource.StronglyTypedFileName), StronglyTypedLanguage=%(EmbeddedResource.StronglyTypedLanguage), StronglyTypedManifestPrefix=%(EmbeddedResource.StronglyTypedManifestPrefix), StronglyTypedNamespace=%(EmbeddedResource.StronglyTypedNamespace), UsePreserializedResources=$(GenerateResourceUsePreserializedResources), UseSourcePath=$(UseSourcePath), WarnOnBinaryFormatterUse=$(GenerateResourceWarnOnBinaryFormatterUse)) Output=StronglyTypedFileName"#,
        conditions: &[
            r#"'%(EmbeddedResource.Type)' == 'Resx' and '%(EmbeddedResource.GenerateResource)' != 'false' and '$(GenerateResourceMSBuildRuntime)' != 'CLR2'"#,
        ],
        gate: Gate::Unreachable("the `StronglyTyped*` metadata of `EmbeddedResource`, on no list"),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "CoreResGen",
        write: r#"GenerateResource(AdditionalInputs=$(MSBuildAllProjects), MSBuildArchitecture=$(GenerateResourceMSBuildArchitecture), MSBuildRuntime=$(GenerateResourceMSBuildRuntime), NeverLockTypeAssemblies=$(GenerateResourceNeverLockTypeAssemblies), OutputResources=@(EmbeddedResource->'$(IntermediateOutputPath)%(ManifestResourceName).resources'), PublicClass=%(EmbeddedResource.PublicClass), References=@(ReferencePath), Sources=@(EmbeddedResource), StateFile=$(IntermediateOutputPath)$(MSBuildProjectFile).GenerateResource.cache, StronglyTypedClassName=%(EmbeddedResource.StronglyTypedClassName), StronglyTypedFileName=%(EmbeddedResource.StronglyTypedFileName), StronglyTypedLanguage=%(EmbeddedResource.StronglyTypedLanguage), StronglyTypedManifestPrefix=%(EmbeddedResource.StronglyTypedManifestPrefix), StronglyTypedNamespace=%(EmbeddedResource.StronglyTypedNamespace), UseSourcePath=$(UseSourcePath)) Output=StronglyTypedFileName"#,
        conditions: &[
            r#"'%(EmbeddedResource.Type)' == 'Resx' and '%(EmbeddedResource.GenerateResource)' != 'false' and '$(GenerateResourceMSBuildRuntime)' == 'CLR2'"#,
        ],
        gate: Gate::Unreachable("the `StronglyTyped*` metadata of `EmbeddedResource`, on no list"),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "GenerateAdditionalSources",
        write: r#"WriteCodeFragment(AssemblyAttributes=@(AssemblyAttributes), Language=$(Language), OutputFile=$(AssemblyAttributesPath)) Output=OutputFile"#,
        conditions: &[
            r#"'@(AssemblyAttributes)' != '' and '$(GenerateAdditionalSources)' == 'true'"#,
        ],
        gate: Gate::Unreachable("the `AssemblyAttributes` item type, on no list"),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "GenerateTargetFrameworkMonikerAttribute",
        write: r#"Include=$(TargetFrameworkMonikerAssemblyAttributesPath)"#,
        conditions: &[
            r#"'@(Compile)' != '' and '$(GenerateTargetFrameworkAttribute)' == 'true'"#,
            r#"'@(Compile)' != '' and '$(TargetFrameworkMonikerAssemblyAttributeText)' != ''"#,
        ],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.Component.targets",
        target: "RazorGenerateComponentDefinition",
        write: r#"Include=@(_RazorComponentDefinition)"#,
        conditions: &[
            r#"'$(DesignTimeBuild)' != 'true' AND '@(_RazorComponentDefinition->Count())' != '0' AND Exists('@(_RazorComponentDeclarationAssembly)')"#,
            r#"'$(DesignTimeBuild)' != 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.DesignTime.targets",
        target: "_RemoveRazorDeclartionsFromCompile",
        write: r#"Remove=@(_RazorComponentDeclaration)"#,
        conditions: &[r#"'$(DesignTimeBuild)'=='true'"#],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.GenerateAssemblyInfo.targets",
        target: "_CoreGenerateRazorAssemblyInfo",
        write: r#"Include=$(_RazorAssemblyInfo)"#,
        conditions: &[
            r#"'$(GenerateRazorAssemblyInfo)' == 'true' AND '@(_RazorAssemblyAttribute)' != ''"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.GenerateAssemblyInfo.targets",
        target: "_CoreGenerateRazorAssemblyInfo",
        write: r#"Remove=$(_RazorAssemblyInfo)"#,
        conditions: &[
            r#"'$(GenerateRazorAssemblyInfo)' == 'true' AND '@(_RazorAssemblyAttribute)' != ''"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.MvcApplicationPartsDiscovery.targets",
        target: "_DiscoverMvcApplicationParts",
        write: r#"Include=$(_MvcApplicationPartAttributeGeneratedFile)"#,
        conditions: &[
            r#"Exists('$(_MvcApplicationPartAttributeGeneratedFile)')"#,
            r#"'$(Language)'!='F#'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.MvcApplicationPartsDiscovery.targets",
        target: "_DiscoverMvcApplicationParts",
        write: r#"Remove=$(_MvcApplicationPartAttributeGeneratedFile)"#,
        conditions: &[
            r#"Exists('$(_MvcApplicationPartAttributeGeneratedFile)')"#,
            r#"'$(Language)'!='F#'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Sdk.Razor.CurrentVersion.targets",
        target: "_AddEmbeddedValidationAttribute",
        write: r#"Include=$(_EmbeddedAttributeFile)"#,
        conditions: &[
            r#"'$(GenerateEmbeddedValidatableTypeAttribute)' == 'true' AND '$(_TargetingNET100OrLater)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Sdk.Razor.CurrentVersion.targets",
        target: "_AddEmbeddedValidationAttribute",
        write: r#"Include=$(_ValidatableTypeAttributeFile)"#,
        conditions: &[
            r#"'$(GenerateEmbeddedValidatableTypeAttribute)' == 'true' AND '$(_TargetingNET100OrLater)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk.WindowsDesktop/targets/Microsoft.WinFX.targets",
        target: "MarkupCompilePass1",
        write: r#"MarkupCompilePass1(AlwaysCompileMarkupFilesInSeparateDomain=$(AlwaysCompileMarkupFilesInSeparateDomain), ApplicationMarkup=@(ApplicationDefinition), AssembliesGeneratedDuringBuild=@(AssembliesGeneratedDuringBuild), AssemblyName=$(AssemblyName), AssemblyPublicKeyToken=$(AssemblyPublicKeyToken), AssemblyVersion=$(AssemblyVersion), ChecksumAlgorithm=$(ChecksumAlgorithm), ContentFiles=@(Content), ContinueOnError=$(_IntellisenseOnlyCompile), DefineConstants=$(DefineConstants), ExtraBuildControlFiles=@(ExtraBuildControlFiles), HostInBrowser=$(HostInBrowser), IsRunningInVisualStudio=$(BuildingInsideVisualStudio), KnownReferencePaths=$(MSBuildBinPath);$(TargetFrameworkDirectory);@(_TargetFrameworkSDKDirectoryItem);@(KnownReferencePaths), Language=$(Language), LanguageSourceExtension=$(DefaultLanguageSourceExtension), LocalizationDirectivesToLocFile=$(LocalizationDirectivesToLocFile), OutputPath=$(IntermediateOutputPath), OutputType=$(OutputType), PageMarkup=@(Page), References=@(ReferencePath), RootNamespace=$(RootNamespace), SourceCodeFiles=@(Compile), SplashScreen=@(SplashScreen), SupportCustomOutputPaths=$(IncludePackageReferencesDuringMarkupCompilation), UICulture=$(UICulture), XamlDebuggingInformation=$(XamlDebuggingInformation)) Output=GeneratedCodeFiles"#,
        conditions: &[r#"'@(Page)' != '' or '@(ApplicationDefinition)' != '' "#],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.GenerateAssemblyInfo.targets",
        target: "CoreGenerateAssemblyInfo",
        write: r#"Remove=$(GeneratedAssemblyInfoFile)"#,
        conditions: &[r#"'$(Language)'=='VB' or '$(Language)'=='C#'"#],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.GenerateAssemblyInfo.targets",
        target: "CoreGenerateAssemblyInfo",
        write: r#"WriteCodeFragment(AssemblyAttributes=@(AssemblyAttribute), Language=$(Language), OutputFile=$(GeneratedAssemblyInfoFile)) Output=OutputFile"#,
        conditions: &[r#"'$(Language)'=='VB' or '$(Language)'=='C#'"#],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.GenerateGlobalUsings.targets",
        target: "GenerateGlobalUsings",
        write: r#"Include=$(GeneratedGlobalUsingsFile)"#,
        conditions: &[r#"@(Using->Count()) != 0"#],
        gate: Gate::Unreachable("the `Using` item type, on no list"),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Publish.targets",
        target: "DefaultCopyToPublishDirectoryMetadata",
        write: r#"<CopyToPublishDirectory>=Always"#,
        conditions: &[
            r#" '$(DefaultCopyToPublishDirectoryMetadata)' == 'true' "#,
            r#"'%(Compile.CopyToOutputDirectory)'=='Always' and '%(Compile.CopyToPublishDirectory)' == ''"#,
        ],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Publish.targets",
        target: "DefaultCopyToPublishDirectoryMetadata",
        write: r#"<CopyToPublishDirectory>=IfDifferent"#,
        conditions: &[
            r#" '$(DefaultCopyToPublishDirectoryMetadata)' == 'true' "#,
            r#"'%(Compile.CopyToOutputDirectory)'=='IfDifferent' and '%(Compile.CopyToPublishDirectory)' == ''"#,
        ],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Publish.targets",
        target: "DefaultCopyToPublishDirectoryMetadata",
        write: r#"<CopyToPublishDirectory>=PreserveNewest"#,
        conditions: &[
            r#" '$(DefaultCopyToPublishDirectoryMetadata)' == 'true' "#,
            r#"'%(Compile.CopyToOutputDirectory)'=='PreserveNewest' and '%(Compile.CopyToPublishDirectory)' == ''"#,
        ],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Sdk.DefaultItems.Shared.targets",
        target: "CheckForDuplicateItems",
        write: r#"Include=@(DeduplicatedCompileItems)"#,
        conditions: &[r#"'$(DesignTimeBuild)' == 'true' And '@(DeduplicatedCompileItems)' != ''"#],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"Compile"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Sdk.DefaultItems.Shared.targets",
        target: "CheckForDuplicateItems",
        write: r#"Remove=@(Compile)"#,
        conditions: &[r#"'$(DesignTimeBuild)' == 'true' And '@(DeduplicatedCompileItems)' != ''"#],
        gate: Gate::Restates,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"EmbeddedFiles"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"Include=@(Embed) KeepDuplicates=false"#,
        conditions: &[],
        gate: Gate::Unreachable("the `Embed` item type, on no list, which no SDK file adds"),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"EmbeddedFiles"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"Include=@(FsGeneratedSource) KeepDuplicates=false"#,
        conditions: &[
            r#"'$(SourceLink)'!='' or '$(EmbeddedFiles)'!='' or '$(EmbedAllSources)'!=''"#,
        ],
        gate: Gate::EmbeddedResources,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"EmbeddedFiles"#,
        file: "Sdks/Microsoft.Build.Tasks.Git/build/Microsoft.Build.Tasks.Git.targets",
        target: "SetEmbeddedFilesFromSourceControlManagerUntrackedFiles",
        write: r#"Microsoft.Build.Tasks.Git.GetUntrackedFiles(ConfigurationScope=$(GitRepositoryConfigurationScope), Files=@(Compile), ProjectDirectory=$(MSBuildProjectDirectory), RepositoryId=$(_GitRepositoryId)) Output=UntrackedFiles"#,
        conditions: &[r#"'$(_GitRepositoryId)' != ''"#],
        gate: Gate::FromCompile,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"FscCompilerTools"#,
        file: "FSharp/Microsoft.FSharp.NetSdk.targets",
        target: "CollectFSharpDesignTimeTools",
        write: r#"Include=$(%(PropertyNames.Identity))"#,
        conditions: &[],
        gate: Gate::Unreachable(
            "the `IsFSharpDesignTimeProvider` metadata of `PackageReference`, on no list",
        ),
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ReferencePathWithRefAssemblies"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "FindReferenceAssembliesForReferences",
        write: r#"Include=@(ReferencePath)"#,
        conditions: &[r#"'$(CompileUsingReferenceAssemblies)' == 'false'"#],
        gate: Gate::References,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ReferencePathWithRefAssemblies"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "FindReferenceAssembliesForReferences",
        write: r#"Include=@(ReferencePath->'%(ReferenceAssembly)') <OriginalPath>=%(ReferencePath.Identity) if '%(ReferencePath.Identity)' != '@(ReferencePath->'%(ReferenceAssembly)')'"#,
        conditions: &[r#"'$(CompileUsingReferenceAssemblies)' != 'false'"#],
        gate: Gate::References,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ReferencePathWithRefAssemblies"#,
        file: "Roslyn/Microsoft.Managed.Core.targets",
        target: "ShimReferencePathsWhenCommonTargetsDoesNotUnderstandReferenceAssemblies",
        write: r#"Include=@(ReferencePath)"#,
        conditions: &[r#"'@(ReferencePathWithRefAssemblies)' == ''"#],
        gate: Gate::References,
    },
    BuildTimeSite {
        kind: SiteKind::Item,
        name: r#"ReferencePathWithRefAssemblies"#,
        file: "Roslyn/Microsoft.Managed.Core.targets",
        target: "_BeforeVBCSCoreCompile",
        write: r#"<EmbedInteropTypes>="#,
        conditions: &[r#"'$(TargetingClr2Framework)' == 'true'"#],
        gate: Gate::References,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"DefineConstants"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Sdk.BeforeCommon.targets",
        target: "AddImplicitDefineConstants",
        write: r#"$(DefineConstants);@(_ImplicitDefineConstant)"#,
        conditions: &[
            r#" '$(DisableImplicitFrameworkDefines)' != 'true' "#,
            r#" '@(_ImplicitDefineConstant)' != '' "#,
        ],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"DefineConstants"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Sdk.BeforeCommon.targets",
        target: "_DisableDiagnosticTracing",
        write: r#"@(_DefineConstantsWithoutTrace)"#,
        conditions: &[r#"'$(DisableDiagnosticTracing)' == 'true'"#],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"FscOtherFlags"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"$(OtherFlags)"#,
        conditions: &[r#"'$(SimpleResolution)' != 'true'"#],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"FscOtherFlags"#,
        file: "FSharp/Microsoft.FSharp.Targets",
        target: "CoreCompile",
        write: r#"--simpleresolution $(OtherFlags)"#,
        conditions: &[r#"'$(SimpleResolution)' == 'true'"#],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"KeyOriginatorFile"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "ResolveKeySource",
        write: r#"ResolveKeySource(CertificateFile=$(ManifestKeyFile), CertificateThumbprint=$(ManifestCertificateThumbprint), ContinueOnError=!$(BuildingProject), KeyFile=$(AssemblyOriginatorKeyFile), ShowImportDialogDespitePreviousFailures=$(BuildingProject), SuppressAutoClosePasswordPrompt=$(BuildingInsideVisualStudio)) Output=ResolvedKeyFile"#,
        conditions: &[
            r#"$(SignManifests) == 'true' or $(SignAssembly) == 'true'"#,
            r#" '$(SignAssembly)' == 'true' "#,
        ],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Microsoft.CSharp.CurrentVersion.targets",
        target: "XamlPreCompile",
        write: r#"$(NoWarn);1701;1702"#,
        conditions: &[
            r#"'@(Page)' != '' Or '@(ApplicationDefinition)' != ''"#,
            r#"('$(TargetFrameworkVersion)' != 'v1.0') and ('$(TargetFrameworkVersion)' != 'v1.1')"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Microsoft.CSharp.CurrentVersion.targets",
        target: "XamlPreCompile",
        write: r#"$(NoWarn);2008"#,
        conditions: &[
            r#"'@(Page)' != '' Or '@(ApplicationDefinition)' != ''"#,
            r#" '$(BuildingInsideVisualStudio)' == 'true' and '$(VisualStudioVersion)' != '' and '$(VisualStudioVersion)' > '10.0' "#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Roslyn/Microsoft.CSharp.Core.targets",
        target: "CoreCompile",
        write: r#"$(NoWarn);1701;1702"#,
        conditions: &[
            r#"('$(TargetFrameworkVersion)' != 'v1.0') and ('$(TargetFrameworkVersion)' != 'v1.1')"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Roslyn/Microsoft.CSharp.Core.targets",
        target: "CoreCompile",
        write: r#"$(NoWarn);2008"#,
        conditions: &[
            r#"'$(BuildingInsideVisualStudio)' == 'true' AND '$(VisualStudioVersion)' != '' AND '$(VisualStudioVersion)' > '10.0'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Roslyn/Microsoft.CSharp.Core.targets",
        target: "CoreCompile",
        write: r#"$(NoWarn);8002"#,
        conditions: &[r#"'$(TargetFrameworkIdentifier)' == '.NETCoreApp'"#],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Roslyn/Microsoft.VisualBasic.Core.targets",
        target: "CoreCompile",
        write: r#"$(NoWarn);BC41997"#,
        conditions: &[r#"'$(TargetFrameworkIdentifier)' == '.NETCoreApp'"#],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.Compilation.targets",
        target: "RazorCoreCompile",
        write: r#"$(NoWarn);1701;1702"#,
        conditions: &[
            r#"'@(RazorCompile)'!=''"#,
            r#"('$(TargetFrameworkVersion)' != 'v1.0') and ('$(TargetFrameworkVersion)' != 'v1.1')"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.Compilation.targets",
        target: "RazorCoreCompile",
        write: r#"$(NoWarn);2008"#,
        conditions: &[
            r#"'@(RazorCompile)'!=''"#,
            r#"'$(BuildingInsideVisualStudio)' == 'true' AND '$(VisualStudioVersion)' != '' AND '$(VisualStudioVersion)' > '10.0'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.Component.targets",
        target: "RazorCompileComponentDeclaration",
        write: r#"$(NoWarn);1701;1702"#,
        conditions: &[
            r#"'$(DesignTimeBuild)'!='true' AND '$(Language)'=='C#' AND '@(_RazorComponentDeclaration)' != ''"#,
            r#"('$(TargetFrameworkVersion)' != 'v1.0') and ('$(TargetFrameworkVersion)' != 'v1.1')"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"NoWarn"#,
        file: "Sdks/Microsoft.NET.Sdk.Razor/targets/Microsoft.NET.Sdk.Razor.Component.targets",
        target: "RazorCompileComponentDeclaration",
        write: r#"$(NoWarn);2008"#,
        conditions: &[
            r#"'$(DesignTimeBuild)'!='true' AND '$(Language)'=='C#' AND '@(_RazorComponentDeclaration)' != ''"#,
            r#"'$(BuildingInsideVisualStudio)' == 'true' AND '$(VisualStudioVersion)' != '' AND '$(VisualStudioVersion)' > '10.0'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PathMap"#,
        file: "FSharp/Microsoft.FSharp.NetSdk.targets",
        target: "_SetPathMapFromSourceRoots",
        write: r#"@(_TopLevelSourceRoot->'%(EscapedKey)=%(EscapedValue)', ','),$(PathMap)"#,
        conditions: &[
            r#"'$(DeterministicSourcePaths)' == 'true'"#,
            r#"'@(_TopLevelSourceRoot)' != ''"#,
        ],
        gate: Gate::SourceRoots,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PathMap"#,
        file: "Roslyn/Microsoft.Managed.Core.targets",
        target: "_SetPathMapFromSourceRoots",
        write: r#"@(_TopLevelSourceRoot->'%(EscapedKey)=%(EscapedValue)', ','),$(PathMap)"#,
        conditions: &[
            r#"'$(DeterministicSourcePaths)' == 'true'"#,
            r#"'@(_TopLevelSourceRoot)' != ''"#,
        ],
        gate: Gate::SourceRoots,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PdbFile"#,
        file: "Microsoft.CSharp.CurrentVersion.targets",
        target: "XamlPreCompile",
        write: r#"$(IntermediateOutputPath)$(TargetName).compile.pdb"#,
        conditions: &[
            r#"'@(Page)' != '' Or '@(ApplicationDefinition)' != ''"#,
            r#"'$(PdbFile)' == '' and '$(OutputType)' == 'winmdobj' and '$(_DebugSymbolsProduced)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PdbFile"#,
        file: "Microsoft.VisualBasic.CurrentVersion.targets",
        target: "XamlPreCompile",
        write: r#"$(IntermediateOutputPath)$(TargetName).compile.pdb"#,
        conditions: &[
            r#"'@(Page)' != '' Or '@(ApplicationDefinition)' != ''"#,
            r#"'$(PdbFile)' == '' and '$(OutputType)' == 'winmdobj' and '$(DebugSymbols)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PdbFile"#,
        file: "Roslyn/Microsoft.CSharp.Core.targets",
        target: "CoreCompile",
        write: r#"$(IntermediateOutputPath)$(TargetName).compile.pdb"#,
        conditions: &[
            r#"'$(PdbFile)' == '' AND '$(OutputType)' == 'winmdobj' AND '$(_DebugSymbolsProduced)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PdbFile"#,
        file: "Roslyn/Microsoft.VisualBasic.Core.targets",
        target: "CoreCompile",
        write: r#"$(IntermediateOutputPath)$(TargetName).compile.pdb"#,
        conditions: &[
            r#"'$(PdbFile)' == '' AND '$(OutputType)' == 'winmdobj' AND '$(DebugSymbols)' == 'true'"#,
        ],
        gate: Gate::NotImported,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"PlatformTarget"#,
        file: "Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.RuntimeIdentifierInference.targets",
        target: "AdjustDefaultPlatformTargetForNetFrameworkExeWithNoNativeCopyLocalItems",
        write: r#"GetDefaultPlatformTargetForNetFramework(NativeCopyLocalItems=@(NativeCopyLocalItems), PackageDependencies=@(PackageDependencies)) Output=DefaultPlatformTarget"#,
        conditions: &[r#"'$(_UsingDefaultPlatformTarget)' == 'true' and
                     '$(_UsingDefaultRuntimeIdentifier)' == 'true'"#],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"SourceLink"#,
        file: "Sdks/Microsoft.SourceLink.Common/build/Microsoft.SourceLink.Common.targets",
        target: "_GenerateSourceLinkFile",
        write: r#"Microsoft.SourceLink.Common.GenerateSourceLinkFile(NoWarnOnMissingSourceControlInformation=$(PkgMicrosoft_SourceLink_Common.Equals('')), OutputFile=$(_SourceLinkFilePath), SourceRoots=@(SourceRoot)) Output=SourceLink"#,
        conditions: &[r#"'$(EnableSourceLink)' == 'true' and '$(DebugType)' != 'none'"#],
        gate: Gate::Generated,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"WarningsNotAsErrors"#,
        file: "Sdks/Microsoft.NET.Sdk/analyzers/build/Microsoft.CodeAnalysis.NetAnalyzers.targets",
        target: "_CodeAnalysisTreatWarningsAsErrors",
        write: r#"$(WarningsNotAsErrors);$(CodeAnalysisRuleIds)"#,
        conditions: &[
            r#"'$(DesignTimeBuild)' == 'true' OR '$(BuildingProject)' != 'true'"#,
            r#"'$(EffectiveCodeAnalysisTreatWarningsAsErrors)' == 'false' and '$(TreatWarningsAsErrors)' == 'true'"#,
        ],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"Win32Manifest"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "_SetEmbeddedWin32ManifestProperties",
        write: r#"$(ApplicationManifest)"#,
        conditions: &[
            r#"'$(GenerateClickOnceManifests)'!='true' and '@(NativeReference)'=='' and '@(ResolvedIsolatedComModules)'==''"#,
        ],
        gate: Gate::Properties,
    },
    BuildTimeSite {
        kind: SiteKind::Property,
        name: r#"Win32Manifest"#,
        file: "Microsoft.Common.CurrentVersion.targets",
        target: "_SetPreferNativeArm64Win32ManifestProperties",
        write: r#"$(_Win32Manifest)"#,
        conditions: &[
            r#" '$(PreferNativeArm64)'=='true' and '$(NoWin32Manifest)'!='true'"#,
            r#"'$(_Win32Manifest)' != ''"#,
        ],
        gate: Gate::Properties,
    },
];

/// The lines of the verified list, comments and blanks left out.
fn verified_lines() -> impl Iterator<Item = &'static str> {
    include_str!("fsc_verified_sdks.txt")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
}

/// The SDKs (version directories, `10.0.401`) the derivation has been graded
/// against: a grading run of `tests/fsproj_assembly_name_perturbation_diff.rs`
/// writes the list, and a test there fails, printing how to regenerate it,
/// when the devshell's SDK is not on it. The SDK's files are part of what
/// the derivation's domain trusts, so an SDK nobody graded declines.
pub fn verified_sdks() -> impl Iterator<Item = &'static str> {
    verified_lines().filter(|line| !line.contains(' '))
}

/// The workload manifest files the grading run of the SDK `sdk` loaded, each
/// by its path under the install's `sdk-manifests`
/// (`10.0.100/microsoft.net.workload.mono.toolchain.current/10.0.112/WorkloadManifest.targets`:
/// feature band, manifest and its version). A manifest is installed apart
/// from the SDK, by a workload update, into a directory of its own version,
/// so the same SDK can load another; the derivation commits only for the
/// manifests its SDK was graded with ([`crate::ParsedProject::workload_manifest_files`]).
pub fn verified_manifests(sdk: &str) -> impl Iterator<Item = &'static str> + '_ {
    verified_lines().filter_map(move |line| {
        let mut words = line.splitn(3, ' ');
        (words.next() == Some(sdk) && words.next() == Some("manifest"))
            .then(|| words.next())
            .flatten()
    })
}

/// The version directory of the SDK `parsed` resolved, when it is the
/// canonical .NET layout (`<dotnet>/sdk/<version>/Sdks/Microsoft.NET.Sdk/Sdk`);
/// another layout (a NuGet SDK, a custom resolver's) has no verified version.
pub fn resolved_sdk_version(parsed: &ParsedProject) -> Option<String> {
    let root = parsed.resolved_sdk_root.as_deref()?;
    let version_dir = crate::evaluator::dotnet_sdk_version_dir(root)?;
    Some(version_dir.file_name()?.to_str()?.to_string())
}

/// [`CompiledAssemblyName`] of the project at `project_path`, from one
/// evaluation of it (`parsed`) and the [`NameInputs`] beside it.
pub fn compiled_assembly_name(
    project_path: &Path,
    parsed: &ParsedProject,
    inputs: &NameInputs<'_>,
) -> CompiledAssemblyName {
    let graded = |version: &str| verified_sdks().any(|sdk| sdk == version);
    let manifest_graded =
        |version: &str, manifest: &str| verified_manifests(version).any(|m| m == manifest);
    compiled_assembly_name_graded(project_path, parsed, inputs, &graded, &manifest_graded)
}

/// [`compiled_assembly_name`], with `graded` saying which SDKs count as
/// graded: the grading run itself names the SDK it grades.
pub(crate) fn compiled_assembly_name_graded(
    project_path: &Path,
    parsed: &ParsedProject,
    inputs: &NameInputs<'_>,
    graded: &dyn Fn(&str) -> bool,
    manifest_graded: &dyn Fn(&str, &str) -> bool,
) -> CompiledAssemblyName {
    let version = match resolved_sdk_version(parsed) {
        Some(version) if graded(&version) => version,
        Some(version) => return CompiledAssemblyName::Unknown(NameDecline::UngradedSdk(version)),
        None => {
            return CompiledAssemblyName::Unknown(NameDecline::HiddenContent(
                "no SDK resolved".to_string(),
            ));
        }
    };
    if let Some(manifest) = parsed
        .workload_manifest_files
        .iter()
        .find(|manifest| !manifest_graded(&version, manifest))
    {
        return CompiledAssemblyName::Unknown(NameDecline::WorkloadManifest(manifest.clone()));
    }
    match decide(project_path, parsed, inputs) {
        Ok(name) => CompiledAssemblyName::Known(name),
        Err(decline) => CompiledAssemblyName::Unknown(decline),
    }
}

fn allowed_property(name: &str) -> Option<Grammar> {
    ALLOWED_PROPERTIES
        .iter()
        .find(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
        .map(|(_, grammar)| *grammar)
}

/// The grammar a value of property `name` must match to stay in the domain, if
/// the name is one the domain admits ([`ALLOWED_PROPERTIES`],
/// [`RESTORE_PROPERTIES`], [`RESTORE_PROPERTY_PREFIX`]). The evaluator checks
/// each write outside the install against it as the write is made
/// ([`crate::ParsedProject::foreign_write_failures`]).
pub(crate) fn grammar_of(name: &str) -> Option<Grammar> {
    allowed_property(name).or_else(|| restore_property(name))
}

fn restore_property(name: &str) -> Option<Grammar> {
    let prefixed = name.len() > RESTORE_PROPERTY_PREFIX.len()
        && name
            .get(..RESTORE_PROPERTY_PREFIX.len())
            .is_some_and(|head| head.eq_ignore_ascii_case(RESTORE_PROPERTY_PREFIX));
    RESTORE_PROPERTIES
        .iter()
        .find(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
        .map(|(_, grammar)| *grammar)
        .or(prefixed.then_some(Grammar::Path))
}

/// `path` with its `.` and `..` folded away lexically.
fn lexical(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

/// Whether `files`, the documents defining a name, are NuGet's restore file
/// alone.
fn only_restore_defines(files: &BTreeSet<PathBuf>, restore: Option<&Path>) -> bool {
    let Some(restore) = restore else {
        return false;
    };
    files.len() == 1 && files.iter().all(|file| lexical(file) == lexical(restore))
}

fn on_list(list: &[&str], name: &str) -> bool {
    list.iter()
        .any(|allowed| allowed.eq_ignore_ascii_case(name))
}

fn decide(
    project_path: &Path,
    parsed: &ParsedProject,
    inputs: &NameInputs<'_>,
) -> Result<String, NameDecline> {
    let NameInputs {
        environment,
        globals,
        files,
        references,
        content,
    } = *inputs;
    if let Some(cause) = &parsed.hidden_content {
        return Err(NameDecline::HiddenContent(format!("{cause:?}")));
    }
    if !parsed.sdk_files_imported_from_outside.is_empty() {
        return Err(NameDecline::HiddenContent(format!(
            "SDK files imported from outside the SDK: {:?}",
            parsed.sdk_files_imported_from_outside
        )));
    }
    if parsed.resolved_sdk_root.is_none() {
        return Err(NameDecline::HiddenContent("no SDK resolved".to_string()));
    }
    if parsed.is_outer_build() != Some(false) {
        return Err(NameDecline::OuterBuild);
    }
    if parsed.auto_response_file != AutoResponseFile::Absent {
        return Err(NameDecline::ResponseFile);
    }
    if !matches!(parsed.property("RestoreSuccess"), PropertyRead::Value(v) if v.eq_ignore_ascii_case("true"))
    {
        return Err(NameDecline::Unrestored);
    }

    if project_path.to_string_lossy().chars().any(char::is_control) {
        return Err(NameDecline::ProjectPath);
    }
    // The entry SDK's files the evaluation imported: none may be one whose
    // build-time writes the register holds unreached.
    if let Some(site) = BUILD_TIME_SITES.iter().find(|site| {
        site.gate == Gate::NotImported && parsed.imported_sdk_files.contains(Path::new(site.file))
    }) {
        return Err(NameDecline::NotImported(site.file.to_string()));
    }
    if let Some(manifest) = parsed.workload_manifests_outside_install.iter().next() {
        return Err(NameDecline::WorkloadManifest(
            manifest.display().to_string(),
        ));
    }
    // The packages' content files reach fsc only through their build action.
    let content = match content {
        ContentFiles::Listed(content) => content,
        ContentFiles::Unread => return Err(NameDecline::ContentFile("not read".to_string())),
    };
    if let Some((path, action)) = content
        .iter()
        .find(|(_, action)| !on_list(ADMITTED_CONTENT_ACTIONS, action))
    {
        return Err(NameDecline::ContentFile(format!("{path} ({action})")));
    }

    // The domain: every name set from outside the .NET install is listed.
    let foreign = &parsed.foreign_definitions;
    if foreign.defines_build_code() || !foreign.build_time_properties.is_empty() {
        return Err(NameDecline::BuildCode);
    }
    let restore = restore_props(project_path);
    let restore_targets = restore
        .as_deref()
        .map(|props| props.with_extension("targets"));
    // NuGet's restore files are exempt only where every condition and
    // expansion in them is one NuGet writes: the path names no author.
    let not_restore_file = |file: &&PathBuf| {
        foreign.unlike_nuget.contains(*file)
            || [restore.as_deref(), restore_targets.as_deref()]
                .into_iter()
                .flatten()
                .all(|restore_file| lexical(file) != lexical(restore_file))
    };
    if let Some(file) = foreign.conditioned.iter().find(not_restore_file) {
        return Err(NameDecline::Conditional(file.display().to_string()));
    }
    if let Some(file) = foreign.expanding.iter().find(not_restore_file) {
        return Err(NameDecline::Expansion(file.display().to_string()));
    }
    if let Some(file) = foreign.globbing.iter().next() {
        return Err(NameDecline::Glob(file.display().to_string()));
    }
    // The tables hold names lowercased, as written; a computed or escaped
    // name is on no list.
    if let Some(name) = foreign.properties.iter().find_map(|(name, files)| {
        let restore_written =
            restore_property(name).is_some() && only_restore_defines(files, restore.as_deref());
        (allowed_property(name).is_none() && !restore_written).then_some(name)
    }) {
        return Err(NameDecline::Property(name.clone()));
    }
    if let Some(name) = globals.keys().find(|name| allowed_property(name).is_none()) {
        return Err(NameDecline::Property(name.clone()));
    }
    if let Some(name) = foreign
        .items
        .iter()
        .chain(&foreign.item_definitions)
        .find_map(|(name, files)| {
            let restore_written = on_list(RESTORE_ITEM_TYPES, name)
                && only_restore_defines(files, restore.as_deref());
            (!on_list(ALLOWED_ITEM_TYPES, name) && !restore_written).then_some(name)
        })
    {
        return Err(NameDecline::ItemType(name.clone()));
    }
    if let Some(name) = foreign.item_metadata.iter().find_map(|(name, files)| {
        let restore_written =
            on_list(RESTORE_METADATA, name) && only_restore_defines(files, restore.as_deref());
        (!on_list(ALLOWED_METADATA, name) && !restore_written).then_some(name)
    }) {
        return Err(NameDecline::Metadata(name.clone()));
    }
    if let Some(decline) = environment_decline(environment) {
        return Err(decline);
    }

    // Every value an allowed property held is in its grammar: its final value,
    // each write a document outside the install made (the SDK may have copied
    // any of them before the next), and its global or variable. A property
    // only the SDK writes is the SDK's to vouch for.
    let admit = |name: &str, grammar: Grammar, value: Option<&str>| match value {
        Some(value) if grammar.admits(value) => Ok(()),
        _ => Err(NameDecline::Value(name.to_string(), format!("{value:?}"))),
    };
    // The evaluation checked each write as it was made (the first one out of
    // its grammar, or one it was not certain of, is kept).
    if let Some((name, value)) = parsed.foreign_write_failures.iter().next() {
        return Err(NameDecline::Value(name.clone(), format!("{value:?}")));
    }
    for name in foreign.properties.keys() {
        if let Some(grammar) = grammar_of(name) {
            match parsed.property(name) {
                PropertyRead::Unset => {}
                PropertyRead::Value(value) => admit(name, grammar, Some(&value))?,
                read => return Err(NameDecline::Value(name.clone(), format!("{read:?}"))),
            }
        }
    }
    for (name, value) in globals.iter().chain(environment) {
        if let Some(grammar) = allowed_property(name) {
            admit(name, grammar, Some(value))?;
            match parsed.property(name) {
                PropertyRead::Unset => {}
                PropertyRead::Value(value) => admit(name, grammar, Some(&value))?,
                read => return Err(NameDecline::Value(name.clone(), format!("{read:?}"))),
            }
        }
    }

    // Every reference fsc is handed is a path it reads as one: absolute (a
    // targeting pack's inside the install, a package's in the package
    // folder), with no line break to start an argument of its own and no
    // start fsc reads as an option.
    let references = match references {
        ReferencePaths::Listed(references) => references,
        ReferencePaths::Unread => {
            return Err(NameDecline::ReferencePath("not read".to_string()));
        }
    };
    if let Some(path) = references.iter().find(|path| {
        let text = path.to_string_lossy();
        !path.is_absolute() || text.chars().any(char::is_control) || may_read_as_option(&text)
    }) {
        return Err(NameDecline::ReferencePath(format!("{}", path.display())));
    }

    // Every file the SDK's default item globs can match has a name the
    // path grammar admits: their items reach fsc (`--resource:`). A `%` is
    // an escape MSBuild decodes after the scan (`%0A` a line break), so the
    // name is checked as written and must hold none.
    let listed = match files {
        DefaultItemFiles::Listed(listed) => listed,
        DefaultItemFiles::Unread => {
            return Err(NameDecline::FileName("not listed".to_string()));
        }
        DefaultItemFiles::Declined(why) => return Err(NameDecline::FileName(why.clone())),
    };
    let project_dir = lexical(project_path);
    let dir = project_dir.parent().unwrap_or(Path::new(""));
    if let Some(file) = listed.iter().find(|file| {
        let relative = file.strip_prefix(dir).unwrap_or(file);
        relative
            .to_string_lossy()
            .chars()
            .any(|c| c.is_control() || c == '%')
    }) {
        return Err(NameDecline::FileName(format!("{}", file.display())));
    }

    // The SDK's own `-o:`: `TargetName` is `AssemblyName`, which the grammar
    // keeps a plain file name, and `TargetExt` follows `OutputType`.
    let name = match parsed.property("TargetName") {
        PropertyRead::Value(name) if Grammar::FileName.admits(&name) => name,
        _ => return Err(NameDecline::Name),
    };
    if !matches!(parsed.property("TargetExt"), PropertyRead::Value(ext) if ext == ".dll" || ext == ".exe")
    {
        return Err(NameDecline::Name);
    }
    if !sources_read_as_files(project_path, parsed) {
        return Err(NameDecline::Sources);
    }
    Ok(name)
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
        // fsc takes a positional `.dll` for an assembly (FS2020) and stops at
        // a positional `.resx` (FS2023).
        let lower = text.trim().trim_matches('"').to_ascii_lowercase();
        if lower.ends_with(".dll") || lower.ends_with(".resx") {
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

#[cfg(test)]
mod tests {
    use super::{
        ALLOWED_ENVIRONMENT, ALLOWED_PROPERTIES, DefaultItemFiles, Grammar, NameDecline,
        VariableClass, classify_variable, default_item_files, environment_decline,
        may_read_as_option,
    };
    use crate::observed::Observer;
    use proptest::prelude::*;
    use std::collections::HashMap;

    /// The environment rule as it stood before it was a classifier, kept
    /// verbatim as the reference the classifier must equal.
    fn declined_before(name: &str) -> bool {
        let toolchain = matches!(
            name,
            "PATH" | "HOME" | "TMPDIR" | "RestoreSources" | "MSBuildUserExtensionsPath"
        ) || name.starts_with("DOTNET_")
            || name.starts_with("NUGET_");
        let graded = ALLOWED_ENVIRONMENT
            .iter()
            .any(|allowed| allowed.eq_ignore_ascii_case(name));
        let property = ALLOWED_PROPERTIES
            .iter()
            .any(|(allowed, _)| allowed.eq_ignore_ascii_case(name));
        !toolchain && !graded && !property
    }

    /// A name for a variable: each listed name and the toolchain's, in its
    /// own case, lower case or upper case, with or without a tail; a
    /// `DOTNET_`/`NUGET_` name in either case; or any short name.
    fn variable_name() -> impl Strategy<Value = String> {
        let listed: Vec<&'static str> = ALLOWED_ENVIRONMENT
            .iter()
            .copied()
            .chain(ALLOWED_PROPERTIES.iter().map(|(name, _)| *name))
            .chain([
                "PATH",
                "HOME",
                "TMPDIR",
                "RestoreSources",
                "MSBuildUserExtensionsPath",
                "DOTNET_",
                "NUGET_",
                "DOTNET_ROOT",
                "NUGET_PACKAGES",
            ])
            .collect();
        prop_oneof![
            (prop::sample::select(listed), 0..3usize, "[A-Za-z_]{0,2}").prop_map(
                |(name, case, tail)| {
                    let name = match case {
                        0 => name.to_string(),
                        1 => name.to_ascii_lowercase(),
                        _ => name.to_ascii_uppercase(),
                    };
                    format!("{name}{tail}")
                }
            ),
            "[A-Za-z_][A-Za-z0-9_.()-]{0,12}",
        ]
    }

    proptest! {
        /// The classifier admits exactly what the rule did before it.
        #[test]
        fn the_classifier_is_the_rule_it_replaced(name in variable_name()) {
            prop_assert_eq!(!classify_variable(&name).admitted(), declined_before(&name));
        }

        /// An environment declines exactly when it holds a variable the rule
        /// declined, and names such a variable.
        #[test]
        fn the_environment_declines_as_it_did(
            names in prop::collection::vec(variable_name(), 0..6)
        ) {
            let environment: HashMap<String, String> =
                names.into_iter().map(|name| (name, "v".to_string())).collect();
            match environment_decline(&environment) {
                Some(NameDecline::Environment(name)) => {
                    prop_assert!(environment.contains_key(&name), "{name} is not set");
                    prop_assert!(declined_before(&name));
                }
                Some(other) => prop_assert!(false, "{other:?}"),
                None => prop_assert!(!environment.keys().any(|name| declined_before(name))),
            }
        }
    }

    /// Each class is reached, so the property above compares every arm.
    #[test]
    fn every_class_is_reached() {
        assert_eq!(classify_variable("PATH"), VariableClass::Toolchain);
        assert_eq!(classify_variable("DOTNET_ROOT"), VariableClass::Toolchain);
        assert_eq!(
            classify_variable("assemblyname"),
            VariableClass::AllowedProperty(Grammar::FileName)
        );
        assert_eq!(classify_variable("lang"), VariableClass::Graded);
        assert_eq!(classify_variable("BORZOI_X"), VariableClass::Unlisted);
        assert_eq!(classify_variable("path"), VariableClass::Unlisted);
    }
    use std::fs::{create_dir_all, write};
    use std::path::Path;

    /// The listing reads the directory MSBuild enumerates: the project's path
    /// with `..` folded, not the target of a link before it.
    #[cfg(unix)]
    #[test]
    fn default_items_are_listed_from_the_folded_directory() {
        let tmp = tempfile::TempDir::new().unwrap();
        let work = tmp.path().join("work");
        let elsewhere = tmp.path().join("elsewhere");
        create_dir_all(elsewhere.join("inner")).unwrap();
        create_dir_all(elsewhere.join("work")).unwrap();
        create_dir_all(&work).unwrap();
        write(work.join("bad%0Aname.resx"), "").unwrap();
        std::os::unix::fs::symlink(elsewhere.join("inner"), tmp.path().join("link")).unwrap();
        // MSBuild's project directory is `<tmp>/work`; `link/../work` read
        // through the link is `elsewhere/work`.
        let project = tmp
            .path()
            .join("link")
            .join("..")
            .join("work")
            .join("Demo.fsproj");
        let DefaultItemFiles::Listed(files) = default_item_files(&project, &Observer::new()) else {
            panic!("listed");
        };
        assert!(
            files.iter().any(|f| f.ends_with("bad%0Aname.resx")),
            "{files:?}"
        );
    }

    /// A project path without a root is never listed: it would be read
    /// against this process's working directory.
    #[test]
    fn an_unrooted_project_is_not_listed() {
        assert_eq!(
            default_item_files(Path::new("../app/Demo.fsproj"), &Observer::new()),
            DefaultItemFiles::Unread
        );
    }

    #[test]
    fn fsc_options_admit_no_output_switch() {
        for flags in [
            "",
            "--warnon:3390",
            "--nowarn:44 --define:OUTER",
            "--optimize+ -g",
            "--warnaserror-",
        ] {
            assert!(Grammar::FscOptions.admits(flags), "{flags:?}");
        }
        for flags in [
            "-o:Friend.dll",
            "--out:Friend.dll",
            "-o",
            "/out:Friend.dll",
            "@extra.rsp",
            "\"--out:a.dll\"",
            "--warnon:1\n--out:Friend.dll",
            "--warnon:1\t--nowarn:2",
            "--OUT:Friend.dll",
            "#--out:Friend.dll",
            "--doc:a b.xml",
            "x",
            "-warnon:1182",
            "--warnon",
            "--nologo",
            "--define:A.B",
            "-g:x",
            "-g+",
            "-O-",
        ] {
            assert!(!Grammar::FscOptions.admits(flags), "{flags:?}");
        }
    }

    #[test]
    fn file_names_are_plain() {
        for name in ["Demo", "My.Lib", "a-b_c", "_x", "9z"] {
            assert!(Grammar::FileName.admits(name), "{name:?}");
        }
        for name in [
            "", "-o:x", ".x", "x.", "a b", "a/b", "a\nb", "%41", "$(X)", "a;b",
        ] {
            assert!(!Grammar::FileName.admits(name), "{name:?}");
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
