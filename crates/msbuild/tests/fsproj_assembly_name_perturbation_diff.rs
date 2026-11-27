//! The grader of [`borzoi_msbuild::fsc::compiled_assembly_name`]'s domain:
//! **certainty implies exactness** under perturbation of every allowed name.
//!
//! The derivation commits to a name only when every name a project sets from
//! outside the .NET install is on one of its lists. This sets each listed
//! name, at each place it can be set from, to values shaped to move fsc's
//! output (an output switch in each spelling fsc reads, behind a line break
//! of each kind, padded, as a response file) and to one plain value, and
//! holds every case to the real build
//! ([`borzoi_oracle_harness::msbuild_oracle::fsc_args`]):
//!
//! - we commit a name ⟹ the oracle answers with fsc's `-o:` naming exactly
//!   that assembly, or cannot answer (no fsc run it can vouch for, counted);
//! - we decline ⟹ no claim, counted by reason.
//!
//! The plain SDK project, and each listed property set to a value in its
//! grammar, must commit and be answered: the gate cannot pass by declining
//! everything.
//!
//! The default run grades the must-commit points and a seeded sample of the
//! rest (`BORZOI_FSC_NAME_SEED`, `BORZOI_FSC_NAME_CASES`); the ignored
//! `deep_every_perturbation` grades every case. `BORZOI_FSC_NAME_ONLY` keeps
//! the cases of one name, `BORZOI_FSC_NAME_THREADS` sets how many are
//! graded at once, and `BORZOI_FSC_NAME_VERBOSE` prints every decline.

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use borzoi_msbuild::fsc::{
    ALLOWED_ENVIRONMENT, ALLOWED_ITEM_TYPES, ALLOWED_METADATA, ALLOWED_PROPERTIES,
    CompiledAssemblyName, FSC_OPTIONS, Grammar, NameDecline, RESTORE_ITEM_TYPES, RESTORE_METADATA,
    RESTORE_PROPERTIES, RESTORE_PROPERTY_PREFIX, ToolchainValue, resolved_sdk_version,
    toolchain_variable, verified_manifests, verified_sdks,
};
use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::unescape;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::hostile::value::{self, Write};
use borzoi_oracle_harness::hostile::{Dimension, coverage};
use borzoi_oracle_harness::hostile::{env as hostile_env, name as hostile_name};
use borzoi_oracle_harness::msbuild_oracle::{
    BUILD_ENVIRONMENT_NAMES, BuildEnvironment, BuildInputs, FscArgsDecline, FscArgsRequest,
    INPUT_NAMES, InputError, fsc_args, msbuild_command, msbuild_user_extensions_path,
};
use common::SplitMix64;
use common::assembly_name::{self, Sdks};

/// The values each name is set to: shaped to move fsc's output by each route
/// fsc reads one, and one plain value ([`plain_value`] adds the property's own).
const VALUES: &[&str] = &[
    "Evil",
    "--out:obj/Evil.dll",
    "-o:Evil.dll",
    "/o:obj/Evil.dll",
    "@evil.rsp",
    " --out:obj/Evil.dll",
    "x --out:obj/Evil.dll",
    "x\n--out:obj/Evil.dll",
    "x\r-o:Evil.dll",
    "x\r\n/out:obj/Evil.dll",
    "x%0A--out%3Aobj/Evil.dll",
    "Evil$(_MSBUILDTLENABLED)",
];

/// The condition [`Place::ConditionalBody`] and [`Place::ConditionalItem`]
/// write under: one MSBuild decides by its working directory, which holds the
/// restored project's `obj/` when it builds (#993).
const PATH_CONDITION: &str = "'$(BaseIntermediateOutputPath)'=='obj/'";

/// A value of property `name` in `grammar`, which the derivation must commit
/// under and the build must compile with.
fn plain_value(name: &str, grammar: Grammar) -> &'static str {
    if name == "LangVersion" {
        return "latest";
    }
    match grammar {
        Grammar::Bool => "true",
        Grammar::OneOf(values) => values[0],
        Grammar::Framework | Grammar::Frameworks => "net10.0",
        Grammar::FileName => "Friend",
        Grammar::DottedIdentifier => "Debug",
        Grammar::Codes => "FS0040",
        Grammar::Version => "1.2.3",
        Grammar::Text => "Some text",
        Grammar::FscOptions => "--warnon:1182",
        Grammar::Path | Grammar::Paths => "/nonexistent/borzoi",
    }
}

/// The property NuGet's restore writes for FSharp.Core's folder, which
/// stands for every name with [`RESTORE_PROPERTY_PREFIX`].
const PACKAGE_FOLDER: &str = "PkgFSharp_Core";

/// Where a name is set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Place {
    /// A property in the project file's body.
    Body,
    /// A property in `Directory.Build.props`.
    DirectoryBuildProps,
    /// A property in `Directory.Build.targets`, written after the SDK's
    /// properties.
    DirectoryBuildTargets,
    /// A global property.
    Global,
    /// An environment variable.
    Environment,
    /// An item of the type, the value its `Include`.
    Item,
    /// Item metadata on an item it applies to.
    Metadata,
    /// A `.resx` file, the value its name: the SDK's default
    /// `EmbeddedResource` glob takes it.
    ResxName,
    /// The value written in the body, then the plain one in
    /// `Directory.Build.targets`.
    BodyThenTargets,
    /// The value written in `Directory.Build.props`, then the plain one in
    /// the body.
    PropsThenBody,
    /// The value written in `Directory.Build.props`, then the plain one in
    /// `Directory.Build.targets`.
    PropsThenTargets,
    /// A package the project references, its compile asset's file name the
    /// value: fsc is handed it as a `-r:` path.
    PackageDll,
    /// A package the project references, shipping one content file whose
    /// build action is the value.
    PackageContent,
    /// A Compile file, the value its name under [`UNTRACKED`], which the git
    /// repository holding the rest of the project ignores: SourceLink's
    /// `EmbedUntrackedSources` hands it to fsc again, as `--embed:`.
    UntrackedCompile,
    /// A property in the project file's body, under [`PATH_CONDITION`].
    ConditionalBody,
    /// A Compile item, the value its `Include`, under [`PATH_CONDITION`].
    ConditionalItem,
    /// An item definition of the type, in an `<ItemDefinitionGroup>`, setting
    /// `Link` to the value.
    ItemDefinition,
    /// Item metadata as an attribute of an item of the given admitted type.
    MetadataOn(&'static str),
    /// Item metadata as a child element of an item it applies to.
    MetadataChild,
    /// Item metadata in an item definition of the type of an item it applies
    /// to, which the item inherits.
    MetadataDefinition,
    /// A property in the project file's body, a comment between each two
    /// characters of its value (MSBuild reads the text around them as one).
    BodySplit,
    /// [`Place::BodySplit`], two comments and a space between them between
    /// each two characters: MSBuild drops the whitespace-only text node
    /// before it joins the text around it.
    BodySpaced,
    /// A property NuGet's restore file (`obj/*.nuget.g.props`) is made to
    /// write after the restore, in a group of its own: a build that finds
    /// the restore current leaves the file as it is.
    RestoreProps,
    /// An item of the type, the value its `Include`, that NuGet's restore
    /// file is made to declare after the restore.
    RestoreItem,
    /// Item metadata on a `None` item that NuGet's restore file is made to
    /// declare after the restore.
    RestoreMetadata,
    /// The environment variables [`Case::variables`], each set as the build's
    /// (through [`BuildInputs::env`]) and handed to the evaluation. One the
    /// oracle does not take (a name off its list, or a second spelling of a
    /// name already set) is handed to the evaluation alone
    /// ([`split_variables`]), so it never reaches a real restore or build,
    /// and a commit under it is a failure unless it is the toolchain's,
    /// which the grading holds fixed. A commit under variables none of which
    /// is an allowed property ([`held_to_plain_arguments`]) must be answered
    /// and hand fsc the plain project's arguments. The source holds a
    /// warning ([`WARNING_SOURCE`]), so fsc speaks whatever language it
    /// prints its banner in (#1129).
    Variables,
}

/// The directory, ignored by git, holding [`Place::UntrackedCompile`]'s file.
const UNTRACKED: &str = "untracked";

/// The package [`Place::PackageDll`] and [`Place::PackageContent`] make.
const PACKAGE: &str = "BorzoiPerturbed";

/// The content types part of a `.nupkg`.
const CONTENT_TYPES: &str = "<?xml version=\"1.0\" encoding=\"utf-8\"?><Types \
     xmlns=\"http://schemas.openxmlformats.org/package/2006/content-types\">\
     <Default Extension=\"nuspec\" ContentType=\"application/octet\"/>\
     <Default Extension=\"dll\" ContentType=\"application/octet\"/>\
     <Default Extension=\"fs\" ContentType=\"application/octet\"/></Types>";

/// A resource file the SDK compiles, as `resgen` reads one.
const RESX: &str = "<?xml version=\"1.0\" encoding=\"utf-8\"?><root>\
<resheader name=\"resmimetype\"><value>text/microsoft-resx</value></resheader>\
<resheader name=\"version\"><value>2.0</value></resheader>\
<resheader name=\"reader\"><value>System.Resources.ResXResourceReader, System.Windows.Forms, \
Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089</value></resheader>\
<resheader name=\"writer\"><value>System.Resources.ResXResourceWriter, System.Windows.Forms, \
Version=4.0.0.0, Culture=neutral, PublicKeyToken=b77a5c561934e089</value></resheader>\
<data name=\"Greeting\" xml:space=\"preserve\"><value>hi</value></data></root>";

#[derive(Debug, Clone)]
struct Case {
    place: Place,
    name: &'static str,
    value: String,
    /// The value a later write puts back, for the places that reset one.
    reset: &'static str,
    /// The name we must commit to, and the oracle with us.
    must_commit: Option<String>,
    /// The derivation must decline, whatever the build does.
    must_decline: bool,
    /// The variable whose value the decline must name ([`declines_for`]), for
    /// a case whose subject is that variable: so a decline the fixture
    /// itself causes (an unrestored project) grades nothing.
    decline_for: Option<String>,
    /// For [`Place::Variables`], the variables, by name and value.
    variables: Vec<(String, String)>,
}

impl Default for Case {
    fn default() -> Case {
        Case {
            place: Place::Body,
            name: "",
            value: String::new(),
            reset: "",
            must_commit: None,
            must_decline: false,
            decline_for: None,
            variables: Vec::new(),
        }
    }
}

/// Whether `why` is a decline the variable `name` causes: off every list,
/// a toolchain value off its shape, or an allowed property's value outside
/// its grammar.
fn declines_for(why: &borzoi_msbuild::fsc::NameDecline, name: &str) -> bool {
    use borzoi_msbuild::fsc::NameDecline;
    match why {
        NameDecline::Environment(n) | NameDecline::ToolchainValue(n, _) => n == name,
        NameDecline::Value(n, _) => n.eq_ignore_ascii_case(name),
        _ => false,
    }
}

impl Case {
    fn label(&self) -> String {
        if self.place == Place::Variables {
            return format!("{:?} {:?}", self.place, self.variables);
        }
        format!("{:?} {} = {:?}", self.place, self.name, self.value)
    }

    /// A [`Place::Variables`] case setting `variables`.
    fn variables(variables: &[(&str, &str)]) -> Case {
        Case {
            place: Place::Variables,
            name: "environment",
            variables: variables
                .iter()
                .map(|(n, v)| (n.to_string(), v.to_string()))
                .collect(),
            ..Case::default()
        }
    }
}

/// The value the environment cases set a variable to, for the `i`th case:
/// [`VALUES`] by turns.
fn env_value(i: usize) -> &'static str {
    VALUES[i % VALUES.len()]
}

/// Whether a commit under `case` must hand fsc exactly what the plain
/// project's build hands it, not only the same `-o:`: a [`Place::Variables`]
/// case none of whose variables is an allowed property (compared without
/// case, as MSBuild compares them), which alone may move fsc's arguments.
/// Decided by what may move them, not by the list of variables the
/// derivation calls inert, so a variable it admits by mistake is compared
/// too.
fn held_to_plain_arguments(case: &Case) -> bool {
    case.place == Place::Variables
        && case.variables.iter().all(|(name, _)| {
            !ALLOWED_PROPERTIES
                .iter()
                .any(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
        })
}

/// The toolchain's own variables, by exact name, with the shape each value
/// must have, which the grading holds fixed: its builds run in its own
/// environment, so it cannot build under another value of one. Pinned here,
/// apart from the derivation's `TOOLCHAIN_VARIABLES`, so a variable the
/// derivation comes to admit as the toolchain's by mistake, or at a shape it
/// should not, fails rather than is excused.
const HELD_FIXED: &[(&str, ToolchainValue)] = &[
    ("DOTNET_CLI_HOME", ToolchainValue::Path),
    ("DOTNET_CLI_TELEMETRY_OPTOUT", ToolchainValue::Switch),
    ("DOTNET_NOLOGO", ToolchainValue::Switch),
    (
        "DOTNET_NUGET_SIGNATURE_VERIFICATION",
        ToolchainValue::Switch,
    ),
    ("DOTNET_SKIP_FIRST_TIME_EXPERIENCE", ToolchainValue::Switch),
    (
        "DOTNET_SKIP_WORKLOAD_INTEGRITY_CHECK",
        ToolchainValue::Switch,
    ),
    ("DOTNET_ROOT", ToolchainValue::Path),
    ("HOME", ToolchainValue::Path),
    ("MSBuildUserExtensionsPath", ToolchainValue::Path),
    ("NUGET_PACKAGES", ToolchainValue::Path),
    ("PATH", ToolchainValue::SearchPath),
    ("RestoreSources", ToolchainValue::Sources),
    ("TMPDIR", ToolchainValue::Path),
];

/// Whether the grading holds the variable `name` at `value` fixed
/// ([`HELD_FIXED`]): a toolchain variable at a value of its shape, which the
/// oracle cannot build under, so a commit is counted
/// ([`Outcome::HeldFixed`]). A commit under a value of another shape is one
/// the derivation must not make, so it fails.
fn held_fixed(name: &str, value: &str) -> bool {
    HELD_FIXED
        .iter()
        .any(|(held, shape)| *held == name && shape.admits(value))
}

/// A commit is excused only for a toolchain variable at a value of its own
/// shape: the hostile toolchain values off their shape, and every name off
/// the list, are not.
#[test]
fn only_a_value_of_its_shape_is_held_fixed() {
    assert!(held_fixed("NUGET_PACKAGES", "/nonexistent/borzoi/packages"));
    assert!(held_fixed("DOTNET_NOLOGO", "true"));
    for (name, value) in [
        ("NUGET_PACKAGES", "relative/packages"),
        ("NUGET_PACKAGES", ""),
        ("DOTNET_ROOT", ""),
        ("DOTNET_NOLOGO", "yes"),
        (
            "RestoreSources",
            "https://private.example.org/v3/index.json",
        ),
        ("PATH", ".:bin"),
        ("NUGET_FALLBACK_PACKAGES", "/nonexistent"),
    ] {
        assert!(!held_fixed(name, value), "{name}={value:?}");
    }
}

/// The source of a [`Place::Variables`] case's project: it compiles, with
/// warning FS0020, which fsc reports by its code in every culture, so the
/// oracle has fsc's sign of having run even where the banner it reads is
/// translated (#1129). The source is not on fsc's command line, so the
/// arguments are still the plain project's.
const WARNING_SOURCE: &str = "module A\nlet x = 1\nx + 1\n";

/// The name the hostile file-name templates are rendered on as variables.
const PLAIN_VARIABLE: &str = "BorzoiVar";

/// One case per entry of the hostile environment alphabet (`hostile::env`),
/// its variables set together, and one per entry of the hostile file-name
/// alphabet (`hostile::name`) rendered on [`PLAIN_VARIABLE`] as a variable's
/// name, each with the dimension it stands for. A template that renders the
/// plain name (no draw of its dimension), a name the environment cannot
/// carry (empty, or holding `=` or NUL) and one that is not UTF-8 have no
/// case.
fn hostile_environment_cases() -> Vec<(Case, Dimension)> {
    let mut out = Vec::new();
    for entry in hostile_env::alphabet().entries() {
        out.push((Case::variables(entry.value), entry.dimension));
    }
    for (i, entry) in hostile_name::as_text(PLAIN_VARIABLE, "")
        .into_iter()
        .enumerate()
    {
        if entry.value.is_empty() || entry.value.contains(['=', '\0']) {
            continue;
        }
        out.push((
            Case::variables(&[(&entry.value, env_value(i))]),
            entry.dimension,
        ));
    }
    out
}

/// The variables that must decline, whatever the build does, graded in every
/// run:
///
/// - each property an `Fsc` parameter is fed from, set as a variable to a
///   line break and an output switch, which no allowed property's grammar
///   and no toolchain value's shape admits. They are chosen from the register
///   (`FSC_PARAMETERS`), unfiltered by the derivation's lists, so a list that
///   came to admit one as inert fails here;
/// - the loader's and the launcher's, which act before any of the install's
///   code runs;
/// - each `DOTNET_`/`NUGET_` variable of the hostile environments that is no
///   toolchain variable and not graded: the prefix that once admitted them.
fn environment_declines() -> Vec<Case> {
    use borzoi_msbuild::fsc::{FSC_PARAMETERS, Feed};
    let must_decline = |name: &str, value: &str| Case {
        must_decline: true,
        decline_for: Some(name.to_string()),
        ..Case::variables(&[(name, value)])
    };
    let admitted = |name: &str| {
        ALLOWED_PROPERTIES
            .iter()
            .any(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
            || HELD_FIXED.iter().any(|(t, _)| t.eq_ignore_ascii_case(name))
            || ALLOWED_ENVIRONMENT
                .iter()
                .any(|graded| graded.eq_ignore_ascii_case(name))
    };
    let mut cases = Vec::new();
    let fed: BTreeSet<&str> = FSC_PARAMETERS
        .iter()
        .filter_map(|p| match p.feed {
            Feed::Properties(names) => Some(names.iter().copied()),
            _ => None,
        })
        .flatten()
        .collect();
    assert!(!fed.is_empty(), "the register feeds fsc from properties");
    for name in fed {
        cases.push(must_decline(name, "x\n--out:obj/Evil.dll"));
    }
    for (name, value) in [
        ("LD_PRELOAD", "/nonexistent/borzoi/evil.so"),
        ("DYLD_INSERT_LIBRARIES", "/nonexistent/borzoi/evil.dylib"),
        ("BASH_ENV", "/nonexistent/borzoi/evil.sh"),
        ("BASH_FUNC_dotnet%%", "() { exit 1; }"),
        ("ENV", "/nonexistent/borzoi/evil.sh"),
    ] {
        cases.push(must_decline(name, value));
    }
    for entry in hostile_env::alphabet().entries() {
        for (name, value) in entry.value {
            let by_prefix = name.starts_with("DOTNET_") || name.starts_with("NUGET_");
            if by_prefix && !admitted(name) {
                cases.push(must_decline(name, value));
            }
        }
    }
    cases
}

/// The plain SDK project, which must commit to its own name.
fn plain_case() -> Case {
    Case {
        place: Place::Body,
        name: "TargetFramework",
        value: "net10.0".into(),
        must_commit: Some("Demo".into()),
        ..Case::default()
    }
}

/// A variable the derivation admits as inert by name, at a plain value: the
/// census's own value, which must commit.
fn plain_variable_case() -> Case {
    Case {
        must_commit: Some("Demo".into()),
        ..Case::variables(&[(ALLOWED_ENVIRONMENT[0], "plain")])
    }
}

/// Every case, the must-commit points first.
fn cases() -> Vec<Case> {
    let mut cases = vec![plain_case()];
    // Each variable the derivation admits as inert by name, at a plain value
    // a build runs under (a locale variable holding an option is no culture,
    // and the restore fails, which the derivation declines as unrestored): it
    // must commit, and leave fsc's arguments as they were. The other values
    // are graded below.
    for name in ALLOWED_ENVIRONMENT {
        cases.push(Case {
            must_commit: Some("Demo".into()),
            ..Case::variables(&[(name, "Evil")])
        });
    }
    for (name, grammar) in ALLOWED_PROPERTIES {
        let plain = plain_value(name, *grammar);
        let expect = if *name == "AssemblyName" {
            plain
        } else {
            "Demo"
        };
        cases.push(Case {
            place: Place::Body,
            name,
            value: plain.into(),
            reset: "",
            must_commit: Some(expect.into()),
            must_decline: false,
            ..Case::default()
        });
    }
    // Every option `OtherFlags` admits, in each form: fsc must compile with it.
    for (spelling, tail) in FSC_OPTIONS {
        for sample in tail.samples() {
            cases.push(Case {
                place: Place::Body,
                name: "OtherFlags",
                value: format!("{spelling}{sample}"),
                reset: "",
                must_commit: Some("Demo".into()),
                must_decline: false,
                ..Case::default()
            });
        }
    }
    // A property MSBuild sets from its command line, which the walk takes for
    // unset, read by a name the build hands fsc.
    cases.push(Case {
        place: Place::Body,
        name: "AssemblyName",
        value: "Demo$(_MSBUILDTLENABLED)".into(),
        reset: "",
        must_commit: None,
        must_decline: true,
        ..Case::default()
    });
    // An item type on no list, defined rather than declared: `Output` in an
    // item definition group is an item type, not a task output.
    cases.push(Case {
        place: Place::ItemDefinition,
        name: "Output",
        value: "safe".into(),
        reset: "",
        must_commit: None,
        must_decline: true,
        ..Case::default()
    });
    // A write or an item under a condition the walk may decide apart from
    // MSBuild must decline, whatever it writes (#993).
    for (name, grammar) in ALLOWED_PROPERTIES {
        cases.push(Case {
            place: Place::ConditionalBody,
            name,
            value: plain_value(name, *grammar).into(),
            reset: "",
            must_commit: None,
            must_decline: true,
            ..Case::default()
        });
    }
    for value in VALUES {
        cases.push(Case {
            place: Place::ConditionalItem,
            name: "Compile",
            value: (*value).into(),
            reset: "",
            must_commit: None,
            must_decline: true,
            ..Case::default()
        });
    }
    let mut rest = Vec::new();
    // Every place a project can set an allowed property, which the
    // derivation admits.
    let everywhere = [
        Place::Body,
        Place::DirectoryBuildProps,
        Place::DirectoryBuildTargets,
        Place::Global,
        Place::Environment,
    ];
    for (name, grammar) in ALLOWED_PROPERTIES {
        for place in everywhere {
            for value in VALUES.iter().copied().chain([plain_value(name, *grammar)]) {
                rest.push(Case {
                    place,
                    name,
                    value: value.into(),
                    reset: "",
                    must_commit: None,
                    must_decline: false,
                    ..Case::default()
                });
            }
        }
    }
    // The names NuGet's restore writes are admitted only from its own file,
    // which every restored case holds at their real values; set in a
    // document of the project's, they must decline. A global or variable of
    // theirs is no input (`INPUT_NAMES`), and the derivation admits none.
    assert!(PACKAGE_FOLDER.starts_with(RESTORE_PROPERTY_PREFIX));
    let package_folder = (PACKAGE_FOLDER, Grammar::Path);
    for (name, grammar) in RESTORE_PROPERTIES.iter().chain([&package_folder]) {
        for place in [Place::Body, Place::DirectoryBuildProps] {
            for value in VALUES.iter().copied().chain([plain_value(name, *grammar)]) {
                rest.push(Case {
                    place,
                    name,
                    value: value.into(),
                    reset: "",
                    must_commit: None,
                    must_decline: true,
                    ..Case::default()
                });
            }
        }
    }
    // The item types and metadata NuGet's restore writes are admitted, like
    // its properties, only from its own file: written by the project, they
    // must decline.
    for (place, names, must_decline) in [
        (Place::Item, ALLOWED_ITEM_TYPES, false),
        (Place::Item, RESTORE_ITEM_TYPES, true),
        (Place::Metadata, ALLOWED_METADATA, false),
        (Place::Metadata, RESTORE_METADATA, true),
        (Place::MetadataChild, ALLOWED_METADATA, false),
        (Place::MetadataDefinition, ALLOWED_METADATA, false),
    ] {
        for name in names {
            for value in VALUES {
                rest.push(Case {
                    place,
                    name,
                    value: (*value).into(),
                    reset: "",
                    must_commit: None,
                    must_decline,
                    ..Case::default()
                });
            }
        }
    }
    // Each allowed metadata name on each admitted item type, as an attribute.
    for host in ALLOWED_ITEM_TYPES {
        for name in ALLOWED_METADATA {
            for value in VALUES {
                rest.push(Case {
                    place: Place::MetadataOn(host),
                    name,
                    value: (*value).into(),
                    reset: "",
                    must_commit: None,
                    must_decline: false,
                    ..Case::default()
                });
            }
        }
    }
    // A Compile item a glob matches keeps the glob's spelling of its
    // directory, which fsc reads (`@sub/../Args.fs`, a response file).
    for value in ["@sub/../A*.fs", "sub/../A*.fs", "A?.fs"] {
        cases.push(Case {
            place: Place::Item,
            name: "Compile",
            value: value.into(),
            reset: "",
            must_commit: None,
            must_decline: true,
            ..Case::default()
        });
    }
    // The restore-only metadata in its other forms.
    for place in [Place::MetadataChild, Place::MetadataDefinition] {
        for name in RESTORE_METADATA {
            rest.push(Case {
                place,
                name,
                value: "Evil".into(),
                reset: "",
                must_commit: None,
                must_decline: true,
                ..Case::default()
            });
        }
    }
    // Each allowed property's value split by comments, and written into
    // NuGet's restore file after the restore.
    // The names only NuGet's restore file may write, written there.
    let package_folder = (PACKAGE_FOLDER, Grammar::Path);
    for (name, grammar) in RESTORE_PROPERTIES.iter().chain([&package_folder]) {
        for value in VALUES.iter().copied().chain([plain_value(name, *grammar)]) {
            rest.push(Case {
                place: Place::RestoreProps,
                name,
                value: value.into(),
                reset: "",
                must_commit: None,
                must_decline: false,
                ..Case::default()
            });
        }
    }
    for (place, names) in [
        (Place::RestoreItem, RESTORE_ITEM_TYPES),
        (Place::RestoreMetadata, RESTORE_METADATA),
    ] {
        for name in names {
            for value in VALUES {
                rest.push(Case {
                    place,
                    name,
                    value: (*value).into(),
                    reset: "",
                    must_commit: None,
                    must_decline: false,
                    ..Case::default()
                });
            }
        }
    }
    for place in [Place::BodySplit, Place::BodySpaced, Place::RestoreProps] {
        for (name, grammar) in ALLOWED_PROPERTIES {
            for value in VALUES.iter().copied().chain([plain_value(name, *grammar)]) {
                rest.push(Case {
                    place,
                    name,
                    value: value.into(),
                    reset: "",
                    must_commit: None,
                    must_decline: false,
                    ..Case::default()
                });
            }
        }
        cases.push(Case {
            place,
            name: "AssemblyName",
            value: "Friend".into(),
            reset: "",
            must_commit: Some("Friend".into()),
            must_decline: false,
            ..Case::default()
        });
        cases.push(Case {
            place,
            name: "AssemblyName",
            value: "Demo$(_MSBUILDTLENABLED)".into(),
            reset: "",
            must_commit: None,
            must_decline: true,
            ..Case::default()
        });
    }
    // A Compile file git does not track, which reaches fsc twice: as a source
    // and as an embedded file.
    for value in VALUES {
        rest.push(Case {
            place: Place::UntrackedCompile,
            name: "EmbedUntrackedSources",
            value: format!("{value}.fs"),
            reset: "",
            must_commit: (*value == "Evil").then(|| "Demo".to_string()),
            must_decline: false,
            ..Case::default()
        });
    }
    // A package content file under each build action: those reaching fsc must
    // decline, the others commit. The grader's own judgement of which reach
    // fsc, not the derivation's list, so a list that widens fails here.
    for action in ["Compile", "EmbeddedResource", "None", "Content"] {
        let admitted = ["None", "Content"].contains(&action);
        rest.push(Case {
            place: Place::PackageContent,
            name: "ContentFiles",
            value: action.into(),
            reset: "",
            must_commit: admitted.then(|| "Demo".to_string()),
            must_decline: !admitted,
            ..Case::default()
        });
    }
    // A reference path fsc is handed, from a package's compile asset.
    for value in VALUES {
        rest.push(Case {
            place: Place::PackageDll,
            name: "PackageReference",
            value: (*value).into(),
            reset: "",
            must_commit: None,
            must_decline: false,
            ..Case::default()
        });
    }
    // A file name the default `EmbeddedResource` glob reaches.
    for value in VALUES {
        rest.push(Case {
            place: Place::ResxName,
            name: "EmbeddedResource",
            value: (*value).into(),
            reset: "",
            must_commit: None,
            must_decline: false,
            ..Case::default()
        });
    }
    // A value the SDK may copy before a later write puts the plain one back.
    for (name, grammar) in ALLOWED_PROPERTIES {
        for place in [
            Place::BodyThenTargets,
            Place::PropsThenBody,
            Place::PropsThenTargets,
        ] {
            for value in VALUES {
                rest.push(Case {
                    place,
                    name,
                    value: (*value).into(),
                    reset: plain_value(name, *grammar),
                    must_commit: None,
                    must_decline: false,
                    ..Case::default()
                });
            }
        }
    }
    // The variables the derivation admits as inert by name, at every value.
    for name in ALLOWED_ENVIRONMENT {
        for value in VALUES {
            rest.push(Case::variables(&[(name, value)]));
        }
    }
    cases.extend(environment_declines());
    cases.extend(rest);
    cases
}

/// `value` escaped for XML text or an attribute, line breaks as character
/// references (which XML keeps, where it would fold a literal `\r`).
fn xml(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\n', "&#10;")
        .replace('\r', "&#13;")
}

/// `inputs`, or `None` when the place cannot carry the value (a global's line
/// break). A name the derivation admits from that place but the oracle does
/// not take as an input is a hole in the grading, and fails.
fn expressible(case: &Case, inputs: Result<BuildInputs, InputError>) -> Option<BuildInputs> {
    match inputs {
        Ok(inputs) => Some(inputs),
        Err(InputError::Unpassable { .. }) => None,
        Err(e) => panic!(
            "{}: an admitted name the oracle cannot set: {e:?}",
            case.label()
        ),
    }
}

/// Lay `case` out under `dir`; the project file and the build's inputs, or
/// `None` when the place cannot carry the value (a global's line break).
fn lay_out(case: &Case, dir: &Path) -> Option<(std::path::PathBuf, BuildInputs)> {
    let value = xml(&case.value);
    let reset = xml(case.reset);
    let group = |name: &str, value: &str| {
        format!("<Project><PropertyGroup><{name}>{value}</{name}></PropertyGroup></Project>")
    };
    let mut body = String::new();
    let mut items = String::new();
    let mut compile_attributes = String::new();
    let mut compile_children = String::new();
    let mut definitions = String::new();
    let mut inputs = BuildInputs::new();
    match case.place {
        Place::Body => body = format!("<{0}>{value}</{0}>", case.name),
        Place::DirectoryBuildProps => std::fs::write(
            dir.join("Directory.Build.props"),
            format!(
                "<Project><PropertyGroup><{0}>{value}</{0}></PropertyGroup></Project>",
                case.name
            ),
        )
        .unwrap(),
        Place::DirectoryBuildTargets => std::fs::write(
            dir.join("Directory.Build.targets"),
            group(case.name, &value),
        )
        .unwrap(),
        Place::Global => inputs = expressible(case, inputs.global(case.name, &case.value))?,
        Place::Environment => inputs = expressible(case, inputs.env(case.name, &case.value))?,
        Place::Item => items = format!("<{} Include=\"{value}\" />", case.name),
        Place::ItemDefinition => {
            definitions = format!(
                "<ItemDefinitionGroup><{0}><Link>{value}</Link></{0}></ItemDefinitionGroup>",
                case.name
            )
        }
        Place::ConditionalBody => {
            body = format!(
                "<{0} Condition=\"{1}\">{value}</{0}>",
                case.name,
                xml(PATH_CONDITION)
            )
        }
        Place::ConditionalItem => {
            items = format!(
                "<{} Include=\"{value}\" Condition=\"{}\" />",
                case.name,
                xml(PATH_CONDITION)
            )
        }
        Place::ResxName => {
            let file = dir.join(tree_file(&format!("{}.resx", case.value))?);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(&file, RESX).unwrap();
        }
        Place::UntrackedCompile => {
            let file = dir.join(UNTRACKED).join(tree_file(&case.value)?);
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(&file, "module Untracked\nlet y = 1\n").unwrap();
            items = format!("<Compile Include=\"{UNTRACKED}/{value}\" />");
        }
        Place::PackageContent => {
            let side = dir.parent().unwrap();
            let (feed, packages) = (side.join("feed"), side.join("packages"));
            std::fs::create_dir_all(&feed).unwrap();
            std::fs::create_dir_all(&packages).unwrap();
            let file = "any/any/PackageContent.fs";
            let nuspec = format!(
                "<?xml version=\"1.0\" encoding=\"utf-8\"?><package \
                 xmlns=\"http://schemas.microsoft.com/packaging/2013/05/nuspec.xsd\"><metadata>\
                 <id>{PACKAGE}</id><version>1.0.0</version><authors>borzoi</authors>\
                 <description>A package with one content file.</description>\
                 <contentFiles><files include=\"{file}\" buildAction=\"{}\" /></contentFiles>\
                 </metadata></package>",
                case.value
            );
            let package = stored_zip(&[
                ("[Content_Types].xml", CONTENT_TYPES.as_bytes()),
                (&format!("{PACKAGE}.nuspec"), nuspec.as_bytes()),
                (
                    &format!("contentFiles/{file}"),
                    b"module PackageContent\nlet z = 1\n",
                ),
            ]);
            std::fs::write(
                feed.join(format!("{}.1.0.0.nupkg", PACKAGE.to_ascii_lowercase())),
                package,
            )
            .unwrap();
            inputs = inputs.package_source(&feed).packages_folder(&packages);
            items = format!("<PackageReference Include=\"{PACKAGE}\" Version=\"1.0.0\" />");
        }
        Place::PackageDll => {
            // A local feed and package folder of the fixture's own, beside
            // its project's directory. A file name holds no `/`, so one in
            // the value stands as `_`.
            let side = dir.parent().unwrap();
            let (feed, packages) = (side.join("feed"), side.join("packages"));
            std::fs::create_dir_all(&feed).unwrap();
            std::fs::create_dir_all(&packages).unwrap();
            let nuspec = format!(
                "<?xml version=\"1.0\" encoding=\"utf-8\"?><package \
                 xmlns=\"http://schemas.microsoft.com/packaging/2013/05/nuspec.xsd\"><metadata>\
                 <id>{PACKAGE}</id><version>1.0.0</version><authors>borzoi</authors>\
                 <description>A package whose assembly's file name is perturbed.</description>\
                 </metadata></package>"
            );
            let dll_entry = format!("lib/net10.0/{}.dll", case.value.replace('/', "_"));
            let package = stored_zip(&[
                ("[Content_Types].xml", CONTENT_TYPES.as_bytes()),
                (&format!("{PACKAGE}.nuspec"), nuspec.as_bytes()),
                (&dll_entry, library_dll()),
            ]);
            std::fs::write(
                feed.join(format!("{}.1.0.0.nupkg", PACKAGE.to_ascii_lowercase())),
                package,
            )
            .unwrap();
            inputs = inputs.package_source(&feed).packages_folder(&packages);
            items = format!("<PackageReference Include=\"{PACKAGE}\" Version=\"1.0.0\" />");
        }
        Place::BodyThenTargets => {
            body = format!("<{0}>{value}</{0}>", case.name);
            std::fs::write(
                dir.join("Directory.Build.targets"),
                group(case.name, &reset),
            )
            .unwrap();
        }
        Place::PropsThenBody => {
            std::fs::write(dir.join("Directory.Build.props"), group(case.name, &value)).unwrap();
            body = format!("<{0}>{reset}</{0}>", case.name);
        }
        Place::PropsThenTargets => {
            std::fs::write(dir.join("Directory.Build.props"), group(case.name, &value)).unwrap();
            std::fs::write(
                dir.join("Directory.Build.targets"),
                group(case.name, &reset),
            )
            .unwrap();
        }
        Place::MetadataOn(host) => {
            std::fs::write(dir.join("readme.txt"), "").unwrap();
            match host {
                "Compile" => compile_attributes = format!(" {}=\"{value}\"", case.name),
                "PackageReference" => {
                    items = format!(
                        "<PackageReference Update=\"FSharp.Core\" {}=\"{value}\" />",
                        case.name
                    )
                }
                _ => {
                    items = format!(
                        "<{host} Include=\"readme.txt\" {}=\"{value}\" />",
                        case.name
                    )
                }
            }
        }
        Place::Metadata | Place::MetadataChild | Place::MetadataDefinition => {
            // The item the metadata applies to: its type and its operation.
            let host = match case.name {
                "Link" => "Compile",
                name if ["CopyToOutputDirectory", "Visible"]
                    .into_iter()
                    .chain(RESTORE_METADATA.iter().copied())
                    .any(|n| n == name) =>
                {
                    std::fs::write(dir.join("readme.txt"), "").unwrap();
                    "None"
                }
                _ => "PackageReference",
            };
            let operation = match host {
                "Compile" => "",
                "None" => " Include=\"readme.txt\"",
                _ => " Update=\"FSharp.Core\"",
            };
            let child = format!("<{0}>{value}</{0}>", case.name);
            match (case.place, host) {
                (Place::Metadata, "Compile") => {
                    compile_attributes = format!(" {}=\"{value}\"", case.name)
                }
                (Place::Metadata, _) => {
                    items = format!("<{host}{operation} {}=\"{value}\" />", case.name)
                }
                (Place::MetadataChild, "Compile") => compile_children = child,
                (Place::MetadataChild, _) => items = format!("<{host}{operation}>{child}</{host}>"),
                _ => {
                    definitions = format!(
                        "<ItemDefinitionGroup><{host}>{child}</{host}></ItemDefinitionGroup>"
                    );
                    if host == "None" {
                        items = format!("<{host}{operation} />");
                    }
                }
            }
        }
        Place::BodySplit | Place::BodySpaced => {
            // Comments between each two characters, each piece escaped.
            let separator = if case.place == Place::BodySplit {
                "<!---->"
            } else {
                "<!--a--> <!--b-->"
            };
            let split = case
                .value
                .chars()
                .map(|c| xml(&c.to_string()))
                .collect::<Vec<_>>()
                .join(separator);
            body = format!("<{0}>{split}</{0}>", case.name);
        }
        Place::Variables => inputs = split_variables(case)?.0,
        // Written after the restore ([`after_restore`]).
        Place::RestoreProps | Place::RestoreItem => {}
        Place::RestoreMetadata => std::fs::write(dir.join("readme.txt"), "").unwrap(),
    }
    let source = if case.place == Place::Variables {
        WARNING_SOURCE
    } else {
        "module A\nlet x = 1\n"
    };
    std::fs::write(dir.join("A.fs"), source).unwrap();
    let project = dir.join("Demo.fsproj");
    let text = format!(
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
         <TargetFramework>net10.0</TargetFramework>{body}</PropertyGroup>\
         {definitions}<ItemGroup>{items}<Compile Include=\"A.fs\"{compile_attributes}>{compile_children}</Compile></ItemGroup></Project>"
    );
    std::fs::write(&project, text).unwrap();
    if case.place == Place::UntrackedCompile {
        commit_ignoring_untracked(dir);
    }
    Some((project, inputs))
}

/// What `case` changes once the project at `project` is restored: for
/// [`Place::RestoreProps`], [`Place::RestoreItem`] and
/// [`Place::RestoreMetadata`], a group of its own in NuGet's restore file.
fn after_restore(case: &Case, project: &Path) {
    let value = xml(&case.value);
    let group = match case.place {
        Place::RestoreProps => {
            format!(
                "<PropertyGroup><{0}>{value}</{0}></PropertyGroup>",
                case.name
            )
        }
        Place::RestoreItem => {
            format!(
                "<ItemGroup><{} Include=\"{value}\" /></ItemGroup>",
                case.name
            )
        }
        Place::RestoreMetadata => format!(
            "<ItemGroup><None Include=\"readme.txt\"><{0}>{value}</{0}></None></ItemGroup>",
            case.name
        ),
        _ => return,
    };
    let group = format!("{group}</Project>");
    let props = borzoi_msbuild::fsc::restore_props(project).unwrap();
    let text = host_fs::read_to_string(&props).expect("the restore wrote its props");
    assert!(text.trim_end().ends_with("</Project>"));
    let at = text.rfind("</Project>").unwrap();
    std::fs::write(&props, format!("{}{group}", &text[..at])).unwrap();
}

/// `name` as a file of the fixture's tree, or `None` when it would leave it.
fn tree_file(name: &str) -> Option<&Path> {
    let relative = Path::new(name);
    let escapes = relative.has_root()
        || relative
            .components()
            .any(|c| matches!(c, std::path::Component::ParentDir));
    (!escapes).then_some(relative)
}

/// Make `dir` a git repository with one commit holding the project file,
/// `A.fs`, and a `.gitignore` ignoring [`UNTRACKED`]: what SourceLink counts as
/// untracked.
fn commit_ignoring_untracked(dir: &Path) {
    std::fs::write(dir.join(".gitignore"), format!("/{UNTRACKED}/\n")).unwrap();
    let git = |args: &[&str]| {
        let mut cmd = std::process::Command::new("git");
        cmd.current_dir(dir)
            .args(["-c", "user.name=borzoi", "-c", "user.email=borzoi@invalid"])
            .args([
                "-c",
                "commit.gpgsign=false",
                "-c",
                "init.defaultBranch=main",
            ])
            .args(args);
        let output = BoundedCommand::new(cmd)
            .timeout(std::time::Duration::from_secs(60))
            .run()
            .unwrap_or_else(|e| panic!("git {args:?} in {}: {e}", dir.display()));
        assert!(
            output.status.success(),
            "git {args:?} in {}: {}",
            dir.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    };
    git(&["init", "-q"]);
    git(&["add", "Demo.fsproj", "A.fs", ".gitignore"]);
    git(&["commit", "-q", "-m", "fixture"]);
}

/// The bytes of a small library assembly, built once per run, which the
/// package [`Place::PackageDll`] makes ships under each perturbed name.
fn library_dll() -> &'static [u8] {
    static DLL: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    DLL.get_or_init(|| {
        let tmp = tempfile::TempDir::new().unwrap();
        let dir = tmp.path();
        std::fs::write(dir.join("L.fs"), "module PerturbedLib\nlet y = 1\n").unwrap();
        std::fs::write(
            dir.join("PerturbedLib.fsproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>\
             <TargetFramework>net10.0</TargetFramework></PropertyGroup>\
             <ItemGroup><Compile Include=\"L.fs\" /></ItemGroup></Project>",
        )
        .unwrap();
        let mut cmd = msbuild_command(dir, inherited_environment(), &BuildInputs::new());
        cmd.args(["-nodeReuse:false", "-restore", "-t:Build"]);
        BoundedCommand::new(cmd)
            .timeout(std::time::Duration::from_secs(900))
            .run_ok("building the perturbed package's library");
        let bytes = host_fs::read(dir.join("bin/Debug/net10.0/PerturbedLib.dll")).unwrap();
        drop(tmp);
        bytes
    })
}

/// A zip archive of `entries`, stored without compression: what a `.nupkg`
/// is, made without a zip library.
fn stored_zip(entries: &[(&str, &[u8])]) -> Vec<u8> {
    fn crc32(bytes: &[u8]) -> u32 {
        let mut crc = !0u32;
        for byte in bytes {
            crc ^= u32::from(*byte);
            for _ in 0..8 {
                crc = if crc & 1 == 1 {
                    (crc >> 1) ^ 0xedb8_8320
                } else {
                    crc >> 1
                };
            }
        }
        !crc
    }
    let (mut out, mut central) = (Vec::new(), Vec::new());
    for (name, data) in entries {
        let (crc, size, offset) = (crc32(data), data.len() as u32, out.len() as u32);
        let name_len = name.len() as u16;
        // Version 2.0, UTF-8 names, stored, 1980-01-01.
        let common = |buf: &mut Vec<u8>| {
            for field in [20u16, 0x0800, 0, 0, 0x21] {
                buf.extend(field.to_le_bytes());
            }
            for field in [crc, size, size] {
                buf.extend(field.to_le_bytes());
            }
            buf.extend(name_len.to_le_bytes());
            buf.extend(0u16.to_le_bytes());
        };
        out.extend(0x0403_4b50u32.to_le_bytes());
        common(&mut out);
        out.extend(name.as_bytes());
        out.extend(*data);
        central.extend(0x0201_4b50u32.to_le_bytes());
        central.extend(20u16.to_le_bytes());
        common(&mut central);
        for field in [0u16, 0, 0] {
            central.extend(field.to_le_bytes());
        }
        central.extend(0u32.to_le_bytes());
        central.extend(offset.to_le_bytes());
        central.extend(name.as_bytes());
    }
    let (count, start, size) = (entries.len() as u16, out.len() as u32, central.len() as u32);
    out.extend(central);
    out.extend(0x0605_4b50u32.to_le_bytes());
    for field in [0u16, 0, count, count] {
        out.extend(field.to_le_bytes());
    }
    out.extend(size.to_le_bytes());
    out.extend(start.to_le_bytes());
    out.extend(0u16.to_le_bytes());
    out
}

/// Whether every variable of `case` reaches the evaluation alone
/// ([`split_variables`]): the build's inputs are empty, so its restore is
/// the plain variables fixture's, which [`shared_variables_fixture`] makes
/// once. Such a case is never built, as a commit under a variable the oracle
/// does not take returns before the build.
fn evaluator_only(case: &Case) -> bool {
    case.place == Place::Variables
        && split_variables(case)
            .is_some_and(|(inputs, rest)| inputs == BuildInputs::new() && !rest.is_empty())
}

/// The project of a [`Place::Variables`] case with no variables, restored
/// once per run under no inputs: what every [`evaluator_only`] case's own
/// restore would make. It is read, never built.
fn shared_variables_fixture() -> &'static Path {
    static FIXTURE: std::sync::OnceLock<(tempfile::TempDir, std::path::PathBuf)> =
        std::sync::OnceLock::new();
    let (_, project) = FIXTURE.get_or_init(|| {
        let tmp = tempfile::TempDir::new().unwrap();
        let dir = host_fs::canonicalize(tmp.path()).unwrap().join("project");
        std::fs::create_dir(&dir).unwrap();
        let (project, inputs) =
            lay_out(&Case::variables(&[]), &dir).expect("the variables fixture lays out");
        restore(&project, &inputs);
        (tmp, project)
    });
    project
}

thread_local! {
    /// How many restores this thread has run, which
    /// [`evaluator_only_cases_share_one_restore`] counts.
    static RESTORES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The environment the grading's builds inherit, and its evaluations are
/// handed beneath their own variables: this process's, read once
/// ([`grading_build_environment`]). Every build, restore and probe the
/// grading runs takes it, so it is checked at its first use, before any of
/// them runs.
///
/// # Panics
///
/// When the derivation declines it: no case could be graded.
fn inherited_environment() -> &'static BuildEnvironment {
    static ENVIRONMENT: std::sync::OnceLock<BuildEnvironment> = std::sync::OnceLock::new();
    ENVIRONMENT.get_or_init(|| {
        grading_build_environment(std::env::vars()).unwrap_or_else(|refusal| panic!("{refusal}"))
    })
}

/// The environment the grading's builds run under, given the variables
/// `inherited`: the oracle's ([`BuildEnvironment::inherited`]), with `PATH`
/// cut to its plain entries ([`graded_path`]), which changes nothing a build
/// measures; or, when the derivation declines it, the refusal
/// ([`refusal`]). The grading holds these variables fixed, so it cannot grade
/// under another value of one; it refuses rather than grade under a value
/// every case would decline for.
fn grading_build_environment(
    inherited: impl IntoIterator<Item = (String, String)>,
) -> Result<BuildEnvironment, String> {
    let environment =
        BuildEnvironment::inherited(inherited.into_iter().filter_map(|(name, value)| {
            match name.as_str() {
                "PATH" => graded_path(&value).map(|path| (name, path)),
                _ => Some((name, value)),
            }
        }));
    let variables = environment
        .vars()
        .map(|(n, v)| (n.to_string(), v.to_string()))
        .collect();
    refusal(&variables).map_or(Ok(environment), Err)
}

/// Why the grading refuses to run under `environment`, if the derivation
/// declines it: a grading under it measures nothing (each case declines for
/// the environment alone). It names the rule broken (a `NameDecline`, which
/// names variables and shapes, never a value).
fn refusal(environment: &HashMap<String, String>) -> Option<String> {
    borzoi_msbuild::fsc::environment_decline(environment).map(|decline| {
        format!(
            "the grading's environment is out of the compiled-name derivation's domain \
             ({decline:?}), so no case can be graded under it: give the variable a value of \
             its shape, or unset it"
        )
    })
}

/// The `PATH` the grading's builds run under, given this process's `path`:
/// its entries that are absolute, without a control character or a `%`
/// (MSBuild reads the value as escaped text), in order, as the platform
/// separates them; `None`, so no `PATH` at all, when none is. The derivation
/// declines a `PATH` holding any other entry, and a build looks up nothing it
/// measures through `PATH` (the host is launched by its absolute path), so
/// the grading's builds leave such entries out.
fn graded_path(path: &str) -> Option<String> {
    let kept: Vec<std::path::PathBuf> = std::env::split_paths(path)
        .filter(|entry| {
            entry.is_absolute()
                && entry
                    .to_str()
                    .is_some_and(|text| !text.chars().any(|c| c.is_control() || c == '%'))
        })
        .collect();
    if kept.is_empty() {
        return None;
    }
    std::env::join_paths(kept)
        .ok()
        .map(|joined| joined.to_string_lossy().into_owned())
}

/// Restore the project at `project` in place, under `inputs`, as the build
/// would; a failed restore leaves the evaluation unrestored, which the
/// derivation declines.
fn restore(project: &Path, inputs: &BuildInputs) {
    RESTORES.with(|n| n.set(n.get() + 1));
    let mut cmd = msbuild_command(project.parent().unwrap(), inherited_environment(), inputs);
    cmd.args(["-nodeReuse:false", "-t:Restore"]);
    for (name, value) in inputs.globals() {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(project);
    BoundedCommand::new(cmd)
        .timeout(std::time::Duration::from_secs(900))
        .run()
        .unwrap_or_else(|e| panic!("restoring {}: {e}", project.display()));
}

/// The variables of `case` the oracle does not take, which the evaluation
/// alone is handed.
fn unsettable(case: &Case) -> Vec<(String, String)> {
    split_variables(case)
        .map(|(_, rest)| rest)
        .unwrap_or_default()
}

/// `case`'s variables, in order, as the build's inputs where the oracle takes
/// them ([`BuildInputs::env`]: a name on its reviewed list), and the rest: a
/// name off the list, and a second spelling of a name already set (which a
/// build's environment holds, and the oracle does not take twice). The rest
/// reach the evaluation alone, never a real restore or build: a name off the
/// list may choose what the build imports. `None` when a value cannot be
/// carried.
fn split_variables(case: &Case) -> Option<(BuildInputs, Vec<(String, String)>)> {
    let mut inputs = BuildInputs::new();
    let mut rest = Vec::new();
    for (name, value) in &case.variables {
        match inputs.clone().env(name, value) {
            Ok(next) => inputs = next,
            Err(InputError::NotAnInput(_) | InputError::Repeated(_)) => {
                rest.push((name.clone(), value.clone()));
            }
            Err(InputError::Unpassable { .. }) => return None,
        }
    }
    Some((inputs, rest))
}

/// Our verdict on the project at `project`, built under `inputs`, its
/// evaluation also handed `extra`.
fn ours(project: &Path, inputs: &BuildInputs, extra: &[(String, String)]) -> CompiledAssemblyName {
    ours_under(project, inputs, extra, &common::dotnet_root_from_env())
}

/// [`ours`], resolving SDKs from the .NET install at `dotnet_root`.
fn ours_under(
    project: &Path,
    inputs: &BuildInputs,
    extra: &[(String, String)],
    dotnet_root: &Path,
) -> CompiledAssemblyName {
    let globals: HashMap<String, String> = inputs
        .globals()
        .map(|(n, v)| (n.to_string(), v.to_string()))
        .collect();
    let mut environment = grading_environment();
    environment.extend(inputs.env_vars(inherited_environment()));
    environment.extend(extra.iter().cloned());
    // The SDK the evaluation resolved is the one being graded.
    assembly_name::derive(project, &globals, &environment, dotnet_root, Sdks::Resolved)
}

/// The environment every case's evaluation is handed beneath its own
/// variables: the grading's builds' own ([`inherited_environment`]), and the
/// `MSBuildUserExtensionsPath` MSBuild computes for itself, as the oracle's
/// other differentials hand it to our evaluation
/// ([`evaluation_environment`]).
///
/// # Panics
///
/// When the derivation declines it: no case could be graded.
fn grading_environment() -> HashMap<String, String> {
    let build = inherited_environment();
    evaluation_environment(build, msbuild_user_extensions_path(build))
        .unwrap_or_else(|refusal| panic!("{refusal}"))
}

/// The environment of [`grading_environment`], given the build's environment
/// `build` and MSBuild's `MSBuildUserExtensionsPath`; or, when the derivation
/// declines it, the refusal ([`refusal`]).
fn evaluation_environment(
    build: &BuildEnvironment,
    user_extensions: &str,
) -> Result<HashMap<String, String>, String> {
    let mut environment: HashMap<String, String> = build
        .vars()
        .map(|(n, v)| (n.to_string(), v.to_string()))
        .collect();
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        user_extensions.to_string(),
    );
    refusal(&environment).map_or(Ok(environment), Err)
}

/// The directories of the MSBuilds that built the agreed cases: the SDKs the
/// run graded.
static BUILT_BY: Mutex<std::collections::BTreeSet<std::path::PathBuf>> =
    Mutex::new(std::collections::BTreeSet::new());

/// What one case came to.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    /// The place cannot carry the value.
    Inexpressible,
    /// We declined, for this reason.
    Declined(String),
    /// We committed, and the oracle answered with the same name.
    Agreed,
    /// We committed, and the oracle could not vouch for a compile.
    Unanswered,
    /// We committed under a toolchain variable the grading holds fixed, so
    /// the oracle cannot build under it.
    HeldFixed,
}

/// Grade `case`; `Err` with a failure message on a wrong commit or a missed
/// must-commit. Every grading path comes through here, so each case's
/// restore and build run under a permit of [`grading_budget`].
fn grade(case: &Case) -> Result<Outcome, String> {
    grading_budget().hold(|| grade_unbudgeted(case))
}

/// [`grade`], without taking a permit.
fn grade_unbudgeted(case: &Case) -> Result<Outcome, String> {
    let tmp = tempfile::TempDir::new().unwrap();
    let (project, inputs) = if evaluator_only(case) {
        // Restored under no inputs, it is the shared fixture, read and never
        // built: a commit under a variable the oracle does not take returns
        // below before any build.
        (shared_variables_fixture().to_path_buf(), BuildInputs::new())
    } else {
        let dir = host_fs::canonicalize(tmp.path()).unwrap().join("project");
        std::fs::create_dir(&dir).unwrap();
        let Some((project, inputs)) = lay_out(case, &dir) else {
            return Ok(Outcome::Inexpressible);
        };
        // The derivation reads a restored evaluation, as the build makes one.
        restore(&project, &inputs);
        after_restore(case, &project);
        (project, inputs)
    };
    let extra = unsettable(case);
    let name = match ours(&project, &inputs, &extra) {
        CompiledAssemblyName::Known(name) => name,
        CompiledAssemblyName::Unknown(why) => {
            if let Some(name) = &case.decline_for
                && !declines_for(&why, name)
            {
                return Err(format!(
                    "{}: declined ({why:?}), but not for {name}",
                    case.label()
                ));
            }
            return match &case.must_commit {
                Some(_) => Err(format!("{}: declined ({why:?}), must commit", case.label())),
                None => {
                    if std::env::var_os("BORZOI_FSC_NAME_VERBOSE").is_some() {
                        eprintln!("declined: {}: {why:?}", case.label());
                    }
                    Ok(Outcome::Declined(
                        format!("{why:?}").split('(').next().unwrap().to_string(),
                    ))
                }
            };
        }
    };
    if case.must_decline {
        return Err(format!(
            "{}: committed {name:?}, must decline",
            case.label()
        ));
    }
    if case.must_commit.as_ref().is_some_and(|want| *want != name) {
        return Err(format!(
            "{}: committed {name:?}, must commit {:?}",
            case.label(),
            case.must_commit
        ));
    }
    if !extra.is_empty() {
        // An evaluator-only case ends here, so the shared fixture is never
        // built.
        return if extra.iter().all(|(name, value)| held_fixed(name, value)) {
            Ok(Outcome::HeldFixed)
        } else {
            Err(format!(
                "{}: committed {name:?} under variables the oracle cannot set: {extra:?}",
                case.label()
            ))
        };
    }
    // `fsc_args`'s domain: a build that does not read the process's command
    // line, which a tree without property functions and build code cannot.
    // Only a committed case is built, so only one is held to it: a value
    // that reads the build (`hostile::value`'s `ReadsTheBuild`) must have
    // declined.
    let dir = project.parent().unwrap();
    let documents = [
        project.to_path_buf(),
        dir.join("Directory.Build.props"),
        dir.join("Directory.Build.targets"),
        borzoi_msbuild::fsc::restore_props(&project).unwrap(),
    ];
    for spelling in ["$([", "<Target ", "<Target>", "<UsingTask ", "<Exec "] {
        if let Some(document) = documents.iter().find(|document| {
            host_fs::read_to_string(document)
                .unwrap_or_default()
                .contains(spelling)
        }) {
            return Err(format!(
                "{}: committed {name:?} for a tree whose {} holds {spelling:?}, outside fsc_args' domain",
                case.label(),
                document.display()
            ));
        }
    }
    let request = FscArgsRequest {
        project: &project,
        environment: inherited_environment(),
        inputs: &inputs,
    };
    match fsc_args(&request) {
        Ok(build) => {
            if case.must_commit.is_some() && !build.succeeded {
                return Err(format!(
                    "{}: committed {name:?}, but the build failed\n{}",
                    case.label(),
                    build
                        .invocations
                        .first()
                        .map(|i| i.response_file.as_str())
                        .unwrap_or_default()
                ));
            }
            for invocation in &build.invocations {
                let theirs = invocation
                    .arguments()
                    .map_err(|e| format!("{}: unreadable arguments {e:?}", case.label()))?
                    .assembly_name();
                if theirs.as_deref() != Some(name.as_str()) {
                    return Err(format!(
                        "{}: WRONG COMMIT: we say {name:?}, fsc's -o: names {theirs:?}\n{}",
                        case.label(),
                        invocation.response_file
                    ));
                }
                // The route the case exists for is live: fsc is handed the
                // untracked file itself to embed.
                let untracked = format!("{UNTRACKED}/{}", case.value);
                let embeds_it = invocation.arguments().is_ok_and(|args| {
                    args.options
                        .iter()
                        .any(|o| o.name == "embed" && o.argument.ends_with(&untracked))
                });
                if case.place == Place::UntrackedCompile && !embeds_it {
                    return Err(format!(
                        "{}: fsc embeds no untracked file, so the case grades nothing\n{}",
                        case.label(),
                        invocation.response_file
                    ));
                }
            }
            if held_to_plain_arguments(case) {
                let ours = normalised_arguments(&build, dir);
                let plain = plain_arguments();
                if ours != plain {
                    return Err(format!(
                        "{}: a variable that is no allowed property moved fsc's arguments\nplain:\n{plain}\nwith it:\n{ours}",
                        case.label()
                    ));
                }
            }
            BUILT_BY
                .lock()
                .unwrap()
                .insert(build.msbuild_directory.clone());
            Ok(Outcome::Agreed)
        }
        Err(decline) if case.must_commit.is_some() || held_to_plain_arguments(case) => {
            Err(format!(
                "{}: committed {name:?}, but the oracle did not answer: {decline:?}",
                case.label()
            ))
        }
        Err(FscArgsDecline::NoBuild(why) | FscArgsDecline::Unanswered(why)) => {
            let first = why.first().map(String::as_str).unwrap_or_default();
            eprintln!(
                "unanswered: {}: {}",
                case.label(),
                first.lines().next().unwrap_or_default()
            );
            Ok(Outcome::Unanswered)
        }
    }
}

/// The response files of `build`, joined, the project's directory `dir`
/// spelt `<dir>`.
fn normalised_arguments(
    build: &borzoi_oracle_harness::msbuild_oracle::FscBuild,
    dir: &Path,
) -> String {
    let dir = dir.to_string_lossy();
    build
        .invocations
        .iter()
        .map(|i| i.response_file.replace(dir.as_ref(), "<dir>"))
        .collect::<Vec<_>>()
        .join("\n----\n")
}

/// [`normalised_arguments`] of the plain project's build, once per run.
fn plain_arguments() -> String {
    static PLAIN: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    PLAIN
        .get_or_init(|| {
            let tmp = tempfile::TempDir::new().unwrap();
            let dir = host_fs::canonicalize(tmp.path()).unwrap().join("project");
            std::fs::create_dir(&dir).unwrap();
            let (project, inputs) =
                lay_out(&plain_case(), &dir).expect("the plain project lays out");
            restore(&project, &inputs);
            let build = fsc_args(&FscArgsRequest {
                project: &project,
                environment: inherited_environment(),
                inputs: &inputs,
            })
            .expect("the plain project's build is answered");
            normalised_arguments(&build, &dir)
        })
        .clone()
}

/// How many cases are graded at once: `BORZOI_FSC_NAME_THREADS`, else 4.
fn threads() -> usize {
    let threads = std::env::var("BORZOI_FSC_NAME_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    assert!(threads > 0, "BORZOI_FSC_NAME_THREADS must be at least 1");
    threads
}

/// Grade `cases` on a few threads; the census, and every failure.
fn grade_all(cases: &[Case]) -> (BTreeMap<(Place, Outcome), usize>, Vec<String>) {
    let mut census = BTreeMap::new();
    let mut failures = Vec::new();
    let graded = in_parallel(threads(), cases.len(), |i| grade(&cases[i]));
    for (case, graded) in cases.iter().zip(graded) {
        match graded {
            Ok(outcome) => *census.entry((case.place, outcome)).or_insert(0) += 1,
            Err(failure) => failures.push(failure),
        }
    }
    (census, failures)
}

/// How many cases may be graded at once, shared by every caller that holds
/// it: tests the harness runs side by side take their permits from one
/// budget, so together they keep to it.
struct Budget {
    free: Mutex<usize>,
    freed: std::sync::Condvar,
}

impl Budget {
    fn new(permits: usize) -> Budget {
        assert!(permits > 0);
        Budget {
            free: Mutex::new(permits),
            freed: std::sync::Condvar::new(),
        }
    }

    /// `f`, run under one permit, waiting for one to come free.
    fn hold<R>(&self, f: impl FnOnce() -> R) -> R {
        struct Permit<'a>(&'a Budget);
        impl Drop for Permit<'_> {
            fn drop(&mut self) {
                *self.0.free.lock().unwrap_or_else(|e| e.into_inner()) += 1;
                self.0.freed.notify_one();
            }
        }
        let mut free = self.free.lock().unwrap_or_else(|e| e.into_inner());
        while *free == 0 {
            free = self.freed.wait(free).unwrap_or_else(|e| e.into_inner());
        }
        *free -= 1;
        drop(free);
        let _permit = Permit(self);
        f()
    }
}

/// The budget every grading path in this test binary shares:
/// `BORZOI_FSC_NAME_THREADS` permits.
fn grading_budget() -> &'static Budget {
    static BUDGET: std::sync::OnceLock<Budget> = std::sync::OnceLock::new();
    BUDGET.get_or_init(|| Budget::new(threads()))
}

/// `f` of each index below `count`, on `workers` threads, in index order.
/// What bounds the restores and builds is [`grade`]'s permit, not this.
fn in_parallel<R: Send>(workers: usize, count: usize, f: impl Fn(usize) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let out = Mutex::new(Vec::with_capacity(count));
    std::thread::scope(|scope| {
        for _ in 0..workers.min(count) {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= count {
                        break;
                    }
                    let r = f(i);
                    out.lock().unwrap().push((i, r));
                }
            });
        }
    });
    let mut out = out.into_inner().unwrap();
    out.sort_by_key(|(i, _)| *i);
    assert_eq!(out.len(), count, "a case went ungraded");
    out.into_iter().map(|(_, r)| r).collect()
}

/// Every grade takes a permit of the shared budget, whatever path calls it:
/// with every permit held elsewhere, even a case that needs no build waits.
#[test]
fn every_grade_takes_a_permit() {
    let inexpressible = Case {
        place: Place::Global,
        name: "AssemblyName",
        value: "a;b".into(),
        ..Case::default()
    };
    let holders = threads();
    let (taken, release) = (
        std::sync::Barrier::new(holders + 1),
        std::sync::Barrier::new(holders + 1),
    );
    let graded = std::sync::atomic::AtomicBool::new(false);
    std::thread::scope(|scope| {
        for _ in 0..holders {
            scope.spawn(|| {
                grading_budget().hold(|| {
                    taken.wait();
                    release.wait();
                })
            });
        }
        taken.wait();
        let waiter = scope.spawn(|| {
            let outcome = grade(&inexpressible);
            graded.store(true, Ordering::SeqCst);
            outcome
        });
        std::thread::sleep(std::time::Duration::from_millis(300));
        let early = graded.load(Ordering::SeqCst);
        // Released before any assertion, so a failure cannot leave the
        // holders waiting.
        release.wait();
        let outcome = waiter.join().unwrap();
        assert!(!early, "graded while every permit was held elsewhere");
        assert_eq!(outcome, Ok(Outcome::Inexpressible));
    });
}

/// Two callers sharing a budget run no more at once, between them, than its
/// permits, and each is answered in order.
#[test]
fn callers_sharing_a_budget_keep_to_it() {
    for permits in [1, 3] {
        let budget = Budget::new(permits);
        let (active, most) = (AtomicUsize::new(0), AtomicUsize::new(0));
        let work = |i: usize| {
            let now = active.fetch_add(1, Ordering::SeqCst) + 1;
            most.fetch_max(now, Ordering::SeqCst);
            std::thread::sleep(std::time::Duration::from_millis(2));
            active.fetch_sub(1, Ordering::SeqCst);
            i
        };
        std::thread::scope(|scope| {
            let callers: Vec<_> = (0..2)
                .map(|_| scope.spawn(|| in_parallel(4, 24, |i| budget.hold(|| work(i)))))
                .collect();
            for caller in callers {
                assert_eq!(caller.join().unwrap(), (0..24).collect::<Vec<_>>());
            }
        });
        assert!(most.load(Ordering::SeqCst) <= permits, "{permits}");
    }
}

/// One case per hostile property value of the shared library
/// (`hostile::value`), each at an allowed property and a place by turns: a
/// value a later write puts back is written in the body and reset in
/// `Directory.Build.targets`. Each with the dimension it stands for.
fn hostile_value_cases() -> Vec<(Case, Dimension)> {
    let places = [
        Place::Body,
        Place::DirectoryBuildProps,
        Place::DirectoryBuildTargets,
        Place::Global,
        Place::Environment,
    ];
    value::alphabet()
        .entries()
        .iter()
        .enumerate()
        .map(|(i, entry)| {
            let (name, grammar) = ALLOWED_PROPERTIES[i % ALLOWED_PROPERTIES.len()];
            let plain = plain_value(name, grammar);
            let (place, reset) = match entry.value.write {
                Write::Final => (places[i % places.len()], ""),
                Write::ThenPlain => (Place::BodyThenTargets, plain),
            };
            let case = Case {
                place,
                name,
                value: entry.value.render(plain),
                reset,
                must_commit: None,
                must_decline: false,
                ..Case::default()
            };
            (case, entry.dimension)
        })
        .collect()
}

/// Every [`hostile_value_cases`] case graded, recording what became of each
/// dimension in the census `assembly_name_values`. A value a global or a
/// variable cannot carry (a line break) is written in the body instead, so
/// every value reaches the derivation.
#[test]
#[ignore = "every hostile property value of the shared library: one build-backed case each"]
fn deep_hostile_values() {
    let census = coverage::open(file!(), "assembly_name_values", &[]);
    let mut failures = Vec::new();
    // The plain values beside them: each allowed property at its plain value.
    for case in cases()
        .into_iter()
        .filter(|c| c.must_commit.is_some() && c.place == Place::Body)
    {
        match grade(&case) {
            Ok(outcome) => {
                let outcome = format!("{outcome:?}");
                census.reached(
                    &BTreeSet::new(),
                    outcome.split('(').next().unwrap_or_default(),
                );
            }
            Err(failure) => failures.push(failure),
        }
    }
    for (case, dimension) in hostile_value_cases() {
        let graded = match grade(&case) {
            Ok(Outcome::Inexpressible) => grade(&Case {
                place: Place::Body,
                ..case.clone()
            }),
            other => other,
        };
        match graded {
            Ok(outcome) => {
                let outcome = format!("{outcome:?}");
                let outcome = outcome.split('(').next().unwrap_or_default();
                census.reached(&BTreeSet::from([dimension]), outcome);
            }
            Err(failure) => failures.push(failure),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
         --test fsproj_assembly_name_perturbation_diff deep_hostile_values -- --ignored",
    );
}

/// Grade `work` on a few threads, recording each case's outcome under its
/// dimension (`None` for the harness's own) in the census
/// `assembly_name_environment`, and fail on any failure or on a dimension
/// the census owes and no case reached ([`census_outcome`]).
fn grade_environment_census(work: &[(Case, Option<Dimension>)]) {
    let census = coverage::open(
        file!(),
        "assembly_name_environment",
        &[(
            Dimension::NonUtf8,
            "the derivation takes the environment as UTF-8 text, as its caller reads it",
        )],
    );
    let graded = in_parallel(threads(), work.len(), |i| grade(&work[i].0));
    let mut failures = Vec::new();
    for (graded, (case, dimension)) in graded.into_iter().zip(work) {
        match census_outcome(case, graded) {
            Ok(outcome) => census.reached(&dimension.iter().copied().collect(), &outcome),
            Err(failure) => failures.push(failure),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
         --test fsproj_assembly_name_perturbation_diff hostile_environments",
    );
}

/// What the census records of a graded environment case: its outcome's name,
/// or a failure. An environment the harness could not lay out never reached
/// the derivation, so it is a failure, not a reach: every hostile
/// environment can be handed to an evaluation.
fn census_outcome(case: &Case, graded: Result<Outcome, String>) -> Result<String, String> {
    match graded? {
        Outcome::Inexpressible => Err(format!(
            "{}: never reached the derivation (inexpressible)",
            case.label()
        )),
        outcome => Ok(format!("{outcome:?}")
            .split('(')
            .next()
            .unwrap_or_default()
            .to_string()),
    }
}

/// An inexpressible environment is a failure of the census, not a reach.
#[test]
fn an_inexpressible_environment_is_no_reach() {
    let case = Case::variables(&[("Configuration", "")]);
    assert!(census_outcome(&case, Ok(Outcome::Inexpressible)).is_err());
    assert_eq!(
        census_outcome(&case, Ok(Outcome::Declined("Value".into()))),
        Ok("Declined".to_string())
    );
    assert!(census_outcome(&case, Err("x".into())).is_err());
}

/// Only names on the oracle's reviewed list reach a real restore or build:
/// every other variable a case sets (an SDK import selector such as
/// `LanguageTargets`, a hostile environment's) is handed to the evaluation
/// alone, where a commit under it fails the case.
#[test]
fn variables_off_the_oracle_list_never_reach_the_build() {
    let selector = Case::variables(&[("LanguageTargets", "/nonexistent/borzoi/Evil.targets")]);
    let all: Vec<Case> = cases()
        .into_iter()
        .chain(
            hostile_environment_cases()
                .into_iter()
                .map(|(case, _)| case),
        )
        .chain([selector.clone()])
        .filter(|case| case.place == Place::Variables)
        .collect();
    for case in &all {
        let Some((inputs, rest)) = split_variables(case) else {
            continue;
        };
        for (name, _) in inputs.env_vars(inherited_environment()) {
            assert!(
                INPUT_NAMES.iter().any(|n| n.eq_ignore_ascii_case(&name)),
                "{}: {name} reaches the build",
                case.label()
            );
        }
        assert_eq!(
            inputs.env_vars(inherited_environment()).len() + rest.len(),
            case.variables.len(),
            "{}",
            case.label()
        );
    }
    assert_eq!(
        unsettable(&selector),
        vec![(
            "LanguageTargets".to_string(),
            "/nonexistent/borzoi/Evil.targets".to_string()
        )]
    );
}

/// A commit under variables none of which is an allowed property is held to
/// the plain project's arguments, whatever list the derivation keeps them
/// on: a name it might admit by mistake (`WarningLevel`), one it admits as
/// inert (`LANG`), and two together. A case setting an allowed property, in
/// any case, may move them.
#[test]
fn variables_that_are_no_allowed_property_are_held_to_the_plain_arguments() {
    for variables in [
        &[("WarningLevel", "5")][..],
        &[("LANG", "Evil")],
        &[("LANG", "Evil"), ("WarningLevel", "5")],
    ] {
        assert!(
            held_to_plain_arguments(&Case::variables(variables)),
            "{variables:?}"
        );
    }
    for variables in [
        &[("AssemblyName", "Evil")][..],
        &[("LANG", "Evil"), ("assemblyname", "Evil")],
    ] {
        assert!(
            !held_to_plain_arguments(&Case::variables(variables)),
            "{variables:?}"
        );
    }
}

/// The build sees each variable the derivation admits as inert by name
/// exactly as a case sets it (as MSBuild reads its value back: an
/// environment variable's value is taken as escaped text, as a property
/// written in a project is, and decoded by the crate's model of MSBuild's
/// unescaping): a commit under one is graded under the value
/// the evaluation was handed, not one a launcher put in its place. Each
/// name at each value, set together, but for the locale's (`LANG`, `LC_*`):
/// .NET takes their values for a culture and stops when it cannot make one,
/// so each is read alone, at a value that names none.
#[test]
fn the_build_sees_each_variable_as_set() {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(dir.join("Probe.proj"), "<Project/>").unwrap();
    let locale = |name: &str| name == "LANG" || name.starts_with("LC_");
    // `VALUES`, and an escape that decodes outside ASCII.
    let mut probes: Vec<(Vec<&str>, &str)> = VALUES
        .iter()
        .chain(&["x%FFy%41"])
        .map(|value| {
            let names = ALLOWED_ENVIRONMENT
                .iter()
                .copied()
                .filter(|name| !locale(name))
                .collect();
            (names, *value)
        })
        .collect();
    probes.extend(
        ALLOWED_ENVIRONMENT
            .iter()
            .filter(|name| locale(name))
            .map(|name| (vec![*name], "Evil")),
    );
    let mut failures = Vec::new();
    for (names, value) in &probes {
        let mut inputs = BuildInputs::new();
        for name in names {
            inputs = inputs.env(name, value).unwrap();
        }
        let mut cmd = msbuild_command(&dir, inherited_environment(), &inputs);
        cmd.arg("-nologo");
        for name in names {
            cmd.arg(format!("-getProperty:{name}"));
        }
        cmd.arg("Probe.proj");
        let out = BoundedCommand::new(cmd)
            .timeout(std::time::Duration::from_secs(300))
            .run_ok("reading the build's view of the environment");
        let stdout = String::from_utf8_lossy(&out.stdout);
        // One property is printed bare; several, as JSON.
        let seen = |name: &str| -> Option<String> {
            if names.len() == 1 {
                return Some(stdout.trim_end_matches(['\r', '\n']).to_string());
            }
            let json: serde_json::Value =
                serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("{e}: {stdout}"));
            json["Properties"][name].as_str().map(str::to_string)
        };
        for name in names {
            let seen = seen(name);
            if seen.as_deref() != Some(unescape(value).as_str()) {
                failures.push(format!("{name} = {value:?}: the build saw {seen:?}"));
            }
        }
    }
    assert!(
        ALLOWED_ENVIRONMENT
            .iter()
            .all(|name| probes.iter().any(|(names, _)| names.contains(name))),
        "a name went unread"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Every test that compares with `fsc_args` starts its own builds as
/// `fsc_args` does, through `msbuild_command`: a `dotnet` launched otherwise
/// (a launcher on `PATH`) may hand MSBuild other variables, and the two
/// would be different builds.
#[test]
fn builds_compared_with_the_oracle_start_as_it_does() {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut checked = 0;
    for entry in host_fs::read_dir(&tests).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let text = host_fs::read_to_string(&path).unwrap();
        if !text.contains("fsc_args(") {
            continue;
        }
        checked += 1;
        let launch = ["Command::new(\"dotnet", "\")"].concat();
        assert!(
            !text.contains(&launch),
            "{} compares with fsc_args but launches `dotnet` itself",
            path.display()
        );
    }
    assert!(checked >= 2, "only {checked} files compare with fsc_args");
}

/// Whatever `PATH` the developer's shell holds, the one the grading's builds
/// run under is exactly its plain entries, in order, or none at all when it
/// has none, and so one the derivation admits: every list of up to three
/// entries drawn from each kind of entry (two plain directories, relative,
/// holding an escape, holding a control character, empty), exhaustively.
#[test]
fn the_grading_s_path_is_always_admitted() {
    use borzoi_msbuild::fsc::ToolchainValue;
    // Each kind of entry, and whether the cut keeps it.
    let labelled = [
        ("/usr/bin", true),
        ("/opt/bin", true),
        ("bin", false),
        (".", false),
        ("/opt/SDK%20Tools/bin", false),
        ("/a\tb", false),
        ("", false),
    ];
    let kinds: Vec<&str> = labelled.iter().map(|(kind, _)| *kind).collect();
    let kept = |kind: &str| labelled.iter().any(|(k, keep)| *k == kind && *keep);
    let mut lists: Vec<Vec<&str>> = vec![vec![]];
    for _ in 0..3 {
        let longer: Vec<Vec<&str>> = lists
            .iter()
            .flat_map(|list| {
                kinds.iter().map(move |kind| {
                    let mut list = list.clone();
                    list.push(kind);
                    list
                })
            })
            .collect();
        lists.extend(longer);
    }
    lists.sort();
    lists.dedup();
    for list in &lists {
        let path = list.join(":");
        let plain: Vec<&str> = list.iter().copied().filter(|e| kept(e)).collect();
        let expected = (!plain.is_empty()).then(|| plain.join(":"));
        let graded = graded_path(&path);
        assert_eq!(graded, expected, "{path:?}");
        if let Some(graded) = graded {
            assert!(
                ToolchainValue::SearchPath.admits(&graded),
                "{path:?} graded as {graded:?}, which the derivation declines"
            );
        }
    }
}

/// Whatever value the developer's shell gives a variable the grading's builds
/// inherit, the grading either runs under it as the build does or refuses to
/// run, naming the variable and never its value; and it refuses exactly when
/// the derivation declines the value. Every name of `BUILD_ENVIRONMENT_NAMES`
/// at every kind of value (each shape's good value, empty, relative, a feed's
/// URL, holding an escape, holding a control character, a word no switch is),
/// exhaustively; and some value of each name is graded under.
#[test]
fn the_grading_s_environment_is_always_admitted() {
    let values = [
        "1",
        "true",
        "/usr/local",
        "/usr/bin:/bin",
        "/feed;/other",
        "",
        "relative",
        "https://private.example.org/v3/index.json",
        "/opt/SDK%20Tools",
        "/a\tb",
        "yes",
    ];
    let user_extensions = "/home/u/.local/share/Microsoft/MSBuild";
    for name in BUILD_ENVIRONMENT_NAMES {
        let mut graded_one = false;
        for value in values {
            // The refusal comes from the build's environment alone, before
            // any build, restore or probe runs: whatever it admits, the
            // evaluation admits too.
            let graded =
                grading_build_environment([(name.to_string(), value.to_string())]).map(|build| {
                    let environment = evaluation_environment(&build, user_extensions)
                        .unwrap_or_else(|refusal| {
                            panic!("{name}={value:?} passes the build's check: {refusal}")
                        });
                    (build, environment)
                });
            // `PATH` is cut to what the derivation admits, never refused.
            assert!(
                *name != "PATH" || graded.is_ok(),
                "PATH={value:?} is refused: {graded:?}"
            );
            match graded {
                Ok((build, environment)) => {
                    assert_eq!(
                        borzoi_msbuild::fsc::environment_decline(&environment),
                        None,
                        "{name}={value:?} is graded under, though the derivation declines it"
                    );
                    // The build runs under the value as it was inherited, but
                    // `PATH` cut to its plain entries.
                    let kept: Vec<(&str, &str)> = build.vars().collect();
                    let cut = graded_path(value);
                    let expected: Vec<(&str, &str)> = match *name {
                        "PATH" => cut
                            .as_deref()
                            .map(|path| (*name, path))
                            .into_iter()
                            .collect(),
                        _ => vec![(*name, value)],
                    };
                    assert_eq!(kept, expected, "{name}={value:?}");
                    // The evaluation sees what the build sees.
                    let mut seen: HashMap<String, String> = build
                        .vars()
                        .map(|(n, v)| (n.to_string(), v.to_string()))
                        .collect();
                    seen.insert(
                        "MSBuildUserExtensionsPath".to_string(),
                        user_extensions.to_string(),
                    );
                    assert_eq!(environment, seen, "{name}={value:?}");
                    graded_one |= environment.contains_key(*name);
                }
                Err(refusal) => {
                    assert!(refusal.contains(name), "{refusal}");
                    assert!(
                        value.len() < 4 || !refusal.contains(value),
                        "the refusal shows {name}'s value: {refusal}"
                    );
                    let environment = HashMap::from([(name.to_string(), value.to_string())]);
                    assert!(
                        borzoi_msbuild::fsc::environment_decline(&environment).is_some(),
                        "{name}={value:?} is refused, though the derivation admits it"
                    );
                }
            }
        }
        assert!(graded_one, "no value of {name} is ever graded under");
    }
    // The evaluation's own variable, which the probe answers, is held to its
    // shape too.
    let build = grading_build_environment([]).unwrap();
    for user_extensions in ["", "relative", "/opt/SDK%20Tools"] {
        let refused = evaluation_environment(&build, user_extensions).unwrap_err();
        assert!(refused.contains("MSBuildUserExtensionsPath"), "{refused}");
    }
}

/// A toolchain variable is held fixed: none is an input the oracle can vary,
/// in any case.
#[test]
fn no_oracle_input_is_a_toolchain_variable() {
    for name in INPUT_NAMES {
        assert!(
            !borzoi_msbuild::fsc::TOOLCHAIN_VARIABLES
                .iter()
                .any(|(toolchain, _)| toolchain.eq_ignore_ascii_case(name)),
            "{name} is a toolchain variable, and an oracle input"
        );
        assert!(
            !HELD_FIXED
                .iter()
                .any(|(held, _)| held.eq_ignore_ascii_case(name)),
            "{name} is held fixed, and an oracle input"
        );
    }
}

/// Every variable the grading's own builds run under is one the derivation
/// admits, so no case declines for the grading's environment alone.
#[test]
fn the_grading_environment_is_admitted() {
    for name in BUILD_ENVIRONMENT_NAMES {
        assert!(
            toolchain_variable(name) || ALLOWED_ENVIRONMENT.contains(name),
            "the grading's builds run under {name}, which the derivation does not admit"
        );
    }
    // And as its values stand: every case's evaluation is handed these, and
    // the grading refuses to run under any the derivation declines.
    grading_environment();
}

/// The name `BORZOI_FSC_NAME_ONLY` selects, if any.
fn only_name() -> Option<String> {
    std::env::var("BORZOI_FSC_NAME_ONLY").ok()
}

/// Every case a run that records an SDK as graded must pass: [`cases`] and
/// every hostile environment.
fn certification_cases() -> Vec<Case> {
    cases()
        .into_iter()
        .chain(
            hostile_environment_cases()
                .into_iter()
                .map(|(case, _)| case),
        )
        .collect()
}

/// A run that records an SDK grades every hostile environment, and every
/// case a focused run can select.
#[test]
fn the_certifying_sweep_grades_every_hostile_environment() {
    let labels: BTreeSet<String> = certification_cases().iter().map(Case::label).collect();
    for (case, _) in hostile_environment_cases() {
        assert!(labels.contains(&case.label()), "{}", case.label());
    }
    assert_eq!(
        certification_cases().len(),
        cases().len() + hostile_environment_cases().len(),
        "a hostile environment is in the sweep twice"
    );
}

/// No hostile name renders the plain variable's name, which would be no
/// draw of its dimension.
#[test]
fn every_hostile_name_is_a_draw() {
    for (case, dimension) in hostile_environment_cases() {
        for (name, _) in &case.variables {
            assert_ne!(name, PLAIN_VARIABLE, "{dimension:?}");
        }
    }
}

/// `cases`, but for those `BORZOI_FSC_NAME_ONLY` (a name) leaves out
/// ([`only_named`]).
fn only(cases: Vec<Case>) -> Vec<Case> {
    only_named(cases, only_name().as_deref())
        .unwrap_or_else(|e| panic!("BORZOI_FSC_NAME_ONLY: {e}"))
}

/// `cases` when no name is given. Given `name`, those that set it (as the
/// case's name, or one of its variables'). A focused run selects from
/// [`certification_cases`], so it reaches a hostile environment's variable
/// too; the census tests leave such a run to this selection, as a census is
/// checked only whole. Selecting nothing is a mistake, so it is an error
/// rather than a run that grades nothing.
fn only_named(cases: Vec<Case>, name: Option<&str>) -> Result<Vec<Case>, String> {
    let Some(name) = name else {
        return Ok(cases);
    };
    let kept: Vec<Case> = cases
        .into_iter()
        .filter(|c| c.name == name || c.variables.iter().any(|(n, _)| n == name))
        .collect();
    if kept.is_empty() {
        return Err(format!("no case sets {name:?}"));
    }
    Ok(kept)
}

/// Selecting a variable's name keeps the cases that set it, a hostile
/// environment's variable among them, and selecting a name no case sets is
/// an error.
#[test]
fn a_variable_is_selected_by_its_name() {
    for name in ["LANG", "FscToolExe"] {
        let pool = certification_cases();
        let setting = pool
            .iter()
            .filter(|c| c.variables.iter().any(|(n, _)| n == name))
            .count();
        let kept = only_named(pool, Some(name)).unwrap();
        assert_eq!(kept.len(), setting, "{name}: selecting added cases");
        assert!(!kept.is_empty(), "{name}");
        assert!(
            kept.iter()
                .all(|c| c.variables.iter().any(|(n, _)| n == name)),
            "{name}"
        );
    }
    assert!(only_named(cases(), Some("BORZOI_NO_CASE_SETS_THIS")).is_err());
}

/// Whether a census test is to stand aside: a focused run
/// (`BORZOI_FSC_NAME_ONLY`) grades its selection through
/// [`committed_names_survive_perturbation`], and a census is checked only
/// whole ([`census_stance`]).
fn census_stands_aside() -> bool {
    let updating = std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some();
    let aside = census_stance(only_name().is_some(), updating).unwrap_or_else(|e| panic!("{e}"));
    if aside {
        eprintln!(
            "BORZOI_FSC_NAME_ONLY is set: committed_names_survive_perturbation grades the \
             selected cases, and the census needs an unfiltered run"
        );
    }
    aside
}

/// Whether a census stands aside, given whether the run is `focused` and
/// whether it is `updating` manifests: a focused run that is asked to
/// regenerate a census is an error, since it would pass having written
/// nothing.
fn census_stance(focused: bool, updating: bool) -> Result<bool, String> {
    match (focused, updating) {
        (true, true) => Err(
            "BORZOI_FSC_NAME_ONLY and BORZOI_UPDATE_MANIFESTS are both set: \
                             a focused run checks no census, so it cannot regenerate one"
                .to_string(),
        ),
        (focused, _) => Ok(focused),
    }
}

/// A focused run asked to regenerate a census fails rather than writes
/// nothing.
#[test]
fn a_focused_run_cannot_regenerate_a_census() {
    assert_eq!(census_stance(false, false), Ok(false));
    assert_eq!(census_stance(false, true), Ok(false));
    assert_eq!(census_stance(true, false), Ok(true));
    assert!(census_stance(true, true).is_err());
}

/// A case whose variables all reach the evaluation alone restores nothing
/// of its own: two such grades run one restore between them at most (the
/// shared fixture's, if no other test made it first), and the second runs
/// none. A case with a variable the build takes restores its own.
#[test]
fn evaluator_only_cases_share_one_restore() {
    let only_evaluated = [
        Case::variables(&[("BorzoiVar.x", "Evil")]),
        Case::variables(&[("BorzoiVar:y", "Evil")]),
    ];
    for case in &only_evaluated {
        assert!(evaluator_only(case), "{}", case.label());
    }
    assert!(!evaluator_only(&Case::variables(&[("LANG", "Evil")])));
    assert!(!evaluator_only(&Case::variables(&[
        ("LANG", "Evil"),
        ("BorzoiVar.x", "Evil")
    ])));
    let before = RESTORES.with(|n| n.get());
    assert!(matches!(
        grade(&only_evaluated[0]),
        Ok(Outcome::Declined(_))
    ));
    let between = RESTORES.with(|n| n.get());
    assert!(matches!(
        grade(&only_evaluated[1]),
        Ok(Outcome::Declined(_))
    ));
    let after = RESTORES.with(|n| n.get());
    assert!(between - before <= 1, "{} restores", between - before);
    assert_eq!(after, between, "the second evaluator-only grade restored");
}

fn run(cases: &[Case]) {
    let (census, failures) = grade_all(cases);
    assert_eq!(
        census.values().sum::<usize>() + failures.len(),
        cases.len(),
        "a case went ungraded"
    );
    eprintln!("{} cases:", cases.len());
    for ((place, outcome), count) in &census {
        eprintln!("  {place:?} {outcome:?}: {count}");
    }
    assert!(
        failures.is_empty(),
        "{} of {} cases failed:\n{}",
        failures.len(),
        cases.len(),
        failures.join("\n")
    );
}

/// Every name the derivation admits as a global or a variable is one the
/// oracle can set, so every such place is graded.
#[test]
fn every_admitted_input_can_be_set() {
    for name in ALLOWED_PROPERTIES
        .iter()
        .map(|(name, _)| *name)
        .chain(ALLOWED_ENVIRONMENT.iter().copied())
    {
        assert!(
            INPUT_NAMES.iter().any(|n| n.eq_ignore_ascii_case(name)),
            "{name} is admitted but the oracle cannot set it"
        );
    }
}

#[test]
fn committed_names_survive_perturbation() {
    let seed = std::env::var("BORZOI_FSC_NAME_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x5eed_f5c0);
    let sample: usize = std::env::var("BORZOI_FSC_NAME_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(40);
    eprintln!(
        "seed {seed:#x}, {sample} sampled cases (BORZOI_FSC_NAME_SEED, BORZOI_FSC_NAME_CASES)"
    );
    run(&chosen(only_name().as_deref(), seed, sample));
}

/// The cases a default run grades. Focused on `name`, every case that sets
/// it, hostile environments' too, unsampled; otherwise the must-commit and
/// must-decline points of [`cases`] and `sample` of the rest, drawn by
/// `seed`.
fn chosen(name: Option<&str>, seed: u64, sample: usize) -> Vec<Case> {
    if name.is_some() {
        return only_named(certification_cases(), name)
            .unwrap_or_else(|e| panic!("BORZOI_FSC_NAME_ONLY: {e}"));
    }
    let mut rng = SplitMix64(seed);
    let (mut chosen, mut rest): (Vec<Case>, Vec<Case>) = cases()
        .into_iter()
        .partition(|c| c.must_commit.is_some() || c.must_decline);
    for _ in 0..sample.min(rest.len()) {
        let i = rng.below(rest.len());
        chosen.push(rest.swap_remove(i));
    }
    chosen
}

/// A focused run grades every case of its name, whatever the sample size.
#[test]
fn a_focused_run_grades_its_whole_selection() {
    for name in ["FscToolExe", "LANG"] {
        let all = only_named(certification_cases(), Some(name)).unwrap();
        for sample in [0, 1, 40] {
            let picked = chosen(Some(name), 1, sample);
            assert_eq!(picked.len(), all.len(), "{name} at {sample}");
        }
    }
}

/// Every [`hostile_environment_cases`] case, in every run, beside
/// [`plain_variable_case`], held to the census `assembly_name_environment`:
/// one restore each, most declining without a build.
#[test]
fn hostile_environments() {
    if census_stands_aside() {
        return;
    }
    let work: Vec<(Case, Option<Dimension>)> = hostile_environment_cases()
        .into_iter()
        .map(|(case, dimension)| (case, Some(dimension)))
        .chain([(plain_variable_case(), None)])
        .collect();
    grade_environment_census(&work);
}

#[test]
#[ignore = "every perturbation: about two thousand cases, most declined without a build"]
fn deep_every_perturbation() {
    let all = only(certification_cases());
    run(&all);
    // A whole, passing run grades the devshell's SDK: record it.
    if std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some()
        && all.len() == certification_cases().len()
    {
        let (sdk, manifests) = devshell_sdk();
        // The SDK recorded is the one whose MSBuild built every agreed case.
        let built_by = BUILT_BY.lock().unwrap().clone();
        assert!(
            !built_by.is_empty()
                && built_by
                    .iter()
                    .all(|dir| dir.file_name().is_some_and(|name| name == sdk.as_str())),
            "the sweep graded the SDK {sdk} by its evaluation, but the builds ran under {built_by:?}"
        );
        let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/fsc_verified_sdks.txt");
        let header: String = host_fs::read_to_string(&file)
            .unwrap()
            .lines()
            .take_while(|line| line.starts_with('#'))
            .map(|line| format!("{line}\n"))
            .collect();
        let manifest_lines: String = manifests
            .iter()
            .map(|manifest| format!("{sdk} manifest {manifest}\n"))
            .collect();
        std::fs::write(&file, format!("{header}{sdk}\n{manifest_lines}")).unwrap();
    }
}

/// `from`'s tree copied to `to`, links followed.
fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in host_fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let (source, target) = (entry.path(), to.join(entry.file_name()));
        if host_fs::metadata(&source).unwrap().is_dir() {
            copy_tree(&source, &target);
        } else {
            std::fs::write(&target, host_fs::read(&source).unwrap()).unwrap();
        }
    }
}

/// A merged .NET install can keep `sdk-manifests` in another tree than its
/// SDKs. Its manifests are still the install's, not user-local ones: the
/// plain project commits under an install whose `sdk-manifests` is a copy
/// and whose every other entry links into the devshell's.
#[cfg(unix)]
#[test]
fn a_split_install_s_manifests_are_its_own() {
    let tmp = tempfile::TempDir::new().unwrap();
    let base = host_fs::canonicalize(tmp.path()).unwrap();
    let real = common::dotnet_root_from_env();
    let split = base.join("dotnet");
    std::fs::create_dir(&split).unwrap();
    for entry in host_fs::read_dir(&real).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == "sdk-manifests" {
            copy_tree(&entry.path(), &split.join("sdk-manifests"));
        } else {
            std::os::unix::fs::symlink(entry.path(), split.join(entry.file_name())).unwrap();
        }
    }
    let dir = base.join("project");
    std::fs::create_dir(&dir).unwrap();
    let (project, inputs) = lay_out(&plain_case(), &dir).expect("the plain project lays out");
    restore(&project, &inputs);
    assert_eq!(
        ours_under(&project, &inputs, &[], &split),
        CompiledAssemblyName::Known("Demo".into())
    );
}

/// An F# project on the Razor SDK imports files the register holds unreached
/// ([`Gate::NotImported`]), and declines however the resolver spells the .NET
/// install: as the environment names it, canonically, and through a link of
/// the test's own. Under each spelling the plain project commits, so the
/// declines are the gate's.
#[test]
fn not_imported_files_decline_however_the_install_is_spelled() {
    let tmp = tempfile::TempDir::new().unwrap();
    let base = host_fs::canonicalize(tmp.path()).unwrap();
    let dotnet_root = common::dotnet_root_from_env();
    let link = base.join("dotnet-link");
    std::os::unix::fs::symlink(&dotnet_root, &link).unwrap();
    let roots = [
        dotnet_root.clone(),
        host_fs::canonicalize(&dotnet_root).unwrap(),
        link,
    ];
    let mut failures = Vec::new();
    for (sdk, must) in [
        ("Microsoft.NET.Sdk", None),
        (
            "Microsoft.NET.Sdk.Razor",
            Some("Sdks/Microsoft.NET.Sdk.Razor/"),
        ),
    ] {
        let dir = base.join(sdk);
        std::fs::create_dir(&dir).unwrap();
        let (project, inputs) = lay_out(&plain_case(), &dir).expect("the plain project lays out");
        let text = host_fs::read_to_string(&project).unwrap();
        std::fs::write(
            &project,
            text.replace("Sdk=\"Microsoft.NET.Sdk\"", &format!("Sdk=\"{sdk}\"")),
        )
        .unwrap();
        restore(&project, &inputs);
        for root in &roots {
            let verdict = ours_under(&project, &inputs, &[], root);
            let right = match (must, &verdict) {
                (None, CompiledAssemblyName::Known(name)) => name == "Demo",
                (Some(prefix), CompiledAssemblyName::Unknown(NameDecline::NotImported(file))) => {
                    file.starts_with(prefix)
                }
                _ => false,
            };
            if !right {
                failures.push(format!("{sdk} under {}: {verdict:?}", root.display()));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The SDK the devshell's `dotnet` resolves for a plain project, the one the
/// sweep grades, and the workload manifest files the project loads with it.
fn devshell_sdk() -> (String, std::collections::BTreeSet<String>) {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = host_fs::canonicalize(tmp.path()).unwrap();
    let (project, _) = lay_out(&plain_case(), &dir).expect("the plain project lays out");
    let globals: HashMap<String, String> = HashMap::new();
    let environment = grading_environment();
    let parsed = assembly_name::evaluate(
        &project,
        &globals,
        &environment,
        &common::dotnet_root_from_env(),
    )
    .expect("the plain project evaluates");
    let sdk = resolved_sdk_version(&parsed).expect("the plain project resolves an SDK");
    (sdk, parsed.workload_manifest_files)
}

/// The derivation commits only for a graded SDK, so the devshell's must be on
/// the verified list: a new one fails here until a whole sweep has graded it.
#[test]
fn the_devshell_sdk_is_graded() {
    let (sdk, manifests) = devshell_sdk();
    let ungraded: Vec<&String> = manifests
        .iter()
        .filter(|manifest| !verified_manifests(&sdk).any(|graded| graded == manifest.as_str()))
        .collect();
    assert!(
        verified_sdks().any(|graded| graded == sdk) && ungraded.is_empty(),
        "the devshell's SDK {sdk}, or its workload manifests {ungraded:?}, are not on \
         fsc_verified_sdks.txt; grade them and record them with\n  \
         BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
         --test fsproj_assembly_name_perturbation_diff deep_every_perturbation -- --ignored"
    );
}
