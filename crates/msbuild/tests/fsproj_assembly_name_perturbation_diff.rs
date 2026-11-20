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
    CompiledAssemblyName, FSC_OPTIONS, FSC_PARAMETERS, Feed, Grammar, NameDecline,
    RESTORE_ITEM_TYPES, RESTORE_METADATA, RESTORE_PROPERTIES, RESTORE_PROPERTY_PREFIX,
    VariableClass, classify_variable, environment_reads, resolved_sdk_version, toolchain_variable,
    verified_manifests, verified_sdks,
};
use borzoi_msbuild::observed::host_fs;
use borzoi_oracle_harness::BoundedCommand;
use borzoi_oracle_harness::hostile::value::{self, Write};
use borzoi_oracle_harness::hostile::{Dimension, coverage};
use borzoi_oracle_harness::hostile::{env as hostile_env, name as hostile_name};
use borzoi_oracle_harness::msbuild_oracle::{
    BUILD_ENVIRONMENT_NAMES, BuildInputs, FscArgsDecline, FscArgsRequest, INPUT_NAMES, InputError,
    build_environment, fsc_args,
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
    /// (through [`BuildInputs::env`] for a name on the oracle's list, else
    /// [`BuildInputs::unlisted_env`]) and handed to the evaluation. One the
    /// oracle refuses, or a second spelling of a name already set, is handed
    /// to the evaluation alone ([`split_variables`]), and a commit under it
    /// is a failure unless it is the toolchain's, which the grading holds
    /// fixed.
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
    /// For [`Place::Variables`], the variables, by name and value.
    variables: Vec<(String, String)>,
    /// The variables are on no list, so inert by construction: fsc must be
    /// handed exactly what the plain project's build hands it.
    inert: bool,
    /// Graded in every run, not only when the sample draws it.
    always: bool,
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
            variables: Vec::new(),
            inert: false,
            always: false,
        }
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

/// The SDKs whose environment reads the cases draw listed names from.
fn graded_reads() -> Vec<&'static borzoi_msbuild::fsc::EnvironmentReads> {
    verified_sdks().filter_map(environment_reads).collect()
}

/// How a variable named `name` classifies under every verified SDK: one
/// class when they agree, else `None`.
fn class_of(name: &str) -> Option<VariableClass> {
    let classes: BTreeSet<String> = verified_sdks()
        .filter_map(|sdk| classify_variable(sdk, name))
        .map(|c| format!("{c:?}"))
        .collect();
    (classes.len() == 1).then(|| {
        classify_variable(verified_sdks().next().expect("a verified SDK"), name)
            .expect("classified")
    })
}

/// `count` of `names`, spread evenly over them.
fn spread<'a>(names: impl IntoIterator<Item = &'a String>, count: usize) -> Vec<String> {
    let names: Vec<&String> = names.into_iter().collect();
    if names.is_empty() {
        return Vec::new();
    }
    let step = (names.len() / count.max(1)).max(1);
    names
        .into_iter()
        .step_by(step)
        .take(count)
        .cloned()
        .collect()
}

/// A random name for a variable, an ASCII letter or `_` then letters, digits
/// and `_`, which [`classify_variable`] finds on no list.
fn random_inert_name(rng: &mut SplitMix64) -> String {
    const FIRST: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_";
    const REST: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_";
    loop {
        let len = 1 + rng.below(16);
        let mut name = String::new();
        name.push(FIRST[rng.below(FIRST.len())] as char);
        for _ in 1..len {
            name.push(REST[rng.below(REST.len())] as char);
        }
        if class_of(&name) == Some(VariableClass::Inert) {
            return name;
        }
    }
}

/// The environment's cases:
///
/// - every property an `Fsc` parameter is fed from that is not an allowed
///   one, set as a variable to a line break and an output switch: the SDK's
///   files read each, so the derivation must decline it or the build agree
///   (graded in every run, and chosen from the register alone, not by the
///   derivation's lists: an SDK-read list missing one commits a name fsc
///   does not compile to);
/// - `listed` names of each list, spread over it, by turns at each value;
/// - `inert` names on no list, random, each must commit and leave fsc's
///   arguments as they were.
fn environment_cases(listed: usize, inert: usize) -> Vec<Case> {
    let mut cases = Vec::new();
    let fed: BTreeSet<&str> = FSC_PARAMETERS
        .iter()
        .filter_map(|p| match p.feed {
            Feed::Properties(names) => Some(names.iter().copied()),
            _ => None,
        })
        .flatten()
        .collect();
    for name in fed {
        if !ALLOWED_PROPERTIES
            .iter()
            .any(|(allowed, _)| allowed.eq_ignore_ascii_case(name))
        {
            cases.push(Case {
                always: true,
                ..Case::variables(&[(name, "x\n--out:obj/Evil.dll")])
            });
        }
    }
    let reads = graded_reads();
    let properties: BTreeSet<&String> = reads.iter().flat_map(|r| &r.properties).collect();
    let variables: BTreeSet<&String> = reads.iter().flat_map(|r| &r.variables).collect();
    for (i, name) in spread(properties, listed)
        .into_iter()
        .chain(spread(variables, listed))
        .enumerate()
    {
        cases.push(Case::variables(&[(
            &name.to_ascii_uppercase(),
            env_value(i),
        )]));
    }
    let mut rng = SplitMix64(0x1064_e7a1);
    for i in 0..inert {
        let name = random_inert_name(&mut rng);
        cases.push(Case {
            must_commit: Some("Demo".into()),
            inert: true,
            ..Case::variables(&[(&name, env_value(i))])
        });
    }
    cases
}

/// One case per entry of the hostile environment alphabet (`hostile::env`),
/// its variables set together, and one per entry of the hostile file-name
/// alphabet (`hostile::name`) rendered as a variable's name: those
/// [`classify_variable`] finds on no list must commit and leave fsc's
/// arguments as they were. Each with the dimension it stands for. A name the
/// environment cannot carry (empty, or holding `=` or NUL) or that is not
/// UTF-8 has no case.
fn hostile_environment_cases() -> Vec<(Case, Dimension)> {
    let mut out = Vec::new();
    for entry in hostile_env::alphabet().entries() {
        let mut case = Case::variables(entry.value);
        let inert = entry
            .value
            .iter()
            .all(|(name, _)| class_of(name) == Some(VariableClass::Inert));
        if inert {
            case.must_commit = Some("Demo".into());
            case.inert = true;
        }
        out.push((case, entry.dimension));
    }
    for (i, entry) in hostile_name::alphabet().entries().iter().enumerate() {
        let rendered = entry.value.render("BorzoiVar", "");
        let Some(name) = rendered.to_str() else {
            continue;
        };
        if name.is_empty() || name.contains(['=', '\0']) {
            continue;
        }
        let mut case = Case::variables(&[(name, env_value(i))]);
        if class_of(name) == Some(VariableClass::Inert) {
            case.must_commit = Some("Demo".into());
            case.inert = true;
        }
        out.push((case, entry.dimension));
    }
    out
}

/// Every case, the must-commit points first.
fn cases() -> Vec<Case> {
    let mut cases = vec![Case {
        place: Place::Body,
        name: "TargetFramework",
        value: "net10.0".into(),
        reset: "",
        must_commit: Some("Demo".into()),
        must_decline: false,
        ..Case::default()
    }];
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
    // The environment: graded-inert names at every value, listed names, and
    // names on no list.
    for name in ALLOWED_ENVIRONMENT {
        for value in VALUES {
            rest.push(Case::variables(&[(name, value)]));
        }
    }
    cases.extend(
        environment_cases(12, 6)
            .into_iter()
            .filter(|c| c.always || c.must_commit.is_some()),
    );
    rest.extend(
        environment_cases(12, 6)
            .into_iter()
            .filter(|c| !(c.always || c.must_commit.is_some())),
    );
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
    std::fs::write(dir.join("A.fs"), "module A\nlet x = 1\n").unwrap();
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
        let mut cmd = std::process::Command::new("dotnet");
        cmd.current_dir(dir)
            .args(["msbuild", "-nodeReuse:false", "-restore", "-t:Build"])
            .env_clear()
            .envs(build_environment());
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

/// Restore the project at `project` in place, under `inputs`, as the build
/// would; a failed restore leaves the evaluation unrestored, which the
/// derivation declines.
fn restore(project: &Path, inputs: &BuildInputs) {
    let mut cmd = std::process::Command::new("dotnet");
    cmd.current_dir(project.parent().unwrap())
        .args(["msbuild", "-nodeReuse:false", "-t:Restore"]);
    for (name, value) in inputs.globals() {
        cmd.arg(format!("-p:{name}={value}"));
    }
    cmd.arg(project).env_clear().envs(build_environment());
    cmd.envs(inputs.env_vars());
    BoundedCommand::new(cmd)
        .timeout(std::time::Duration::from_secs(900))
        .run()
        .unwrap_or_else(|e| panic!("restoring {}: {e}", project.display()));
}

/// The variables of `case` the oracle refuses to set, which the evaluation
/// alone is handed.
fn unsettable(case: &Case) -> Vec<(String, String)> {
    split_variables(case)
        .map(|(_, rest)| rest)
        .unwrap_or_default()
}

/// `case`'s variables, in order, as the build's inputs where the oracle sets
/// them (through [`BuildInputs::env`] for a name on its list, else
/// [`BuildInputs::unlisted_env`]), and the rest: those it refuses, and a
/// second spelling of a name already set (which a build's environment holds,
/// and the oracle does not take twice). `None` when a value cannot be
/// carried.
fn split_variables(case: &Case) -> Option<(BuildInputs, Vec<(String, String)>)> {
    let mut inputs = BuildInputs::new();
    let mut rest = Vec::new();
    for (name, value) in &case.variables {
        let set = match inputs.clone().env(name, value) {
            Err(InputError::NotAnInput(_)) => inputs.clone().unlisted_env(name, value),
            other => other,
        };
        match set {
            Ok(next) => inputs = next,
            Err(InputError::Refused(_) | InputError::Repeated(_)) => {
                rest.push((name.clone(), value.clone()));
            }
            Err(InputError::Unpassable { .. }) => return None,
            Err(e) => panic!("{}: {e:?}", case.label()),
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
    let mut environment: HashMap<String, String> = build_environment().into_iter().collect();
    // What MSBuild computes for itself, as the oracle's other differentials
    // hand it to our evaluation.
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        common::msbuild_user_extensions_path().to_string(),
    );
    environment.extend(inputs.env_vars());
    environment.extend(extra.iter().cloned());
    // The SDK the evaluation resolved is the one being graded.
    assembly_name::derive(project, &globals, &environment, dotnet_root, Sdks::Resolved)
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
/// must-commit.
fn grade(case: &Case) -> Result<Outcome, String> {
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = host_fs::canonicalize(tmp.path()).unwrap().join("project");
    std::fs::create_dir(&dir).unwrap();
    let Some((project, inputs)) = lay_out(case, &dir) else {
        return Ok(Outcome::Inexpressible);
    };
    // The derivation reads a restored evaluation, as the build makes one.
    restore(&project, &inputs);
    after_restore(case, &project);
    let extra = unsettable(case);
    let name = match ours(&project, &inputs, &extra) {
        CompiledAssemblyName::Known(name) => name,
        CompiledAssemblyName::Unknown(why) => {
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
        return if extra.iter().all(|(name, _)| toolchain_variable(name)) {
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
            if case.inert {
                let ours = normalised_arguments(&build, dir);
                let plain = plain_arguments();
                if ours != plain {
                    return Err(format!(
                        "{}: a variable on no list moved fsc's arguments\nplain:\n{plain}\nwith it:\n{ours}",
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
        Err(decline) if case.must_commit.is_some() => Err(format!(
            "{}: committed {name:?}, but the oracle did not answer: {decline:?}",
            case.label()
        )),
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
            let (project, inputs) = lay_out(&cases()[0], &dir).expect("the plain project lays out");
            restore(&project, &inputs);
            let build = fsc_args(&FscArgsRequest {
                project: &project,
                inputs: &inputs,
            })
            .expect("the plain project's build is answered");
            normalised_arguments(&build, &dir)
        })
        .clone()
}

/// Grade `cases` on a few threads; the census, and every failure.
fn grade_all(cases: &[Case]) -> (BTreeMap<(Place, Outcome), usize>, Vec<String>) {
    let next = AtomicUsize::new(0);
    let results = Mutex::new((BTreeMap::new(), Vec::new()));
    std::thread::scope(|scope| {
        let threads: usize = std::env::var("BORZOI_FSC_NAME_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(4);
        assert!(threads > 0, "BORZOI_FSC_NAME_THREADS must be at least 1");
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(case) = cases.get(i) else { break };
                    let graded = grade(case);
                    let mut results = results.lock().unwrap();
                    match graded {
                        Ok(outcome) => *results.0.entry((case.place, outcome)).or_insert(0) += 1,
                        Err(failure) => results.1.push(failure),
                    }
                }
            });
        }
    });
    results.into_inner().unwrap()
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

/// Every [`hostile_environment_cases`] case graded, recording what became of
/// each dimension in the census `assembly_name_environment`, beside the
/// listed names of [`environment_cases`] at a larger sample.
#[test]
#[ignore = "every hostile environment and every hostile name as a variable: one build each that commits"]
fn deep_hostile_environment() {
    let census = coverage::open(
        file!(),
        "assembly_name_environment",
        &[(
            Dimension::NonUtf8,
            "the derivation takes the environment as UTF-8 text, as its caller reads it",
        )],
    );
    let mut failures = Vec::new();
    for (case, dimension) in hostile_environment_cases() {
        match grade(&case) {
            Ok(outcome) => {
                let outcome = format!("{outcome:?}");
                census.reached(
                    &BTreeSet::from([dimension]),
                    outcome.split('(').next().unwrap_or_default(),
                );
            }
            Err(failure) => failures.push(failure),
        }
    }
    // The harness's own values beside them: the listed names and the random
    // names on no list.
    let (outcomes, more) = grade_all(&environment_cases(200, 40));
    for (_, outcome) in outcomes.keys() {
        let outcome = format!("{outcome:?}");
        census.reached(
            &BTreeSet::new(),
            outcome.split('(').next().unwrap_or_default(),
        );
    }
    failures.extend(more);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild \
         --test fsproj_assembly_name_perturbation_diff deep_hostile_environment -- --ignored",
    );
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
}

/// `cases`, but for those `BORZOI_FSC_NAME_ONLY` (a name) leaves out.
fn only(cases: Vec<Case>) -> Vec<Case> {
    match std::env::var("BORZOI_FSC_NAME_ONLY") {
        Ok(name) => cases.into_iter().filter(|c| c.name == name).collect(),
        Err(_) => cases,
    }
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
    let all = cases();
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
    let mut rng = SplitMix64(seed);
    let (mut chosen, mut rest): (Vec<Case>, Vec<Case>) = all
        .into_iter()
        .partition(|c| c.must_commit.is_some() || c.must_decline || c.always);
    for _ in 0..sample.min(rest.len()) {
        let i = rng.below(rest.len());
        chosen.push(rest.swap_remove(i));
    }
    run(&only(chosen));
}

#[test]
#[ignore = "every perturbation: about two thousand cases, most declined without a build"]
fn deep_every_perturbation() {
    let all = only(cases());
    run(&all);
    // A whole, passing run grades the devshell's SDK: record it.
    if std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some() && all.len() == cases().len() {
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
    let (project, inputs) = lay_out(&cases()[0], &dir).expect("the plain project lays out");
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
        let (project, inputs) = lay_out(&cases()[0], &dir).expect("the plain project lays out");
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
    let case = &cases()[0];
    let (project, _) = lay_out(case, &dir).expect("the plain project lays out");
    let globals: HashMap<String, String> = HashMap::new();
    let mut environment: HashMap<String, String> = build_environment().into_iter().collect();
    environment.insert(
        "MSBuildUserExtensionsPath".to_string(),
        common::msbuild_user_extensions_path().to_string(),
    );
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
