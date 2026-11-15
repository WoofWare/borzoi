//! Generative differential: the walk's **import graph** against MSBuild's, over
//! generated SDK import graphs (#677).
//!
//! Every property and target the walk reports is only as exact as the set and
//! order of files it imports. The other differentials hold that graph fixed:
//! the property and target sweeps write SDK-less projects, and the real SDK
//! appears only in the corpus and in fixtures, whose `Directory.Build.*` import
//! points are always the standard ones with true conditions. So a walk that
//! imports a file MSBuild does not, or skips one MSBuild imports, agrees with
//! every one of them.
//!
//! This harness lays out a **synthetic SDK** per case, which the oracle resolves
//! through `--sdks-path` exactly as our resolver does, and varies what decides
//! the graph:
//!
//! - the project form: the `Sdk` attribute, explicit `<Import Sdk=…>` (with
//!   body writes before the props import), no SDK at all, and an SDK reached
//!   only through an imported file;
//! - the `Directory.Build.props` import point in `Sdk.props`: absent, the
//!   standard `Microsoft.Common.props` block, the same block one file deeper,
//!   a condition that is false, one decided by a value `Sdk.props` writes, and
//!   a second import point after the first;
//! - the `Directory.Build.targets` import point in `Sdk.targets`: absent,
//!   standard, false, and decided by a value `Directory.Build.props` writes;
//! - what `Directory.Build.props` writes: the targets gate, that value, and a
//!   redirect of `DirectoryBuildPropsPath`;
//! - re-imports of either file by alias (a `..` respelling, a case respelling,
//!   a directory symlink, a file symlink, a relative path to a symlink beside
//!   the importing file), literal, through the path property, or by writing
//!   the path property alone for an import point to read, from `Sdk.props`
//!   (before or after its props import point), `Sdk.targets`, the body, or
//!   `Directory.Build.targets`.
//!
//! Every file appends its marker to `Trace`, so the final value is a log of
//! which files ran and in what order, and defines the target `T`, so MSBuild's
//! target table names the last file that ran. Both are graded with the
//! oracle's `evaluated` op, certain-implies-exact: a property the walk commits
//! (a trusted value, or a trusted "unset") must be MSBuild's, and a target read
//! the probe calls exact must name the element MSBuild keeps.
//!
//! A project MSBuild rejects is graded too: any value the walk commits for it
//! is a divergence.
//!
//! ## Known divergences
//!
//! A divergence in a case that belongs to none of [`KNOWN_DIVERGENCES`] fails
//! the sweep. Membership is decided from the case's shape, never from the
//! walk's answer. Each known family also has a witness case
//! ([`Family::witness`]) that the test asserts *still* diverges, so the change
//! that fixes a family turns this test red until the family is deleted.
//!
//! ## Anti-vacuity
//!
//! A per-case obligation, not a commit count: [`Case::must_commit`] names the
//! properties the walk has no legitimate reason to decline in that case, and a
//! decline of one is reported like a divergence. Since the families exempt
//! their cases, half the cases lean to the shape real projects have, and the
//! sweep asserts that a quarter of them fall outside every family and that,
//! among those, MSBuild both imports and skips each `Directory.Build.*` file.
//! A census asserts that every value of every dimension is generated.
//!
//! Checked by mutation: deduplicating imports by canonical rather than lexical
//! path fails 44 cases outside every family.

// The aliases are symlinks.
#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use borzoi_msbuild::observed::host_fs;
use borzoi_msbuild::test_support::{PropertyRead, ReadProbe, parse_fsproj_reads};
use borzoi_msbuild::{SdkPaths, SdkResolution, SdkResolveError};
use common::{Oracle, SplitMix64};

// ---------------------------------------------------------------------------
// The case space.
// ---------------------------------------------------------------------------

/// How the project reaches the SDK.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Form {
    /// `<Project Sdk="S">`.
    SdkAttribute,
    /// `<Project>` with `<Import Project="Sdk.props" Sdk="S"/>` and
    /// `<Import Project="Sdk.targets" Sdk="S"/>` in the body, and body writes
    /// before the first.
    ExplicitImports,
    /// `<Project>` with no SDK anywhere.
    SdkLess,
    /// `<Project>` whose body imports a file that is `<Project Sdk="S">`.
    NestedSdk,
}

/// The `Directory.Build.props` import point in `Sdk.props`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PropsPoint {
    Absent,
    /// `Microsoft.Common.props`'s block, verbatim.
    Standard,
    /// The standard block in a file `Sdk.props` imports.
    InSdkFile,
    /// The standard block with a condition that is false.
    ConditionFalse,
    /// The import's condition reads a value `Sdk.props` writes: true or false.
    SdkWrittenGate(bool),
}

/// The `Directory.Build.targets` import point in `Sdk.targets`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TargetsPoint {
    Absent,
    /// `Microsoft.Common.targets`'s block, verbatim.
    Standard,
    ConditionFalse,
    /// The import's condition reads `DemoGate`, which `Directory.Build.props`
    /// may write.
    GateWrittenByProps,
}

/// Which `Directory.Build.*` file a re-import names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Which {
    Props,
    Targets,
}

/// How a re-import spells the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Spelling {
    /// Through `..`, which MSBuild's path normalisation collapses.
    DotDot,
    /// In another case, which MSBuild's duplicate check folds.
    Case,
    /// Through a directory symlink: another file to MSBuild.
    DirLink,
    /// Through a file symlink: another file to MSBuild.
    FileLink,
    /// A relative path, which MSBuild resolves against the directory of the
    /// file the import is in: `rel.{props,targets}`, a symlink to the file in
    /// each directory a site's file is in.
    Relative,
}

/// How a re-import reaches its path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Shape {
    /// `<Import Project="…" Condition="Exists('…')"/>`.
    Literal,
    /// Writes the path to `DirectoryBuild{Props,Targets}Path` and imports
    /// `$(…)` under `exists('$(…)')`: the import point's own shape.
    ViaProperty,
    /// Only writes the path to `DirectoryBuild{Props,Targets}Path`, leaving
    /// the import to whichever import point reads it next.
    PropertyOnly,
}

/// Where a re-import is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Site {
    /// In `Sdk.props`, before its props import point.
    SdkPropsBeforePoint,
    /// In `Sdk.props`, after its props import point.
    SdkProps,
    SdkTargets,
    Body,
    DirectoryBuildTargets,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Reimport {
    which: Which,
    spelling: Spelling,
    shape: Shape,
    site: Site,
}

/// What `Directory.Build.props` holds beyond its marker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct Props {
    present: bool,
    /// Writes `ImportDirectoryBuildTargets=false`.
    disables_targets_import: bool,
    /// Writes `DemoGate=on`, which [`TargetsPoint::GateWrittenByProps`] reads.
    opens_demo_gate: bool,
    /// Writes `DirectoryBuildPropsPath` to `other.props`, beside it.
    redirects_props_path: bool,
}

#[derive(Debug, Clone)]
struct Case {
    form: Form,
    props_point: PropsPoint,
    /// A second props import point after the first, in `Sdk.props`.
    second_props_point: bool,
    targets_point: TargetsPoint,
    props: Props,
    targets_present: bool,
    /// The body (before the props import, in the explicit form) writes
    /// `ImportDirectoryBuildProps=false`.
    body_disables_props_import: bool,
    /// The body writes `ImportDirectoryBuildTargets=false`.
    body_disables_targets_import: bool,
    reimports: Vec<Reimport>,
}

/// The properties every case reads back.
const PROPERTIES: [&str; 9] = [
    "Trace",
    "BodySaw",
    "InDbp",
    "InDbt",
    "InOther",
    "ImportDirectoryBuildProps",
    "ImportDirectoryBuildTargets",
    "DirectoryBuildPropsPath",
    "DirectoryBuildTargetsPath",
];

/// The targets every case reads back: `T` is defined by every file, so the
/// definition MSBuild keeps names the last file that ran; the others by one
/// file each.
const TARGETS: [&str; 4] = ["T", "T_dbp", "T_dbt", "T_body"];

/// A case. Half are drawn leaning to the SDK shape real projects have (the
/// attribute form with the standard import points), which the walk already
/// models, so that the sweep grades many cases in full outside the known
/// families as well as exploring the rest of the space.
fn gen_case(rng: &mut SplitMix64) -> Case {
    let usual = rng.below(2) == 0;
    let form = if usual && rng.below(5) != 0 {
        Form::SdkAttribute
    } else {
        *rng.pick(&[
            Form::SdkAttribute,
            Form::ExplicitImports,
            Form::SdkLess,
            Form::NestedSdk,
        ])
    };
    let props_point = if usual {
        *rng.pick(&[PropsPoint::Standard, PropsPoint::InSdkFile])
    } else {
        *rng.pick(&[
            PropsPoint::Absent,
            PropsPoint::Standard,
            PropsPoint::InSdkFile,
            PropsPoint::ConditionFalse,
            PropsPoint::SdkWrittenGate(true),
            PropsPoint::SdkWrittenGate(false),
        ])
    };
    let targets_point = if usual {
        TargetsPoint::Standard
    } else {
        *rng.pick(&[
            TargetsPoint::Absent,
            TargetsPoint::Standard,
            TargetsPoint::ConditionFalse,
            TargetsPoint::GateWrittenByProps,
        ])
    };
    let props = Props {
        present: rng.below(6) != 0,
        disables_targets_import: rng.below(5) == 0,
        opens_demo_gate: rng.below(2) == 0,
        redirects_props_path: rng.below(6) == 0,
    };
    let reimports = (0..[0, 0, 1, 1, 2][rng.below(5)])
        .map(|_| Reimport {
            which: *rng.pick(&[Which::Props, Which::Targets]),
            spelling: *rng.pick(&[
                Spelling::DotDot,
                Spelling::Case,
                Spelling::DirLink,
                Spelling::FileLink,
                Spelling::Relative,
            ]),
            shape: *rng.pick(&[Shape::Literal, Shape::ViaProperty, Shape::PropertyOnly]),
            site: *rng.pick(&[
                Site::SdkPropsBeforePoint,
                Site::SdkProps,
                Site::SdkTargets,
                Site::Body,
                Site::DirectoryBuildTargets,
            ]),
        })
        .collect();
    Case {
        form,
        props_point,
        second_props_point: !usual && rng.below(4) == 0,
        targets_point,
        props,
        targets_present: rng.below(6) != 0,
        body_disables_props_import: rng.below(6) == 0,
        body_disables_targets_import: rng.below(6) == 0,
        reimports,
    }
}

// ---------------------------------------------------------------------------
// Rendering.
// ---------------------------------------------------------------------------

/// A file's marker: appended to `Trace`, and the target `T` and `T_<marker>`.
fn tracer(marker: &str) -> String {
    format!(
        "  <PropertyGroup>\n    <Trace>$(Trace);{marker}</Trace>\n  </PropertyGroup>\n  \
         <Target Name=\"T\" />\n  <Target Name=\"T_{marker}\" />\n"
    )
}

/// `Microsoft.Common.props`'s `Directory.Build.props` block, with the import's
/// condition replaced by `condition`.
fn props_block(condition: &str) -> String {
    format!(
        r#"  <PropertyGroup>
    <ImportDirectoryBuildProps Condition="'$(ImportDirectoryBuildProps)' == ''">true</ImportDirectoryBuildProps>
  </PropertyGroup>
  <PropertyGroup Condition="'$(ImportDirectoryBuildProps)' == 'true' and '$(DirectoryBuildPropsPath)' == ''">
    <_DirectoryBuildPropsFile Condition="'$(_DirectoryBuildPropsFile)' == ''">Directory.Build.props</_DirectoryBuildPropsFile>
    <_DirectoryBuildPropsBasePath Condition="'$(_DirectoryBuildPropsBasePath)' == ''">$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), '$(_DirectoryBuildPropsFile)'))</_DirectoryBuildPropsBasePath>
    <DirectoryBuildPropsPath Condition="'$(_DirectoryBuildPropsBasePath)' != '' and '$(_DirectoryBuildPropsFile)' != ''">$([System.IO.Path]::Combine('$(_DirectoryBuildPropsBasePath)', '$(_DirectoryBuildPropsFile)'))</DirectoryBuildPropsPath>
  </PropertyGroup>
  <Import Project="$(DirectoryBuildPropsPath)" Condition="{condition}"/>
"#
    )
}

const STANDARD_PROPS_CONDITION: &str =
    "'$(ImportDirectoryBuildProps)' == 'true' and exists('$(DirectoryBuildPropsPath)')";

/// `Microsoft.Common.targets`'s `Directory.Build.targets` block, with the
/// import's condition replaced by `condition`.
fn targets_block(condition: &str) -> String {
    format!(
        r#"  <PropertyGroup>
    <ImportDirectoryBuildTargets Condition="'$(ImportDirectoryBuildTargets)' == ''">true</ImportDirectoryBuildTargets>
  </PropertyGroup>
  <PropertyGroup Condition="'$(ImportDirectoryBuildTargets)' == 'true' and '$(DirectoryBuildTargetsPath)' == ''">
    <_DirectoryBuildTargetsFile Condition="'$(_DirectoryBuildTargetsFile)' == ''">Directory.Build.targets</_DirectoryBuildTargetsFile>
    <_DirectoryBuildTargetsBasePath Condition="'$(_DirectoryBuildTargetsBasePath)' == ''">$([MSBuild]::GetDirectoryNameOfFileAbove($(MSBuildProjectDirectory), '$(_DirectoryBuildTargetsFile)'))</_DirectoryBuildTargetsBasePath>
    <DirectoryBuildTargetsPath Condition="'$(_DirectoryBuildTargetsBasePath)' != '' and '$(_DirectoryBuildTargetsFile)' != ''">$([System.IO.Path]::Combine('$(_DirectoryBuildTargetsBasePath)', '$(_DirectoryBuildTargetsFile)'))</DirectoryBuildTargetsPath>
  </PropertyGroup>
  <Import Project="$(DirectoryBuildTargetsPath)" Condition="{condition}"/>
"#
    )
}

const STANDARD_TARGETS_CONDITION: &str =
    "'$(ImportDirectoryBuildTargets)' == 'true' and exists('$(DirectoryBuildTargetsPath)')";

/// The path a re-import names. All but [`Spelling::Relative`] are absolute
/// through `$(MSBuildProjectDirectory)`, so they mean the same file from
/// whichever file they are written in. The project is `<case>/proj/p.proj`;
/// the `Directory.Build.*` files are in `<case>`, `<case>/proj/up` is a
/// symlink to `<case>`, `<case>/proj/alias.{props,targets}` are symlinks to
/// the two files, and so is `rel.{props,targets}` in the SDK directory,
/// `<case>` and `<case>/proj`.
fn reimport_path(which: Which, spelling: Spelling) -> String {
    let ext = match which {
        Which::Props => "props",
        Which::Targets => "targets",
    };
    match spelling {
        Spelling::DotDot => format!("$(MSBuildProjectDirectory)/../proj/../Directory.Build.{ext}"),
        Spelling::Case => format!("$(MSBuildProjectDirectory)/../DIRECTORY.build.{ext}"),
        Spelling::DirLink => format!("$(MSBuildProjectDirectory)/up/Directory.Build.{ext}"),
        Spelling::FileLink => format!("$(MSBuildProjectDirectory)/alias.{ext}"),
        Spelling::Relative => format!("rel.{ext}"),
    }
}

fn render_reimport(r: &Reimport) -> String {
    let path = reimport_path(r.which, r.spelling);
    match r.shape {
        Shape::Literal => {
            format!("  <Import Project=\"{path}\" Condition=\"Exists('{path}')\" />\n")
        }
        Shape::ViaProperty | Shape::PropertyOnly => {
            let name = match r.which {
                Which::Props => "DirectoryBuildPropsPath",
                Which::Targets => "DirectoryBuildTargetsPath",
            };
            let write =
                format!("  <PropertyGroup>\n    <{name}>{path}</{name}>\n  </PropertyGroup>\n");
            if r.shape == Shape::PropertyOnly {
                write
            } else {
                format!(
                    "{write}  <Import Project=\"$({name})\" Condition=\"exists('$({name})')\" />\n"
                )
            }
        }
    }
}

fn reimports_at(case: &Case, site: Site) -> String {
    case.reimports
        .iter()
        .filter(|r| r.site == site)
        .map(render_reimport)
        .collect()
}

/// The files of one case, as `(path relative to the case directory, text)`,
/// and the SDK's files, relative to the SDK directory.
struct Rendered {
    case_files: Vec<(&'static str, String)>,
    sdk_files: Vec<(&'static str, String)>,
    project: String,
}

fn render(case: &Case, sdk: &str) -> Rendered {
    // Sdk.props.
    let mut sdk_props = String::from("<Project>\n");
    sdk_props.push_str(&tracer("sdkp"));
    sdk_props.push_str(&reimports_at(case, Site::SdkPropsBeforePoint));
    let mut sdk_files = Vec::new();
    match case.props_point {
        PropsPoint::Absent => {}
        PropsPoint::Standard => sdk_props.push_str(&props_block(STANDARD_PROPS_CONDITION)),
        PropsPoint::InSdkFile => {
            sdk_props
                .push_str("  <Import Project=\"$(MSBuildThisFileDirectory)Common.props\" />\n");
            sdk_files.push((
                "Common.props",
                format!(
                    "<Project>\n{}{}</Project>\n",
                    tracer("common"),
                    props_block(STANDARD_PROPS_CONDITION)
                ),
            ));
        }
        PropsPoint::ConditionFalse => sdk_props.push_str(&props_block(
            "'false' == 'true' and exists('$(DirectoryBuildPropsPath)')",
        )),
        PropsPoint::SdkWrittenGate(open) => {
            sdk_props.push_str(&format!(
                "  <PropertyGroup>\n    <DemoImportDbp>{open}</DemoImportDbp>\n  </PropertyGroup>\n"
            ));
            sdk_props.push_str(&props_block(
                "'$(DemoImportDbp)' == 'true' and exists('$(DirectoryBuildPropsPath)')",
            ));
        }
    }
    if case.second_props_point {
        sdk_props.push_str(&format!(
            "  <Import Project=\"$(DirectoryBuildPropsPath)\" Condition=\"{STANDARD_PROPS_CONDITION}\"/>\n"
        ));
    }
    sdk_props.push_str(&reimports_at(case, Site::SdkProps));
    sdk_props.push_str("</Project>\n");
    sdk_files.push(("Sdk.props", sdk_props));

    // Sdk.targets.
    let mut sdk_targets = String::from("<Project>\n");
    sdk_targets.push_str(&tracer("sdkt"));
    match case.targets_point {
        TargetsPoint::Absent => {}
        TargetsPoint::Standard => sdk_targets.push_str(&targets_block(STANDARD_TARGETS_CONDITION)),
        TargetsPoint::ConditionFalse => sdk_targets.push_str(&targets_block(
            "'false' == 'true' and exists('$(DirectoryBuildTargetsPath)')",
        )),
        TargetsPoint::GateWrittenByProps => sdk_targets.push_str(&targets_block(
            "'$(DemoGate)' == 'on' and exists('$(DirectoryBuildTargetsPath)')",
        )),
    }
    sdk_targets.push_str(&reimports_at(case, Site::SdkTargets));
    sdk_targets.push_str(&tracer("sdkt2"));
    sdk_targets.push_str("</Project>\n");
    sdk_files.push(("Sdk.targets", sdk_targets));

    // The user's files.
    let mut case_files = Vec::new();
    if case.props.present {
        let mut text = String::from("<Project>\n");
        text.push_str(&tracer("dbp"));
        text.push_str("  <PropertyGroup>\n    <InDbp>1</InDbp>\n");
        if case.props.disables_targets_import {
            text.push_str("    <ImportDirectoryBuildTargets>false</ImportDirectoryBuildTargets>\n");
        }
        if case.props.opens_demo_gate {
            text.push_str("    <DemoGate>on</DemoGate>\n");
        }
        if case.props.redirects_props_path {
            text.push_str(
                "    <DirectoryBuildPropsPath>$(MSBuildThisFileDirectory)other.props</DirectoryBuildPropsPath>\n",
            );
        }
        text.push_str("  </PropertyGroup>\n</Project>\n");
        case_files.push(("Directory.Build.props", text));
    }
    case_files.push((
        "other.props",
        format!(
            "<Project>\n{}  <PropertyGroup>\n    <InOther>1</InOther>\n  </PropertyGroup>\n</Project>\n",
            tracer("other")
        ),
    ));
    if case.targets_present {
        let mut text = String::from("<Project>\n");
        text.push_str(&tracer("dbt"));
        text.push_str("  <PropertyGroup>\n    <InDbt>1</InDbt>\n  </PropertyGroup>\n");
        text.push_str(&reimports_at(case, Site::DirectoryBuildTargets));
        text.push_str("</Project>\n");
        case_files.push(("Directory.Build.targets", text));
    }

    // The project.
    let mut body = String::new();
    body.push_str("  <PropertyGroup>\n    <BodySaw>$(Trace)</BodySaw>\n  </PropertyGroup>\n");
    body.push_str(&tracer("body"));
    if case.body_disables_targets_import {
        body.push_str(
            "  <PropertyGroup>\n    <ImportDirectoryBuildTargets>false</ImportDirectoryBuildTargets>\n  </PropertyGroup>\n",
        );
    }
    body.push_str(&reimports_at(case, Site::Body));
    let disable_props = if case.body_disables_props_import {
        "  <PropertyGroup>\n    <ImportDirectoryBuildProps>false</ImportDirectoryBuildProps>\n  </PropertyGroup>\n"
    } else {
        ""
    };
    let project = match case.form {
        Form::SdkAttribute => format!("<Project Sdk=\"{sdk}\">\n{disable_props}{body}</Project>\n"),
        Form::ExplicitImports => format!(
            "<Project>\n{disable_props}  <Import Project=\"Sdk.props\" Sdk=\"{sdk}\" />\n{body}  \
             <Import Project=\"Sdk.targets\" Sdk=\"{sdk}\" />\n</Project>\n"
        ),
        Form::SdkLess => format!("<Project>\n{disable_props}{body}</Project>\n"),
        Form::NestedSdk => {
            case_files.push((
                "proj/inner.props",
                format!("<Project Sdk=\"{sdk}\">\n{}</Project>\n", tracer("inner")),
            ));
            format!(
                "<Project>\n{disable_props}{body}  <Import Project=\"inner.props\" />\n</Project>\n"
            )
        }
    };
    Rendered {
        case_files,
        sdk_files,
        project,
    }
}

// ---------------------------------------------------------------------------
// Known divergences.
// ---------------------------------------------------------------------------

/// A family of cases in which the walk's import graph is known to differ from
/// MSBuild's (#677).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Family {
    /// The walk splices `Directory.Build.*` into a project with no SDK, which
    /// MSBuild never imports them into (#676, merged into #677).
    SdkLessSplice,
    /// The walk splices `Directory.Build.*` itself rather than following the
    /// SDK's import, so it diverges wherever the SDK's import point is absent,
    /// conditioned otherwise than the standard block, or reached in a
    /// different place.
    EmulatedImportPoint,
    /// The walk takes every SDK import of `$(DirectoryBuildPropsPath)` for
    /// the props import point it splices itself, and suppresses it when it
    /// names the file the splice took or is about to take: compared by
    /// canonical path, with a relative path resolved against the project's
    /// directory. MSBuild has no such point: it imports any file it has not
    /// imported yet, by lexical full path, resolved against the importing
    /// file's directory. So an SDK that writes the property itself diverges
    /// when it names the file through an alias, relative to itself, or before
    /// a `Directory.Build.props` it imports redirects it.
    PropsPointIdentity,
    /// `Exists()` on a symlink whose target is missing: MSBuild (.NET's
    /// `File.Exists`) says true, the walk says false. So an import guarded by
    /// it is skipped by the walk and attempted by MSBuild, which then rejects
    /// the project (#778).
    DanglingSymlinkExists,
}

const KNOWN_DIVERGENCES: &[Family] = &[
    Family::SdkLessSplice,
    Family::EmulatedImportPoint,
    Family::PropsPointIdentity,
    Family::DanglingSymlinkExists,
];

impl Family {
    /// Whether `case` is in the family: decided from the case's shape alone,
    /// never from how the walk answered it.
    fn contains(self, case: &Case) -> bool {
        let has_file = case.props.present || case.targets_present;
        match self {
            Family::SdkLessSplice => case.form == Form::SdkLess && has_file,
            Family::EmulatedImportPoint => {
                // The splice and the SDK's real import agree only when the SDK
                // is the project's own, reached through the attribute, and its
                // import points are the standard blocks.
                case.form != Form::SdkLess
                    && has_file
                    && (case.form != Form::SdkAttribute
                        || !matches!(
                            case.props_point,
                            PropsPoint::Standard | PropsPoint::InSdkFile
                        )
                        || case.second_props_point
                        || case.targets_point != TargetsPoint::Standard)
            }
            // Every site but the body can be in a file the walk counts as the
            // SDK's: `Directory.Build.targets` too, when an SDK file reaches
            // it through the `rel.targets` link in the SDK's directory.
            Family::PropsPointIdentity => case.reimports.iter().any(|r| {
                r.which == Which::Props
                    && matches!(r.shape, Shape::ViaProperty | Shape::PropertyOnly)
                    && r.site != Site::Body
            }),
            Family::DanglingSymlinkExists => case.reimports.iter().any(|r| {
                matches!(r.spelling, Spelling::FileLink | Spelling::Relative)
                    && match r.which {
                        Which::Props => !case.props.present,
                        Which::Targets => !case.targets_present,
                    }
            }),
        }
    }

    /// A case the family's divergence is known to show in, which the test
    /// asserts still diverges.
    fn witness(self) -> Case {
        let base = Case::usual();
        match self {
            Family::SdkLessSplice => Case {
                form: Form::SdkLess,
                ..base
            },
            Family::EmulatedImportPoint => Case {
                props_point: PropsPoint::Absent,
                ..base
            },
            Family::PropsPointIdentity => Case {
                reimports: vec![Reimport {
                    which: Which::Props,
                    spelling: Spelling::FileLink,
                    shape: Shape::ViaProperty,
                    site: Site::SdkProps,
                }],
                ..base
            },
            Family::DanglingSymlinkExists => Case {
                targets_present: false,
                reimports: vec![Reimport {
                    which: Which::Targets,
                    spelling: Spelling::FileLink,
                    shape: Shape::Literal,
                    site: Site::Body,
                }],
                ..base
            },
        }
    }
}

impl Case {
    /// The SDK attribute form with the standard import points and both
    /// `Directory.Build.*` files.
    fn usual() -> Case {
        Case {
            form: Form::SdkAttribute,
            props_point: PropsPoint::Standard,
            second_props_point: false,
            targets_point: TargetsPoint::Standard,
            props: Props {
                present: true,
                ..Props::default()
            },
            targets_present: true,
            body_disables_props_import: false,
            body_disables_targets_import: false,
            reimports: Vec::new(),
        }
    }

    /// The properties the walk has no reason to decline here. Every import
    /// condition in the case is a literal or reads a literal some file wrote,
    /// every path is one the walk can spell, and nothing reads the
    /// environment, so the log of which files ran and the markers they wrote
    /// are all decided.
    fn must_commit(&self) -> &'static [&'static str] {
        &["Trace", "BodySaw", "InDbp", "InDbt", "InOther"]
    }
}

// ---------------------------------------------------------------------------
// Both-ways evaluation.
// ---------------------------------------------------------------------------

struct Shared {
    root: PathBuf,
    oracle: Oracle,
}

impl Shared {
    fn new() -> Shared {
        // `BORZOI_IMPORT_GRAPH_ROOT` moves the cases to another file system,
        // so a run on a case-insensitive host can check the case-sensitive
        // behaviour CI's Linux runners have, and vice versa.
        let base = std::env::var_os("BORZOI_IMPORT_GRAPH_ROOT")
            .map_or_else(|| PathBuf::from(env!("CARGO_TARGET_TMPDIR")), PathBuf::from);
        let root = base.join(format!(
            "sdk-import-graph-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(root.join("Sdks")).expect("mkdir Sdks");
        let root = host_fs::canonicalize(&root).expect("canonicalize root");
        let oracle = Oracle::spawn_with_sdks_path(&root.join("Sdks"));
        Shared { root, oracle }
    }
}

impl Drop for Shared {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// One disagreement, or a declined obligation.
#[derive(Debug)]
struct Finding {
    what: String,
    ours: String,
    theirs: String,
}

/// What one case came to.
#[derive(Debug, Default)]
struct Outcome {
    findings: Vec<Finding>,
    /// MSBuild rejected the project.
    rejected: bool,
    committed_properties: usize,
    exact_targets: usize,
    /// Whether MSBuild imported `Directory.Build.props` and `.targets`, read
    /// off the markers they write.
    msbuild_imported: Option<(bool, bool)>,
}

fn symlink(target: &Path, link: &Path) {
    std::os::unix::fs::symlink(target, link)
        .unwrap_or_else(|e| panic!("symlink {} -> {}: {e}", link.display(), target.display()));
}

fn evaluate(shared: &mut Shared, case: &Case) -> (Outcome, String) {
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    let sdk = format!("S{n}");
    let sdk_dir = shared.root.join("Sdks").join(&sdk).join("Sdk");
    let case_dir = shared.root.join(format!("case{n}"));
    std::fs::create_dir_all(&sdk_dir).expect("mkdir sdk");
    std::fs::create_dir_all(case_dir.join("proj")).expect("mkdir proj");
    let rendered = render(case, &sdk);
    for (name, text) in &rendered.sdk_files {
        std::fs::write(sdk_dir.join(name), text).expect("write sdk file");
    }
    for (name, text) in &rendered.case_files {
        std::fs::write(case_dir.join(name), text).expect("write case file");
    }
    // The case respelling names a file that exists whenever the original
    // does, on either kind of file system: a case-insensitive one finds the
    // original under it, and on a case-sensitive one it is a link.
    for ext in ["props", "targets"] {
        let original = case_dir.join(format!("Directory.Build.{ext}"));
        let respelt = case_dir.join(format!("DIRECTORY.build.{ext}"));
        if host_fs::symlink_metadata(&original).is_ok()
            && host_fs::symlink_metadata(&respelt).is_err()
        {
            symlink(&original, &respelt);
        }
    }
    symlink(Path::new(".."), &case_dir.join("proj/up"));
    symlink(
        Path::new("../Directory.Build.props"),
        &case_dir.join("proj/alias.props"),
    );
    symlink(
        Path::new("../Directory.Build.targets"),
        &case_dir.join("proj/alias.targets"),
    );
    for dir in [
        sdk_dir.as_path(),
        case_dir.as_path(),
        &case_dir.join("proj"),
    ] {
        symlink(
            &case_dir.join("Directory.Build.props"),
            &dir.join("rel.props"),
        );
        symlink(
            &case_dir.join("Directory.Build.targets"),
            &dir.join("rel.targets"),
        );
    }
    let project_path = case_dir.join("proj/p.proj");
    std::fs::write(&project_path, &rendered.project).expect("write project");

    let resolver = {
        let sdk = sdk.clone();
        let sdk_dir = sdk_dir.clone();
        move |name: &str, _: &borzoi_msbuild::observed::Observer| {
            if name.eq_ignore_ascii_case(&sdk) {
                Ok(SdkResolution::Single(SdkPaths {
                    root: sdk_dir.clone(),
                    props: sdk_dir.join("Sdk.props"),
                    targets: sdk_dir.join("Sdk.targets"),
                }))
            } else {
                Err(SdkResolveError::NotFound)
            }
        }
    };
    // The oracle sets `MSBuildSDKsPath` in its own environment, which MSBuild
    // folds in as an initial property; our side sees the same snapshot.
    let mut environment = common::oracle_environment();
    environment.insert(
        "MSBuildSDKsPath".to_string(),
        shared.root.join("Sdks").to_string_lossy().into_owned(),
    );
    let probe = ReadProbe {
        properties: PROPERTIES.iter().map(|p| (*p).to_owned()).collect(),
        targets: TARGETS.iter().map(|t| (*t).to_owned()).collect(),
        ..ReadProbe::default()
    };
    let (_, ours) = parse_fsproj_reads(
        &rendered.project,
        &project_path,
        &HashMap::new(),
        &environment,
        Some(&resolver),
        None,
        &probe,
    )
    .expect("well-formed XML parses");
    let theirs = shared
        .oracle
        .try_evaluated(&project_path, &[], &PROPERTIES, &[], &TARGETS);

    let mut outcome = Outcome::default();
    let mut describe = format!("{case:#?}\n--- p.proj\n{}", rendered.project);
    for (name, text) in rendered.sdk_files.iter().chain(&rendered.case_files) {
        describe.push_str(&format!("--- {name}\n{text}"));
    }
    let Some(theirs) = theirs else {
        // MSBuild refuses the project, so any value the walk commits is one no
        // build holds.
        outcome.rejected = true;
        for name in PROPERTIES {
            if let read @ (PropertyRead::Value(_) | PropertyRead::Unset) = &ours.properties[name] {
                outcome.findings.push(Finding {
                    what: name.to_owned(),
                    ours: format!("{read:?}"),
                    theirs: "a rejected project".to_owned(),
                });
            }
        }
        let _ = std::fs::remove_dir_all(&case_dir);
        let _ = std::fs::remove_dir_all(sdk_dir.parent().unwrap());
        return (outcome, describe);
    };
    outcome.msbuild_imported = Some((
        !theirs["properties"]["InDbp"].is_null(),
        !theirs["properties"]["InDbt"].is_null(),
    ));
    for name in PROPERTIES {
        let theirs = &theirs["properties"][name];
        let read = &ours.properties[name];
        let committed = match read {
            PropertyRead::Value(value) => {
                (theirs.as_str() != Some(value.as_str())).then(|| format!("{value:?}"))
            }
            PropertyRead::Unset => (!theirs.is_null()).then(|| "unset".to_owned()),
            PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => {
                if case.must_commit().contains(&name) {
                    outcome.findings.push(Finding {
                        what: format!("{name} (must commit)"),
                        ours: format!("{read:?}"),
                        theirs: theirs.to_string(),
                    });
                }
                continue;
            }
        };
        outcome.committed_properties += 1;
        if let Some(ours) = committed {
            outcome.findings.push(Finding {
                what: name.to_owned(),
                ours,
                theirs: theirs.to_string(),
            });
        }
    }
    for name in TARGETS {
        match common::check_target(&ours.targets[name], &theirs["targets"][name]) {
            Ok(true) => outcome.exact_targets += 1,
            Ok(false) => {}
            Err(why) => outcome.findings.push(Finding {
                what: format!("target {name}"),
                ours: why,
                theirs: String::new(),
            }),
        }
    }
    let _ = std::fs::remove_dir_all(&case_dir);
    let _ = std::fs::remove_dir_all(sdk_dir.parent().unwrap());
    (outcome, describe)
}

// ---------------------------------------------------------------------------
// The sweep.
// ---------------------------------------------------------------------------

/// One line naming the case's shape, for a worklist.
fn brief(case: &Case) -> String {
    let p = case.props;
    let mut s = format!(
        "{:?} pp={:?}{} tp={:?} dbp={}{}{}{} dbt={} body={}{}",
        case.form,
        case.props_point,
        if case.second_props_point { "+2nd" } else { "" },
        case.targets_point,
        u8::from(p.present),
        if p.disables_targets_import {
            "/noT"
        } else {
            ""
        },
        if p.opens_demo_gate { "/gate" } else { "" },
        if p.redirects_props_path { "/redir" } else { "" },
        u8::from(case.targets_present),
        if case.body_disables_props_import {
            "noP"
        } else {
            "-"
        },
        if case.body_disables_targets_import {
            "noT"
        } else {
            "-"
        },
    );
    for r in &case.reimports {
        s.push_str(&format!(
            " re[{:?} {:?} {:?} @{:?}]",
            r.which, r.spelling, r.shape, r.site
        ));
    }
    s
}

/// Which value of each dimension the sweep generated, as `dimension=value`.
fn census_keys(case: &Case) -> Vec<String> {
    let mut keys = vec![
        format!("form={:?}", case.form),
        format!("props_point={:?}", case.props_point),
        format!("second_props_point={}", case.second_props_point),
        format!("targets_point={:?}", case.targets_point),
        format!("props.present={}", case.props.present),
        format!(
            "props.disables_targets_import={}",
            case.props.disables_targets_import
        ),
        format!("props.opens_demo_gate={}", case.props.opens_demo_gate),
        format!(
            "props.redirects_props_path={}",
            case.props.redirects_props_path
        ),
        format!("targets_present={}", case.targets_present),
        format!(
            "body_disables_props_import={}",
            case.body_disables_props_import
        ),
        format!(
            "body_disables_targets_import={}",
            case.body_disables_targets_import
        ),
    ];
    for r in &case.reimports {
        keys.push(format!("reimport.which={:?}", r.which));
        // A spelling is exercised only when it names a file that exists:
        // otherwise its `Exists()` guard skips it before identity matters.
        let target_present = match r.which {
            Which::Props => case.props.present,
            Which::Targets => case.targets_present,
        };
        if target_present {
            keys.push(format!("reimport.spelling={:?}", r.spelling));
        }
        keys.push(format!("reimport.shape={:?}", r.shape));
        keys.push(format!("reimport.site={:?}", r.site));
    }
    keys
}

#[derive(Default)]
struct Report {
    cases: usize,
    rejected: usize,
    committed_properties: usize,
    exact_targets: usize,
    /// Cases in no known family, which the sweep grades in full.
    outside_families: usize,
    /// Of those, how often MSBuild imported `(Directory.Build.props,
    /// Directory.Build.targets)`.
    outside_imports: BTreeMap<(bool, bool), usize>,
    /// Findings in cases outside every known family: the case in one line
    /// with its findings, and the case in full.
    unexplained: Vec<(String, String)>,
    /// Cases with findings, by the known families they belong to.
    explained: BTreeMap<Vec<Family>, usize>,
    census: BTreeMap<String, usize>,
}

fn sweep(seed: u64, cases: usize) -> Report {
    let mut rng = SplitMix64(seed);
    let mut shared = Shared::new();
    let mut report = Report::default();
    for _ in 0..cases {
        let case = gen_case(&mut rng);
        for key in census_keys(&case) {
            *report.census.entry(key).or_default() += 1;
        }
        let families: Vec<Family> = KNOWN_DIVERGENCES
            .iter()
            .copied()
            .filter(|f| f.contains(&case))
            .collect();
        let (outcome, describe) = evaluate(&mut shared, &case);
        report.cases += 1;
        report.rejected += usize::from(outcome.rejected);
        report.committed_properties += outcome.committed_properties;
        report.exact_targets += outcome.exact_targets;
        if families.is_empty() {
            report.outside_families += 1;
            if let Some(imported) = outcome.msbuild_imported {
                *report.outside_imports.entry(imported).or_default() += 1;
            }
        }
        if outcome.findings.is_empty() {
            continue;
        }
        if families.is_empty() {
            let findings: Vec<String> = outcome
                .findings
                .iter()
                .map(|f| format!("    {}: ours {}, MSBuild {}", f.what, f.ours, f.theirs))
                .collect();
            report.unexplained.push((
                format!("{}\n{}", brief(&case), findings.join("\n")),
                describe,
            ));
        } else {
            *report.explained.entry(families).or_default() += 1;
        }
    }
    report
}

fn assert_clean(report: &Report) {
    eprintln!(
        "sdk import graph: {} cases, {} rejected, {} committed property reads, \
         {} exact target reads; {} cases outside every family, MSBuild's \
         (props, targets) imports among them: {:?}; known-family cases with \
         findings: {:?}",
        report.cases,
        report.rejected,
        report.committed_properties,
        report.exact_targets,
        report.outside_families,
        report.outside_imports,
        report.explained
    );
    assert!(
        report.unexplained.is_empty(),
        "{} cases outside every known family disagree with MSBuild:\n{}\n\nThe first in full:\n{}",
        report.unexplained.len(),
        report
            .unexplained
            .iter()
            .map(|(brief, _)| brief.as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        report
            .unexplained
            .iter()
            .take(3)
            .map(|(_, full)| full.as_str())
            .collect::<Vec<_>>()
            .join("\n=====\n")
    );
}

#[test]
fn the_import_graph_is_exact_or_declined() {
    let report = sweep(0x5d4b_0677, 600);
    assert_clean(&report);
    // The families exempt cases from grading, so the sweep must still grade a
    // good share of cases in full, and among them see MSBuild both import and
    // skip each file.
    assert!(
        report.outside_families * 4 > report.cases,
        "only {} of {} cases are outside every known family",
        report.outside_families,
        report.cases
    );
    for (which, pick) in [
        (
            "Directory.Build.props",
            (|k: &(bool, bool)| k.0) as fn(&(bool, bool)) -> bool,
        ),
        ("Directory.Build.targets", |k: &(bool, bool)| k.1),
    ] {
        for imported in [true, false] {
            let n: usize = report
                .outside_imports
                .iter()
                .filter(|(k, _)| pick(k) == imported)
                .map(|(_, n)| n)
                .sum();
            assert!(
                n >= 10,
                "outside every family, MSBuild {} {which} in only {n} cases",
                if imported { "imported" } else { "skipped" }
            );
        }
    }
    // MSBuild rejects only the dangling-symlink imports: a case it rejects
    // grades little, so a generator drifting into rejected shapes would hollow
    // the sweep out.
    assert!(
        report.rejected * 10 < report.cases,
        "MSBuild rejected {} of {} generated projects",
        report.rejected,
        report.cases
    );
    // Every value of every dimension is generated, so no axis is dead.
    let expected: BTreeSet<String> = [
        "form=SdkAttribute",
        "form=ExplicitImports",
        "form=SdkLess",
        "form=NestedSdk",
        "props_point=Absent",
        "props_point=Standard",
        "props_point=InSdkFile",
        "props_point=ConditionFalse",
        "props_point=SdkWrittenGate(true)",
        "props_point=SdkWrittenGate(false)",
        "second_props_point=true",
        "targets_point=Absent",
        "targets_point=Standard",
        "targets_point=ConditionFalse",
        "targets_point=GateWrittenByProps",
        "props.present=false",
        "props.disables_targets_import=true",
        "props.opens_demo_gate=true",
        "props.redirects_props_path=true",
        "targets_present=false",
        "body_disables_props_import=true",
        "body_disables_targets_import=true",
        "reimport.which=Props",
        "reimport.which=Targets",
        "reimport.spelling=DotDot",
        "reimport.spelling=Case",
        "reimport.spelling=DirLink",
        "reimport.spelling=FileLink",
        "reimport.spelling=Relative",
        "reimport.shape=Literal",
        "reimport.shape=ViaProperty",
        "reimport.shape=PropertyOnly",
        "reimport.site=SdkPropsBeforePoint",
        "reimport.site=SdkProps",
        "reimport.site=SdkTargets",
        "reimport.site=Body",
        "reimport.site=DirectoryBuildTargets",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let missing: Vec<&String> = expected
        .iter()
        .filter(|key| report.census.get(*key).copied().unwrap_or(0) < 5)
        .collect();
    assert!(
        missing.is_empty(),
        "dimension values generated fewer than 5 times: {missing:?}"
    );
}

/// Each known family's witness still diverges. When one stops, the family is
/// fixed: delete it from [`KNOWN_DIVERGENCES`], so the sweep holds every case
/// it covered.
#[test]
fn every_known_divergence_still_diverges() {
    let mut shared = Shared::new();
    let mut fixed = Vec::new();
    for family in KNOWN_DIVERGENCES {
        let case = family.witness();
        assert!(
            family.contains(&case),
            "{family:?}'s witness is not in the family"
        );
        let (outcome, describe) = evaluate(&mut shared, &case);
        if outcome.findings.is_empty() {
            fixed.push(format!("{family:?}\n{describe}"));
        }
    }
    assert!(
        fixed.is_empty(),
        "known divergences no longer diverge; delete them from KNOWN_DIVERGENCES:\n{}",
        fixed.join("\n=====\n")
    );
}

#[test]
#[ignore = "a fresh-seed soak; BORZOI_MSBUILD_SOAK_SEED / BORZOI_MSBUILD_SOAK_CASES"]
fn soak() {
    let (seed, cases) = common::soak_parameters("fsproj_sdk_import_graph_generative_diff", 3000);
    assert_clean(&sweep(seed, cases));
}
