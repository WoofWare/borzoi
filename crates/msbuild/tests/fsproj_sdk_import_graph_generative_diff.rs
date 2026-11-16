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
//!   a condition that is false, one decided by a value `Sdk.props` writes, the
//!   block behind an import the walk cannot decide, and a second import point
//!   after the first;
//! - the `Directory.Build.targets` import point in `Sdk.targets`: absent,
//!   standard, false, decided by a value `Directory.Build.props` writes, inside
//!   an `<ImportGroup>` after a helper import, and behind an import the walk
//!   cannot decide;
//! - what `Directory.Build.props` writes: the targets gate, that value, a
//!   redirect of `DirectoryBuildPropsPath`, and `Exists()` probes under a
//!   `<When>`, a property element and a property group;
//! - re-imports of either file by alias (a `..` respelling, a `..` after a
//!   directory symlink, a case respelling, a directory symlink, a file
//!   symlink, a relative path to a symlink beside the importing file, and one
//!   beside the importing file but not the project), literal, through the path property, SDK-qualified
//!   (`<Import Sdk=…>`), or by writing the path property alone for an import
//!   point to read, from `Sdk.props` (before or after its props import point),
//!   `Sdk.targets`, the body, or `Directory.Build.targets`;
//! - a write to one of the four import inputs (each file's gate and path) the
//!   walk cannot pin down: under a condition it cannot decide, refused then
//!   overwritten, or refused then overwritten from a value an import it cannot
//!   decide redefines; in `Sdk.props`, the body, or a helper `Sdk.targets`
//!   imports just before its point.
//! - an import of a user's file, or an `<ImportGroup>` around one, in `Sdk.props`,
//!   the body or `Sdk.targets`, under a gate MSBuild takes or skips that reads a
//!   value the walk doubts: one written under a condition it cannot decide, a
//!   toolset property it does not seed, one an import it cannot decide
//!   rewrites, one refused then overwritten, and one an SDK file marks tainted
//!   without a diagnostic (the gated imports, [`GateInput`]).
//!
//! Every file appends its marker to `Trace`, so the final value is a log of
//! which files ran and in what order, and defines the target `T`, so MSBuild's
//! target table names the last file that ran; a user's file also contributes a
//! Compile item. Every file also declares a `<ProjectReference>` of its own,
//! and a user's file other than the project removes the project's, so content
//! that runs after the body changes the list. Every file also appends a define
//! of its own to `DefineConstants`. All five are graded with the oracle's
//! `evaluated` op, certain-implies-exact: a property the walk commits (a
//! trusted value, or a trusted "unset") must be MSBuild's, a target read the
//! probe calls exact must name the element MSBuild keeps, and a Compile set the
//! walk calls certain (`items_uncertain` false, what the LSP folds), a
//! reference list it calls certain (`project_references_uncertain` false, the
//! LSP's project graph) and a define set it calls certain
//! (`define_constants_uncertain` false, the `#if` symbols the LSP parses
//! under) must be MSBuild's, entry for entry and in order.
//!
//! A project MSBuild rejects is graded too: any value the walk commits for it
//! is a divergence.
//!
//! ## Known divergences
//!
//! A divergence in a case that belongs to none of [`KNOWN_DIVERGENCES`] fails
//! the sweep. Membership is decided from the case's shape, never from the
//! walk's answer, and a family may explain only some of a case's findings
//! ([`Family::covers`]). Each known family also has a witness case
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
use borzoi_msbuild::{RejectionCertainty, SdkPaths, SdkResolution, SdkResolveError};
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
    /// The standard block in a file `Sdk.props` imports under a condition
    /// MSBuild finds true and the walk cannot decide.
    BehindUndecidedImport,
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
    /// The standard block with its import inside an `<ImportGroup>`, after an
    /// import of the SDK's `Helper.targets`, which can rewrite its inputs.
    InImportGroup,
    /// The standard block in a file `Sdk.targets` imports under a condition
    /// MSBuild finds true and the walk cannot decide.
    BehindUndecidedImport,
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
    /// Through `..` after a directory symlink, which MSBuild collapses as
    /// text: the file beside the link, not the decoy beside its target.
    LinkDotDot,
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
    /// A relative path to `relx.{props,targets}`, a symlink to the file beside
    /// the SDK's files and `Directory.Build.targets` but not beside the
    /// project. An `<Import>`'s condition resolves `Exists()` against the
    /// importing file's directory, as the import itself does; most other
    /// conditions resolve it against the project's.
    RelativeElsewhere,
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
    /// [`Shape::ViaProperty`] with the import qualified by the SDK
    /// (`<Import Sdk="S" Project="$(…)"/>`), which MSBuild resolves by joining
    /// the SDK's directory to the attribute as written. The path is written
    /// relative to the SDK's directory, whatever the spelling.
    ViaPropertySdk,
    /// [`Shape::ViaPropertySdk`] with the spelling's absolute path, which the
    /// join appends rather than substitutes.
    ViaPropertySdkAbsolute,
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
    /// Writes three properties under `Exists('p.proj')`, which only the
    /// project's directory has: `ExistsProbe` under a `<When>`,
    /// `ExistsElementProbe` under the property element's own condition, and
    /// `ExistsGroupProbe` under a property group's. MSBuild resolves the
    /// first two against the project's directory and the third against this
    /// file's (`Evaluator.GetCurrentDirectoryForConditionEvaluation`).
    probes_exists: bool,
}

/// Where an [`Undecided`] write sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum UndecidedSite {
    /// In `Sdk.props`, before its props import point.
    SdkProps,
    /// In the body (before the props import, in the explicit form).
    Body,
    /// In the SDK's `Helper.targets`, which `Sdk.targets` imports just before
    /// its targets import point (inside the group, for
    /// [`TargetsPoint::InImportGroup`]).
    SdkTargetsHelper,
}

/// One of the four properties that decide the `Directory.Build.*` imports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ImportInput {
    PropsGate,
    PropsPath,
    TargetsGate,
    TargetsPath,
}

/// How an [`Undecided`] write leaves its property.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum UndecidedHow {
    /// Written under a condition MSBuild finds true and the walk cannot
    /// decide: a gate to `false`, a path to `other.props`.
    UnderUndecidedCondition,
    /// Written from a value the walk cannot compute, so it refuses the write,
    /// then overwritten with a clean value.
    RefusedThenOverwritten,
    /// Refused, then overwritten from `$(UndecidedStale)`, which `Sdk.props`
    /// defines and then redefines in an import the walk cannot decide: the
    /// overwrite is clean text resting on a value hidden content changed.
    RefusedThenStale,
}

/// A write to an import input the walk cannot pin down. The walk may decline
/// whatever it decides; it must not commit what MSBuild does not hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Undecided {
    site: UndecidedSite,
    input: ImportInput,
    how: UndecidedHow,
}

/// How an import point's decision is put in doubt to the walk, though not to
/// MSBuild, which decides it (#677).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PointDoubt {
    /// Nothing: the walk decides the point.
    Decided,
    /// The point's condition gains a conjunct MSBuild finds true and the walk
    /// cannot evaluate: the walk is unsure whether the file is imported.
    GateTrue,
    /// The same, with a conjunct MSBuild finds false.
    GateFalse,
    /// The point's `Exists` becomes a disjunct beside a term MSBuild finds
    /// true and the walk cannot evaluate: MSBuild imports the path whether or
    /// not the file exists, and rejects the project when it does not (MSB4019).
    GateOr,
    /// The SDK's discovery computes the path with an expression the walk
    /// refuses and MSBuild evaluates to the default: the walk is unsure which
    /// file is imported.
    PathRefused,
}

/// Which file a [`Repeat`] imports again: the `Directory.Build.*` file its
/// point imports, or the file that one imports (`child`), or the file that
/// one imports (`grandchild`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum RepeatTarget {
    File,
    Child,
    Grandchild,
}

/// Where a [`Repeat`] is written, relative to the point of its kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum RepeatSite {
    /// In the body: after the props point, before the targets point.
    Body,
    /// In the SDK file holding the point, before it.
    SdkBeforePoint,
    /// The same, under a condition MSBuild takes and the walk cannot decide:
    /// content the walk cannot see imports the file before the point.
    HiddenBeforePoint,
    /// The same through an SDK file: the import the walk cannot decide is of
    /// `Via<i>`, beside the SDK's files, which imports the file. That the
    /// hidden import names a file of the SDK says nothing of what it reaches.
    HiddenViaSdkFile,
    /// In the SDK file holding the point, after it.
    SdkAfterPoint,
    /// In `child` (a cycle when it imports the file or itself).
    InChild,
    /// In `grandchild`.
    InGrandchild,
}

/// An import, by its own spelling, of a file the point of [`Case::repeat_which`]
/// imports or reaches, which MSBuild skips when that file is imported already
/// and walks otherwise. The site sets `Seen`, `SeenChild` and
/// `SeenGrandchild` to `pre<i>` just before it and copies them to
/// `Repeat<i>`, `Repeat<i>Child` and `Repeat<i>Grandchild` just after. Every
/// file it may import writes its marker to `Seen`, and `child` and
/// `grandchild` to their own as well, so the copies say which files ran
/// there, a file's own one even when a later file overwrote `Seen`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Repeat {
    target: RepeatTarget,
    site: RepeatSite,
}

impl Repeat {
    /// Whether the walk cannot see the import, which MSBuild makes.
    fn is_hidden(&self) -> bool {
        matches!(
            self.site,
            RepeatSite::HiddenBeforePoint | RepeatSite::HiddenViaSdkFile
        )
    }
}

/// Where a [`GatedImport`] is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum GatedSite {
    /// At the end of `Sdk.props`.
    SdkProps,
    /// In the body, after the project's own tracer.
    Body,
    /// In `Sdk.targets`, before its closing tracer.
    SdkTargets,
}

/// How the value a [`GatedImport`]'s gate reads is put in doubt to the walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum GateInput {
    /// `GateIn` is written `off`, then `on` under a condition MSBuild takes and
    /// the walk cannot decide: the walk holds a value it cannot pin down.
    UnderUndecidedCondition,
    /// The gate reads `$(RoslynTargetsPath)`, a toolset property the walk does
    /// not seed and MSBuild defines.
    UnseededToolset,
    /// `GateIn` is written `on`, then a property group whose gate reads
    /// `$(RoslynTargetsPath)` (so the walk cannot pin it down) holds a write of
    /// `GateIn` under a condition that is cleanly false. In an SDK file the
    /// walk marks `GateIn` SDK-tainted without a diagnostic, though no build
    /// rewrites it, so the gate reads a value the walk calls untrusted and its
    /// decision raises nothing.
    SdkTaintedOnly,
    /// `GateIn` is written from a value the walk refuses, then overwritten
    /// with `on`.
    RefusedThenOverwritten,
    /// `GateIn` is written `off`, then rewritten `on` by an import MSBuild
    /// takes and the walk cannot decide: a stale value.
    HiddenRewrite,
}

/// An `<Import>` (or an `<ImportGroup>` around one) of the user's
/// `gated.props` under a condition that reads a value the walk doubts. The
/// file appends its tracer, so all three item axes see whether it ran.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GatedImport {
    site: GatedSite,
    input: GateInput,
    /// Through an `<ImportGroup Condition>` rather than the import's own.
    group: bool,
    /// The gate tests the value MSBuild holds (`on`, or a defined
    /// `RoslynTargetsPath`), so MSBuild takes the import; otherwise it tests
    /// the other value and skips it.
    taken: bool,
}

impl GatedImport {
    /// Whether the gate's decision raises a diagnostic in the walk, which
    /// latches its opacity: every input but the two it decides exactly.
    fn undecided_to_the_walk(self) -> bool {
        !matches!(
            self.input,
            GateInput::SdkTaintedOnly | GateInput::RefusedThenOverwritten
        )
    }
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
    undecided: Option<Undecided>,
    /// The kind whose point [`Self::point_doubt`] doubts and whose files
    /// [`Self::repeats`] import again.
    repeat_which: Which,
    point_doubt: PointDoubt,
    repeats: Vec<Repeat>,
    /// Never at an SDK site in an SDK-less project, which has no SDK file to
    /// write it in, so a case with one always evaluates its gate.
    gated: Option<GatedImport>,
}

/// The properties every case reads back.
const PROPERTIES: [&str; 22] = [
    "Seen",
    "SeenChild",
    "SeenGrandchild",
    "Repeat0",
    "Repeat0Child",
    "Repeat0Grandchild",
    "Repeat1",
    "Repeat1Child",
    "Repeat1Grandchild",
    "Trace",
    "DefineConstants",
    "BodySaw",
    "InDbp",
    "InDbt",
    "InOther",
    "ImportDirectoryBuildProps",
    "ImportDirectoryBuildTargets",
    "DirectoryBuildPropsPath",
    "DirectoryBuildTargetsPath",
    "ExistsProbe",
    "ExistsElementProbe",
    "ExistsGroupProbe",
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
            PropsPoint::BehindUndecidedImport,
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
            TargetsPoint::InImportGroup,
            TargetsPoint::BehindUndecidedImport,
        ])
    };
    let props = Props {
        present: rng.below(6) != 0,
        disables_targets_import: rng.below(5) == 0,
        opens_demo_gate: rng.below(2) == 0,
        redirects_props_path: rng.below(6) == 0,
        probes_exists: !usual && rng.below(4) == 0,
    };
    let reimports = (0..[0, 0, 1, 1, 2][rng.below(5)])
        .map(|_| Reimport {
            which: *rng.pick(&[Which::Props, Which::Targets]),
            spelling: *rng.pick(&[
                Spelling::DotDot,
                Spelling::LinkDotDot,
                Spelling::Case,
                Spelling::DirLink,
                Spelling::FileLink,
                Spelling::Relative,
                Spelling::RelativeElsewhere,
            ]),
            shape: *rng.pick(&[
                Shape::Literal,
                Shape::ViaProperty,
                Shape::PropertyOnly,
                Shape::ViaPropertySdk,
                Shape::ViaPropertySdkAbsolute,
            ]),
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
        undecided: (!usual && rng.below(3) == 0).then(|| Undecided {
            site: *rng.pick(&[
                UndecidedSite::SdkProps,
                UndecidedSite::Body,
                UndecidedSite::SdkTargetsHelper,
            ]),
            input: *rng.pick(&[
                ImportInput::PropsGate,
                ImportInput::PropsPath,
                ImportInput::TargetsGate,
                ImportInput::TargetsPath,
            ]),
            how: *rng.pick(&[
                UndecidedHow::UnderUndecidedCondition,
                UndecidedHow::RefusedThenOverwritten,
                UndecidedHow::RefusedThenStale,
            ]),
        }),
        repeat_which: *rng.pick(&[Which::Props, Which::Targets]),
        point_doubt: *rng.pick(&[
            PointDoubt::Decided,
            PointDoubt::Decided,
            PointDoubt::GateTrue,
            PointDoubt::GateFalse,
            PointDoubt::GateOr,
            PointDoubt::PathRefused,
        ]),
        repeats: (0..[0, 1, 1, 2][rng.below(4)])
            .map(|_| Repeat {
                target: *rng.pick(&[
                    RepeatTarget::File,
                    RepeatTarget::Child,
                    RepeatTarget::Grandchild,
                ]),
                site: *rng.pick(&[
                    RepeatSite::Body,
                    RepeatSite::SdkBeforePoint,
                    RepeatSite::HiddenBeforePoint,
                    RepeatSite::HiddenViaSdkFile,
                    RepeatSite::SdkAfterPoint,
                    RepeatSite::InChild,
                    RepeatSite::InGrandchild,
                ]),
            })
            .collect(),
        gated: (rng.below(2) == 0)
            .then(|| GatedImport {
                site: *rng.pick(&[GatedSite::SdkProps, GatedSite::Body, GatedSite::SdkTargets]),
                input: *rng.pick(&[
                    GateInput::UnderUndecidedCondition,
                    GateInput::UnseededToolset,
                    GateInput::SdkTaintedOnly,
                    GateInput::SdkTaintedOnly,
                    GateInput::RefusedThenOverwritten,
                    GateInput::RefusedThenOverwritten,
                    GateInput::HiddenRewrite,
                ]),
                group: rng.below(2) == 0,
                taken: rng.below(2) == 0,
            })
            // An SDK-less project has no SDK file to write the import in.
            .filter(|g| g.site == GatedSite::Body || form != Form::SdkLess),
    }
}

/// The gated import written at `site`, with the writes that put its input in
/// doubt just before it, in the same file.
fn render_gated(case: &Case, site: GatedSite) -> String {
    let Some(g) = case.gated.filter(|g| g.site == site) else {
        return String::new();
    };
    // `$(GateX.Substring(0,1))` is `a` to MSBuild; the walk computes no
    // `Substring`.
    let writes = match g.input {
        GateInput::UnderUndecidedCondition => "  <PropertyGroup>\n    <GateX>abc</GateX>\n    \
             <GateIn>off</GateIn>\n    \
             <GateIn Condition=\"'$(GateX.Substring(0,1))' == 'a'\">on</GateIn>\n  \
             </PropertyGroup>\n"
            .to_owned(),
        GateInput::UnseededToolset => String::new(),
        GateInput::SdkTaintedOnly => {
            "  <PropertyGroup>\n    <GateIn>on</GateIn>\n  </PropertyGroup>\n  \
             <PropertyGroup Condition=\"'$(RoslynTargetsPath)' != 'zzz'\">\n    \
             <GateIn Condition=\"'$(GateIn)' == 'zzz'\">off</GateIn>\n  </PropertyGroup>\n"
                .to_owned()
        }
        GateInput::RefusedThenOverwritten => "  <PropertyGroup>\n    <GateX>abc</GateX>\n    \
             <GateIn>$(GateX.Substring(0,1))</GateIn>\n    <GateIn>on</GateIn>\n  \
             </PropertyGroup>\n"
            .to_owned(),
        GateInput::HiddenRewrite => "  <PropertyGroup>\n    <GateX>abc</GateX>\n    \
             <GateIn>off</GateIn>\n  </PropertyGroup>\n  \
             <Import Project=\"$(MSBuildProjectDirectory)/../gate-rewrite.props\" \
             Condition=\"'$(GateX.Substring(0,1))' == 'a'\" />\n"
            .to_owned(),
    };
    let condition = match (g.input, g.taken) {
        (GateInput::UnseededToolset, true) => "'$(RoslynTargetsPath)' != ''",
        (GateInput::UnseededToolset, false) => "'$(RoslynTargetsPath)' == ''",
        (_, true) => "'$(GateIn)' == 'on'",
        (_, false) => "'$(GateIn)' == 'off'",
    };
    let path = "$(MSBuildProjectDirectory)/../gated.props";
    let import = if g.group {
        format!(
            "  <ImportGroup Condition=\"{condition}\">\n    <Import Project=\"{path}\" />\n  \
             </ImportGroup>\n"
        )
    } else {
        format!("  <Import Project=\"{path}\" Condition=\"{condition}\" />\n")
    };
    format!("{writes}{import}")
}

/// The file a repeat imports, as a path an import anywhere in the case
/// spells it by.
fn repeat_path(case: &Case, r: &Repeat) -> String {
    let ext = ext(case.repeat_which);
    let file = match r.target {
        RepeatTarget::File => format!("Directory.Build.{ext}"),
        RepeatTarget::Child => format!("child.{ext}"),
        RepeatTarget::Grandchild => format!("grandchild.{ext}"),
    };
    format!("$(MSBuildProjectDirectory)/../{file}")
}

/// The name, beside the SDK's files, of the file through which the `i`th
/// repeat imports its file when it is [`RepeatSite::HiddenViaSdkFile`].
fn via_file(case: &Case, i: usize) -> &'static str {
    match (i, case.repeat_which) {
        (0, Which::Props) => "Via0.props",
        (0, Which::Targets) => "Via0.targets",
        (1, Which::Props) => "Via1.props",
        (1, Which::Targets) => "Via1.targets",
        _ => panic!("a case has at most two repeats"),
    }
}

/// The SDK's `Via<i>` files, one for each [`RepeatSite::HiddenViaSdkFile`]
/// repeat: each imports the repeat's file as an unhidden repeat would.
fn via_files(case: &Case) -> Vec<(&'static str, String)> {
    case.repeats
        .iter()
        .enumerate()
        .filter(|(_, r)| r.site == RepeatSite::HiddenViaSdkFile)
        .map(|(i, r)| {
            let path = repeat_path(case, r);
            (
                via_file(case, i),
                format!(
                    "<Project>\n  <Import Project=\"{path}\" Condition=\"Exists('{path}')\" />\n</Project>\n"
                ),
            )
        })
        .collect()
}

fn ext(which: Which) -> &'static str {
    match which {
        Which::Props => "props",
        Which::Targets => "targets",
    }
}

/// The repeats written at `site`, each between its `Seen` reset and copy.
fn repeats_at(case: &Case, site: RepeatSite) -> String {
    case.repeats
        .iter()
        .enumerate()
        .filter(|(_, r)| r.site == site)
        .map(|(i, r)| {
            let path = match r.site {
                RepeatSite::HiddenViaSdkFile => {
                    format!("$(MSBuildThisFileDirectory){}", via_file(case, i))
                }
                _ => repeat_path(case, r),
            };
            let (hide, condition) = if r.is_hidden() {
                (
                    "    <UndecidedX>abc</UndecidedX>\n",
                    format!("Exists('{path}') and '$(UndecidedX.Substring(0,1))' == 'a'"),
                )
            } else {
                ("", format!("Exists('{path}')"))
            };
            format!(
                "  <PropertyGroup>\n{hide}    <Seen>pre{i}</Seen>\n    <SeenChild>pre{i}</SeenChild>\n    \
                 <SeenGrandchild>pre{i}</SeenGrandchild>\n  </PropertyGroup>\n  \
                 <Import Project=\"{path}\" Condition=\"{condition}\" />\n  \
                 <PropertyGroup>\n    <Repeat{i}>$(Seen)</Repeat{i}>\n    \
                 <Repeat{i}Child>$(SeenChild)</Repeat{i}Child>\n    \
                 <Repeat{i}Grandchild>$(SeenGrandchild)</Repeat{i}Grandchild>\n  </PropertyGroup>\n"
            )
        })
        .collect()
}

/// `Directory.Build.*`'s import of `child`, when the case has repeats.
fn child_import(case: &Case, which: Which) -> String {
    if case.repeats.is_empty() || case.repeat_which != which {
        return String::new();
    }
    format!(
        "  <PropertyGroup>\n    <Seen>{}</Seen>\n  </PropertyGroup>\n  \
         <Import Project=\"$(MSBuildProjectDirectory)/../child.{}\" />\n",
        match which {
            Which::Props => "dbp",
            Which::Targets => "dbt",
        },
        ext(which)
    )
}

/// Put the point of `case.repeat_which` in doubt in an SDK file's `text`.
fn doubt_point(case: &Case, text: String) -> String {
    let name = match case.repeat_which {
        Which::Props => "DirectoryBuildPropsPath",
        Which::Targets => "DirectoryBuildTargetsPath",
    };
    let file = match case.repeat_which {
        Which::Props => "_DirectoryBuildPropsFile",
        Which::Targets => "_DirectoryBuildTargetsFile",
    };
    let base = match case.repeat_which {
        Which::Props => "_DirectoryBuildPropsBasePath",
        Which::Targets => "_DirectoryBuildTargetsBasePath",
    };
    let gate = |conjunct: &str| {
        text.replace(
            &format!("exists('$({name})')\"/>"),
            &format!("exists('$({name})') and {conjunct}\"/>"),
        )
    };
    match case.point_doubt {
        PointDoubt::Decided => text,
        PointDoubt::GateTrue => gate("$([System.String]::IsNullOrWhiteSpace(''))"),
        PointDoubt::GateFalse => gate("$([System.String]::IsNullOrWhiteSpace('no'))"),
        PointDoubt::GateOr => text.replace(
            &format!("exists('$({name})')\"/>"),
            &format!("($([System.String]::IsNullOrWhiteSpace('')) Or exists('$({name})'))\"/>"),
        ),
        PointDoubt::PathRefused => {
            let combine =
                format!("$([System.IO.Path]::Combine('$({base})', '$({file})'))</{name}>");
            if !text.contains(&combine) {
                return text;
            }
            text.replace(
                &combine,
                &format!(
                    "$([System.IO.Path]::Combine('$({base})', '$({file})'))$(UndecidedX.Substring(0,0))</{name}>"
                ),
            )
            .replacen(
                "<Project>\n",
                "<Project>\n  <PropertyGroup><UndecidedX>abc</UndecidedX></PropertyGroup>\n",
                1,
            )
        }
    }
}

/// `undecided`'s write, as a property group, when it sits at `site`.
/// The `(name, value MSBuild ends with, value the walk holds when it cannot
/// see the redefinition)` of an [`Undecided`] write.
fn undecided_write(u: Undecided) -> (&'static str, &'static str, &'static str) {
    match u.input {
        ImportInput::PropsGate => ("ImportDirectoryBuildProps", "false", "true"),
        ImportInput::PropsPath => (
            "DirectoryBuildPropsPath",
            "$(MSBuildProjectDirectory)/../other.props",
            "$(MSBuildProjectDirectory)/../Directory.Build.props",
        ),
        ImportInput::TargetsGate => ("ImportDirectoryBuildTargets", "false", "true"),
        ImportInput::TargetsPath => (
            "DirectoryBuildTargetsPath",
            "$(MSBuildProjectDirectory)/../other.props",
            "$(MSBuildProjectDirectory)/../Directory.Build.targets",
        ),
    }
}

/// For [`UndecidedHow::RefusedThenStale`], `Sdk.props`'s definition of
/// `UndecidedStale` and the import that redefines it, which the walk cannot
/// decide (`Stale.props`, beside it).
fn render_stale_source(case: &Case) -> String {
    match case.undecided {
        Some(u) if u.how == UndecidedHow::RefusedThenStale => {
            let (_, _, stale) = undecided_write(u);
            format!(
                "  <PropertyGroup>\n    <UndecidedX>abc</UndecidedX>\n    \
                 <UndecidedStale>{stale}</UndecidedStale>\n  </PropertyGroup>\n  \
                 <Import Project=\"$(MSBuildThisFileDirectory)Stale.props\" \
                 Condition=\"'$(UndecidedX.Substring(0,1))' == 'a'\" />\n"
            )
        }
        _ => String::new(),
    }
}

fn render_undecided(case: &Case, site: UndecidedSite) -> String {
    let Some(u) = case.undecided.filter(|u| u.site == site) else {
        return String::new();
    };
    let (name, value, _) = undecided_write(u);
    // `$(UndecidedX.Substring(0,1))` is `a` to MSBuild; the walk computes no
    // `Substring`.
    let write = match u.how {
        UndecidedHow::UnderUndecidedCondition => format!(
            "    <{name} Condition=\"'$(UndecidedX.Substring(0,1))' == 'a'\">{value}</{name}>\n"
        ),
        UndecidedHow::RefusedThenOverwritten => format!(
            "    <{name}>$(UndecidedX.Substring(0,1))</{name}>\n    <{name}>{value}</{name}>\n"
        ),
        UndecidedHow::RefusedThenStale => format!(
            "    <{name}>$(UndecidedX.Substring(0,1))</{name}>\n    <{name}>$(UndecidedStale)</{name}>\n"
        ),
    };
    format!("  <PropertyGroup>\n    <UndecidedX>abc</UndecidedX>\n{write}  </PropertyGroup>\n")
}

// ---------------------------------------------------------------------------
// Rendering.
// ---------------------------------------------------------------------------

/// A file's marker: appended to `Trace`, and the target `T` and `T_<marker>`.
/// Every file declares the reference `refs/<marker>.fsproj`, so the reference
/// list logs which files ran. A user's file also contributes the Compile item
/// `<marker>.fs`, so the Compile set logs which of the user's files ran, and,
/// unless it is the project, removes the project's reference
/// ([`BODY_REFERENCE`]). So a user's file that runs after the body strips it,
/// which no SDK file here does: the project's reference survives exactly when
/// no such file runs (#848). An SDK's files contribute no Compile item, so
/// that the Compile set logs the user's files alone. Every file appends the
/// define `D_<marker>`, so the define set logs which files ran too, the SDK's
/// own among them: content the walk cannot see may write a define whether it
/// is an SDK's file or a user's (#843, #862).
fn tracer(marker: &str) -> String {
    let user = if SDK_MARKERS.contains(&marker) {
        String::new()
    } else {
        let remove = if marker == "body" {
            String::new()
        } else {
            format!("    <ProjectReference Remove=\"{BODY_REFERENCE}\" />\n")
        };
        format!("    <Compile Include=\"{marker}.fs\" />\n{remove}")
    };
    format!(
        "  <PropertyGroup>\n    <Trace>$(Trace);{marker}</Trace>\n    \
         <DefineConstants>$(DefineConstants);D_{marker}</DefineConstants>\n  </PropertyGroup>\n  \
         <ItemGroup>\n    <ProjectReference Include=\"refs/{marker}.fsproj\" />\n{user}  \
         </ItemGroup>\n  <Target Name=\"T\" />\n  <Target Name=\"T_{marker}\" />\n"
    )
}

/// The project's own reference, which every other user's file removes.
const BODY_REFERENCE: &str = "refs/body.fsproj";

/// The markers of the SDK's own files.
const SDK_MARKERS: [&str; 6] = ["sdkp", "common", "sdkt", "sdkt2", "behindp", "behindt"];

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
/// `<case>` and `<case>/proj`; `<case>/proj/far` is a symlink to
/// `<case>/decoy/x/y`.
fn reimport_path(which: Which, spelling: Spelling) -> String {
    let ext = match which {
        Which::Props => "props",
        Which::Targets => "targets",
    };
    match spelling {
        Spelling::DotDot => format!("$(MSBuildProjectDirectory)/../proj/../Directory.Build.{ext}"),
        Spelling::LinkDotDot => {
            format!("$(MSBuildProjectDirectory)/far/../../Directory.Build.{ext}")
        }
        Spelling::Case => format!("$(MSBuildProjectDirectory)/../DIRECTORY.build.{ext}"),
        Spelling::DirLink => format!("$(MSBuildProjectDirectory)/up/Directory.Build.{ext}"),
        Spelling::FileLink => format!("$(MSBuildProjectDirectory)/alias.{ext}"),
        Spelling::Relative => format!("rel.{ext}"),
        Spelling::RelativeElsewhere => format!("relx.{ext}"),
    }
}

fn render_reimport(r: &Reimport, sdk: &str) -> String {
    let path = if r.shape == Shape::ViaPropertySdk {
        // `<root>/Sdks/S<n>/Sdk` to `<root>/case<n>`.
        let ext = match r.which {
            Which::Props => "props",
            Which::Targets => "targets",
        };
        format!("../../../case{}/Directory.Build.{ext}", &sdk[1..])
    } else {
        reimport_path(r.which, r.spelling)
    };
    match r.shape {
        Shape::Literal => {
            format!("  <Import Project=\"{path}\" Condition=\"Exists('{path}')\" />\n")
        }
        Shape::ViaProperty
        | Shape::PropertyOnly
        | Shape::ViaPropertySdk
        | Shape::ViaPropertySdkAbsolute => {
            let name = match r.which {
                Which::Props => "DirectoryBuildPropsPath",
                Which::Targets => "DirectoryBuildTargetsPath",
            };
            let write =
                format!("  <PropertyGroup>\n    <{name}>{path}</{name}>\n  </PropertyGroup>\n");
            let qualifier = if matches!(
                r.shape,
                Shape::ViaPropertySdk | Shape::ViaPropertySdkAbsolute
            ) {
                format!(" Sdk=\"{sdk}\"")
            } else {
                String::new()
            };
            if r.shape == Shape::PropertyOnly {
                write
            } else {
                format!(
                    "{write}  <Import{qualifier} Project=\"$({name})\" Condition=\"exists('$({name})')\" />\n"
                )
            }
        }
    }
}

fn reimports_at(case: &Case, site: Site, sdk: &str) -> String {
    case.reimports
        .iter()
        .filter(|r| r.site == site)
        .map(|r| render_reimport(r, sdk))
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
    sdk_props.push_str(&render_stale_source(case));
    sdk_props.push_str(&reimports_at(case, Site::SdkPropsBeforePoint, sdk));
    sdk_props.push_str(&render_undecided(case, UndecidedSite::SdkProps));
    if case.repeat_which == Which::Props {
        sdk_props.push_str(&repeats_at(case, RepeatSite::SdkBeforePoint));
        sdk_props.push_str(&repeats_at(case, RepeatSite::HiddenBeforePoint));
        sdk_props.push_str(&repeats_at(case, RepeatSite::HiddenViaSdkFile));
    }
    let mut sdk_files = via_files(case);
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
        PropsPoint::BehindUndecidedImport => {
            sdk_props.push_str(
                "  <PropertyGroup><UndecidedX>abc</UndecidedX></PropertyGroup>\n  \
                 <Import Project=\"$(MSBuildThisFileDirectory)Behind.props\" \
                 Condition=\"'$(UndecidedX.Substring(0,1))' == 'a'\" />\n",
            );
            sdk_files.push((
                "Behind.props",
                format!(
                    "<Project>\n{}{}</Project>\n",
                    tracer("behindp"),
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
    sdk_props.push_str(&reimports_at(case, Site::SdkProps, sdk));
    if case.repeat_which == Which::Props {
        sdk_props.push_str(&repeats_at(case, RepeatSite::SdkAfterPoint));
    }
    sdk_props.push_str(&render_gated(case, GatedSite::SdkProps));
    sdk_props.push_str("</Project>\n");
    sdk_files.push(("Sdk.props", sdk_props));

    // Sdk.targets.
    let mut sdk_targets = String::from("<Project>\n");
    sdk_targets.push_str(&tracer("sdkt"));
    if case.targets_point != TargetsPoint::InImportGroup {
        sdk_targets
            .push_str("  <Import Project=\"$(MSBuildThisFileDirectory)Helper.targets\" />\n");
    }
    if let Some(u) = case.undecided {
        let (_, value, _) = undecided_write(u);
        sdk_files.push((
            "Stale.props",
            format!(
                "<Project>\n  <PropertyGroup>\n    <UndecidedStale>{value}</UndecidedStale>\n  \
                 </PropertyGroup>\n</Project>\n"
            ),
        ));
    }
    sdk_files.push((
        "Helper.targets",
        format!(
            "<Project>\n{}</Project>\n",
            render_undecided(case, UndecidedSite::SdkTargetsHelper)
        ),
    ));
    if case.repeat_which == Which::Targets {
        sdk_targets.push_str(&repeats_at(case, RepeatSite::SdkBeforePoint));
        sdk_targets.push_str(&repeats_at(case, RepeatSite::HiddenBeforePoint));
        sdk_targets.push_str(&repeats_at(case, RepeatSite::HiddenViaSdkFile));
    }
    match case.targets_point {
        TargetsPoint::Absent => {}
        TargetsPoint::Standard => sdk_targets.push_str(&targets_block(STANDARD_TARGETS_CONDITION)),
        TargetsPoint::ConditionFalse => sdk_targets.push_str(&targets_block(
            "'false' == 'true' and exists('$(DirectoryBuildTargetsPath)')",
        )),
        TargetsPoint::GateWrittenByProps => sdk_targets.push_str(&targets_block(
            "'$(DemoGate)' == 'on' and exists('$(DirectoryBuildTargetsPath)')",
        )),
        TargetsPoint::BehindUndecidedImport => {
            sdk_targets.push_str(
                "  <PropertyGroup><UndecidedX>abc</UndecidedX></PropertyGroup>\n  \
                 <Import Project=\"$(MSBuildThisFileDirectory)Behind.targets\" \
                 Condition=\"'$(UndecidedX.Substring(0,1))' == 'a'\" />\n",
            );
            sdk_files.push((
                "Behind.targets",
                format!(
                    "<Project>\n{}{}</Project>\n",
                    tracer("behindt"),
                    targets_block(STANDARD_TARGETS_CONDITION)
                ),
            ));
        }
        TargetsPoint::InImportGroup => {
            let import = format!(
                "  <Import Project=\"$(DirectoryBuildTargetsPath)\" Condition=\"{STANDARD_TARGETS_CONDITION}\"/>\n"
            );
            let block = targets_block(STANDARD_TARGETS_CONDITION);
            assert!(block.contains(&import), "the block ends in its import");
            sdk_targets.push_str(&block.replace(
                &import,
                &format!(
                    "  <ImportGroup Condition=\"'true' == 'true'\">\n  \
                     <Import Project=\"$(MSBuildThisFileDirectory)Helper.targets\" />\n{import}  </ImportGroup>\n"
                ),
            ));
        }
    }
    sdk_targets.push_str(&reimports_at(case, Site::SdkTargets, sdk));
    if case.repeat_which == Which::Targets {
        sdk_targets.push_str(&repeats_at(case, RepeatSite::SdkAfterPoint));
    }
    sdk_targets.push_str(&render_gated(case, GatedSite::SdkTargets));
    sdk_targets.push_str(&tracer("sdkt2"));
    sdk_targets.push_str("</Project>\n");
    sdk_files.push(("Sdk.targets", sdk_targets));
    let sdk_files: Vec<(&'static str, String)> = sdk_files
        .into_iter()
        .map(|(name, text)| (name, doubt_point(case, text)))
        .collect();

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
        if case.props.probes_exists {
            text.push_str(
                "    <ExistsElementProbe Condition=\"Exists('p.proj')\">1</ExistsElementProbe>\n",
            );
        }
        text.push_str("  </PropertyGroup>\n");
        text.push_str(&child_import(case, Which::Props));
        if case.props.probes_exists {
            text.push_str(
                "  <PropertyGroup Condition=\"Exists('p.proj')\">\n    \
                 <ExistsGroupProbe>1</ExistsGroupProbe>\n  </PropertyGroup>\n  \
                 <Choose>\n    <When Condition=\"Exists('p.proj')\">\n      \
                 <PropertyGroup><ExistsProbe>1</ExistsProbe></PropertyGroup>\n    \
                 </When>\n  </Choose>\n",
            );
        }
        text.push_str("</Project>\n");
        case_files.push(("Directory.Build.props", text));
    }
    case_files.push((
        "other.props",
        format!(
            "<Project>\n{}  <PropertyGroup>\n    <InOther>1</InOther>\n  </PropertyGroup>\n</Project>\n",
            tracer("other")
        ),
    ));
    if case.gated.is_some() {
        case_files.push((
            "gated.props",
            format!("<Project>\n{}</Project>\n", tracer("gated")),
        ));
        case_files.push((
            "gate-rewrite.props",
            "<Project>\n  <PropertyGroup>\n    <GateIn>on</GateIn>\n  </PropertyGroup>\n</Project>\n"
                .to_owned(),
        ));
    }
    if case.targets_present {
        let mut text = String::from("<Project>\n");
        text.push_str(&tracer("dbt"));
        text.push_str("  <PropertyGroup>\n    <InDbt>1</InDbt>\n  </PropertyGroup>\n");
        text.push_str(&child_import(case, Which::Targets));
        text.push_str(&reimports_at(case, Site::DirectoryBuildTargets, sdk));
        text.push_str("</Project>\n");
        case_files.push(("Directory.Build.targets", text));
    }

    if !case.repeats.is_empty() {
        let ext = ext(case.repeat_which);
        let child = format!(
            "<Project>\n{}  <PropertyGroup>\n    <Seen>child</Seen>\n    <SeenChild>child</SeenChild>\n  </PropertyGroup>\n  \
             <Import Project=\"$(MSBuildProjectDirectory)/../grandchild.{ext}\" />\n{}</Project>\n",
            tracer("child"),
            repeats_at(case, RepeatSite::InChild)
        );
        let grandchild = format!(
            "<Project>\n{}  <PropertyGroup>\n    <Seen>grandchild</Seen>\n    <SeenGrandchild>grandchild</SeenGrandchild>\n  </PropertyGroup>\n{}</Project>\n",
            tracer("grandchild"),
            repeats_at(case, RepeatSite::InGrandchild)
        );
        let (child_name, grandchild_name) = match case.repeat_which {
            Which::Props => ("child.props", "grandchild.props"),
            Which::Targets => ("child.targets", "grandchild.targets"),
        };
        case_files.push((child_name, child));
        case_files.push((grandchild_name, grandchild));
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
    body.push_str(&reimports_at(case, Site::Body, sdk));
    body.push_str(&repeats_at(case, RepeatSite::Body));
    body.push_str(&render_gated(case, GatedSite::Body));
    let disable_props = format!(
        "{}{}",
        if case.body_disables_props_import {
            "  <PropertyGroup>\n    <ImportDirectoryBuildProps>false</ImportDirectoryBuildProps>\n  </PropertyGroup>\n"
        } else {
            ""
        },
        render_undecided(case, UndecidedSite::Body)
    );
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
    /// #820's remainder: an import point in or after content the walk cannot
    /// see whose failure ([`PointDoubt::GateOr`] over a missing file) makes
    /// MSBuild reject an evaluation the walk cannot know is rejected. Covers findings
    /// against a rejected project only.
    HiddenPointRejectsTheProject,
}

const KNOWN_DIVERGENCES: &[Family] = &[Family::HiddenPointRejectsTheProject];

impl Family {
    /// Whether `case` is in the family: decided from the case's shape alone,
    /// never from how the walk answered it.
    fn contains(self, case: &Case) -> bool {
        match self {
            Family::HiddenPointRejectsTheProject => {
                case.point_doubt == PointDoubt::GateOr && case.hides_content_from_the_walk()
            }
        }
    }

    /// Whether the family explains `finding`, in a case it contains.
    fn covers(self, finding: &Finding) -> bool {
        match self {
            Family::HiddenPointRejectsTheProject => finding.theirs == "a rejected project",
        }
    }

    /// A case the family's divergence is known to show in, which the test
    /// asserts still diverges.
    fn witness(self) -> Case {
        match self {
            // The targets point is behind an import the walk cannot decide,
            // and imports its path whether or not the file exists. `Sdk.targets`
            // sets `Seen` after it, a literal the walk commits.
            Family::HiddenPointRejectsTheProject => Case {
                targets_point: TargetsPoint::BehindUndecidedImport,
                targets_present: false,
                point_doubt: PointDoubt::GateOr,
                repeats: vec![Repeat {
                    target: RepeatTarget::File,
                    site: RepeatSite::SdkAfterPoint,
                }],
                ..Case::usual()
            },
        }
    }
}

impl Case {
    /// Whether the case holds an import the walk cannot decide, apart from
    /// the import points' own doubt: content the walk cannot see.
    fn hides_content_from_the_walk(&self) -> bool {
        self.undecided.is_some()
            || self.props_point == PropsPoint::BehindUndecidedImport
            || self.targets_point == TargetsPoint::BehindUndecidedImport
            || self.has_hidden_repeat()
            || self.gated.is_some_and(GatedImport::undecided_to_the_walk)
    }

    /// Whether content the walk cannot see imports a file the point reaches.
    fn has_hidden_repeat(&self) -> bool {
        self.repeats.iter().any(Repeat::is_hidden)
    }

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
            undecided: None,
            repeat_which: Which::Targets,
            point_doubt: PointDoubt::Decided,
            repeats: Vec::new(),
            gated: None,
        }
    }

    /// The properties the walk has no reason to decline here. Every import
    /// condition in the case is a literal or reads a literal some file wrote,
    /// every path is one the walk can spell, and nothing reads the
    /// environment, so the log of which files ran and the markers they wrote
    /// are all decided.
    ///
    /// A case with an [`Undecided`] write has no such obligation: that write
    /// may decide every import that follows it. Nor has a case whose import
    /// point is behind an import the walk cannot decide: what the hidden file
    /// writes is the walk's to doubt. Nor has a case with a gated import: its
    /// gate reads a value the walk doubts, so the walk may settle a
    /// `Directory.Build.*` import point it never reaches as undecided.
    fn must_commit(&self) -> &'static [&'static str] {
        if self.undecided.is_some()
            || self.has_hidden_repeat()
            || self.point_doubt != PointDoubt::Decided
            || self.props_point == PropsPoint::BehindUndecidedImport
            || self.targets_point == TargetsPoint::BehindUndecidedImport
            || self.gated.is_some()
        {
            &[]
        } else {
            &["Trace", "BodySaw", "InDbp", "InDbt", "InOther"]
        }
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
    kind: FindingKind,
}

/// What a [`Finding`] is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FindingKind {
    Property,
    Target,
    Compile,
    References,
    Defines,
    /// A rejection the walk claims (`RejectionCertainty::Certain`) of a
    /// project MSBuild evaluates.
    Rejection,
}

/// What one case came to.
#[derive(Debug, Default)]
struct Outcome {
    findings: Vec<Finding>,
    /// MSBuild rejected the project.
    rejected: bool,
    /// The walk claims MSBuild rejects the project, and it does.
    claimed_rejection: bool,
    committed_properties: usize,
    /// The properties the walk committed, graded against MSBuild.
    committed: Vec<&'static str>,
    exact_targets: usize,
    /// The walk called the Compile set certain (and MSBuild accepted the
    /// project).
    certain_compile: bool,
    /// The walk called the reference list certain (and MSBuild accepted the
    /// project).
    certain_references: bool,
    /// Of those, whether MSBuild's list holds the project's own reference: no
    /// file that runs after the body stripped it.
    body_reference_kept: bool,
    /// The walk called the define set certain (and MSBuild accepted the
    /// project).
    certain_defines: bool,
    /// Of those, whether MSBuild's set holds a define from a user's file
    /// other than the project.
    other_user_define: bool,
    /// Whether MSBuild imported `Directory.Build.props` and `.targets`, read
    /// off the markers they write.
    msbuild_imported: Option<(bool, bool)>,
    /// Whether MSBuild ran `gated.props`, read off its marker in `Trace`.
    msbuild_ran_gated: bool,
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
    // `proj/far/../..` is `<case>` to MSBuild and `<case>/decoy` to the file
    // system, where each `Directory.Build.*` is an empty project.
    std::fs::create_dir_all(case_dir.join("decoy/x/y")).expect("mkdir decoy");
    for ext in ["props", "targets"] {
        std::fs::write(
            case_dir.join(format!("decoy/Directory.Build.{ext}")),
            "<Project />",
        )
        .expect("write decoy");
    }
    symlink(Path::new("../decoy/x/y"), &case_dir.join("proj/far"));
    symlink(
        Path::new("../Directory.Build.props"),
        &case_dir.join("proj/alias.props"),
    );
    symlink(
        Path::new("../Directory.Build.targets"),
        &case_dir.join("proj/alias.targets"),
    );
    for dir in [sdk_dir.as_path(), case_dir.as_path()] {
        symlink(
            &case_dir.join("Directory.Build.props"),
            &dir.join("relx.props"),
        );
        symlink(
            &case_dir.join("Directory.Build.targets"),
            &dir.join("relx.targets"),
        );
    }
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
    let (parsed, ours) = parse_fsproj_reads(
        &rendered.project,
        &project_path,
        &HashMap::new(),
        &environment,
        Some(&resolver),
        None,
        None,
        &probe,
    )
    .expect("well-formed XML parses");
    let theirs = shared.oracle.try_evaluated(
        &project_path,
        &[],
        &PROPERTIES,
        &["Compile", "ProjectReference"],
        &TARGETS,
    );

    let mut outcome = Outcome::default();
    let mut describe = format!("{case:#?}\n--- p.proj\n{}", rendered.project);
    for (name, text) in rendered.sdk_files.iter().chain(&rendered.case_files) {
        describe.push_str(&format!("--- {name}\n{text}"));
    }
    let claims_rejection =
        parsed.rejection.as_ref().map(|r| r.certainty) == Some(RejectionCertainty::Certain);
    let Some(theirs) = theirs else {
        // MSBuild refuses the project, so any value the walk commits is one no
        // build holds.
        outcome.rejected = true;
        outcome.claimed_rejection = claims_rejection;
        if !parsed.items_uncertain {
            outcome.findings.push(Finding {
                what: "Compile".to_owned(),
                ours: "a certain item set".to_owned(),
                theirs: "a rejected project".to_owned(),
                kind: FindingKind::Compile,
            });
        }
        if !parsed.project_references_uncertain {
            outcome.findings.push(Finding {
                what: "ProjectReference".to_owned(),
                ours: "a certain reference list".to_owned(),
                theirs: "a rejected project".to_owned(),
                kind: FindingKind::References,
            });
        }
        if !parsed.define_constants_uncertain {
            outcome.findings.push(Finding {
                what: "define_constants".to_owned(),
                ours: "a certain define set".to_owned(),
                theirs: "a rejected project".to_owned(),
                kind: FindingKind::Defines,
            });
        }
        for name in PROPERTIES {
            if let read @ (PropertyRead::Value(_) | PropertyRead::Unset) = &ours.properties[name] {
                outcome.findings.push(Finding {
                    what: name.to_owned(),
                    ours: format!("{read:?}"),
                    theirs: "a rejected project".to_owned(),
                    kind: FindingKind::Property,
                });
            }
        }
        let _ = std::fs::remove_dir_all(&case_dir);
        let _ = std::fs::remove_dir_all(sdk_dir.parent().unwrap());
        return (outcome, describe);
    };
    if claims_rejection {
        outcome.findings.push(Finding {
            what: "the project".to_owned(),
            ours: format!("a certain rejection: {:?}", parsed.rejection),
            theirs: "an evaluated project".to_owned(),
            kind: FindingKind::Rejection,
        });
    }
    outcome.msbuild_imported = Some((
        !theirs["properties"]["InDbp"].is_null(),
        !theirs["properties"]["InDbt"].is_null(),
    ));
    outcome.msbuild_ran_gated = theirs["properties"]["Trace"]
        .as_str()
        .is_some_and(|trace| trace.split(';').any(|marker| marker == "gated"));
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
                        kind: FindingKind::Property,
                    });
                }
                continue;
            }
        };
        outcome.committed_properties += 1;
        outcome.committed.push(name);
        if let Some(ours) = committed {
            outcome.findings.push(Finding {
                what: name.to_owned(),
                ours,
                theirs: theirs.to_string(),
                kind: FindingKind::Property,
            });
        }
    }
    // A Compile set the walk calls certain must be MSBuild's, file for file
    // and in order: that is what the LSP folds. MSBuild's identity is the
    // `Include` as written, relative to the project's directory wherever the
    // item was declared.
    if !parsed.items_uncertain {
        outcome.certain_compile = true;
        let project_dir = project_path.parent().expect("a project has a directory");
        let ours: Vec<PathBuf> = parsed
            .items
            .iter()
            .filter(|item| item.kind == borzoi_msbuild::ItemKind::Compile)
            .map(|item| item.include.clone())
            .collect();
        let theirs: Vec<PathBuf> = theirs["items"]["Compile"]
            .as_array()
            .expect("the Compile items")
            .iter()
            .map(|item| project_dir.join(item["identity"].as_str().expect("an identity")))
            .collect();
        if ours != theirs {
            outcome.findings.push(Finding {
                what: "Compile".to_owned(),
                ours: format!("{ours:?}"),
                theirs: format!("{theirs:?}"),
                kind: FindingKind::Compile,
            });
        }
    }
    // So must a reference list the walk calls certain: the LSP's project graph
    // reads it as the edges MSBuild builds. Identities are relative to the
    // project's directory, as the Compile items' are.
    if !parsed.project_references_uncertain {
        outcome.certain_references = true;
        let project_dir = project_path.parent().expect("a project has a directory");
        let ours: Vec<PathBuf> = parsed
            .project_references
            .iter()
            .map(|item| item.include.clone())
            .collect();
        let theirs: Vec<PathBuf> = theirs["items"]["ProjectReference"]
            .as_array()
            .expect("the ProjectReference items")
            .iter()
            .map(|item| project_dir.join(item["identity"].as_str().expect("an identity")))
            .collect();
        outcome.body_reference_kept = theirs.contains(&project_dir.join(BODY_REFERENCE));
        if ours != theirs {
            outcome.findings.push(Finding {
                what: "ProjectReference".to_owned(),
                ours: format!("{ours:?}"),
                theirs: format!("{theirs:?}"),
                kind: FindingKind::References,
            });
        }
    }
    // So must a define set the walk calls certain: the LSP parses every file
    // under it. MSBuild's list is its `DefineConstants` split on semicolons,
    // empty entries dropped; no marker needs escaping.
    if !parsed.define_constants_uncertain {
        outcome.certain_defines = true;
        let theirs: Vec<String> = theirs["properties"]["DefineConstants"]
            .as_str()
            .unwrap_or_default()
            .split(';')
            .map(str::trim)
            .filter(|define| !define.is_empty())
            .map(str::to_owned)
            .collect();
        outcome.other_user_define = theirs.iter().any(|define| {
            define
                .strip_prefix("D_")
                .is_some_and(|marker| marker != "body" && !SDK_MARKERS.contains(&marker))
        });
        if parsed.define_constants != theirs {
            outcome.findings.push(Finding {
                what: "define_constants".to_owned(),
                ours: format!("{:?}", parsed.define_constants),
                theirs: format!("{theirs:?}"),
                kind: FindingKind::Defines,
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
                kind: FindingKind::Target,
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
        "{:?} pp={:?}{} tp={:?} dbp={}{}{}{}{} dbt={} body={}{}",
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
        if p.probes_exists { "/exists" } else { "" },
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
    if let Some(u) = case.undecided {
        s.push_str(&format!(" und[{:?} {:?} @{:?}]", u.input, u.how, u.site));
    }
    if case.point_doubt != PointDoubt::Decided {
        s.push_str(&format!(
            " doubt[{:?} {:?}]",
            case.repeat_which, case.point_doubt
        ));
    }
    for r in &case.repeats {
        s.push_str(&format!(
            " rep[{:?} {:?} {:?}]",
            case.repeat_which, r.target, r.site
        ));
    }
    if let Some(g) = case.gated {
        s.push_str(&format!(
            " gated[{:?} {:?}{}{}]",
            g.input,
            g.site,
            if g.group { " group" } else { "" },
            if g.taken { " taken" } else { "" }
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
        format!("props.probes_exists={}", case.props.probes_exists),
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
    keys.push(format!("point_doubt={:?}", case.point_doubt));
    for r in &case.repeats {
        keys.push(format!("repeat.target={:?}", r.target));
        keys.push(format!("repeat.site={:?}", r.site));
        keys.push(format!("repeat.with={:?}", case.point_doubt));
    }
    if let Some(g) = case.gated {
        keys.push(format!("gated.site={:?}", g.site));
        keys.push(format!("gated.input={:?}", g.input));
        keys.push(format!("gated.group={}", g.group));
        keys.push(format!("gated.taken={}", g.taken));
    }
    if let Some(u) = case.undecided {
        keys.push(format!("undecided.site={:?}", u.site));
        keys.push(format!("undecided.input={:?}", u.input));
        keys.push(format!("undecided.how={:?}", u.how));
    }
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
    /// Of those, the cases whose rejection the walk claims.
    claimed_rejections: usize,
    committed_properties: usize,
    exact_targets: usize,
    /// Cases whose Compile set the walk called certain, each graded.
    certain_compile: usize,
    /// Cases whose reference list the walk called certain, each graded, by
    /// whether MSBuild kept the project's own reference.
    certain_references: BTreeMap<bool, usize>,
    /// Cases whose define set the walk called certain, each graded, by
    /// whether MSBuild's set holds a define from a user's file other than the
    /// project.
    certain_defines: BTreeMap<bool, usize>,
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
        // Which re-imports reached a graded commit: the walk committed what
        // the import left in `Repeat<i>`, and MSBuild agreed or it is a
        // finding.
        for (i, r) in case.repeats.iter().enumerate() {
            let copies = [
                format!("Repeat{i}"),
                format!("Repeat{i}Child"),
                format!("Repeat{i}Grandchild"),
            ];
            if outcome
                .committed
                .iter()
                .any(|name| copies.iter().any(|copy| copy == name))
            {
                for key in [
                    format!("repeat_commit.site={:?}", r.site),
                    format!("repeat_commit.target={:?}", r.target),
                    format!("repeat_commit.with={:?}", case.point_doubt),
                ] {
                    *report.census.entry(key).or_default() += 1;
                }
            }
        }
        if let Some(g) = case.gated
            && outcome.certain_compile
            && outcome.certain_defines
        {
            let place = if g.site == GatedSite::Body {
                "user"
            } else {
                "sdk"
            };
            *report
                .census
                .entry(format!("gated_graded={:?}@{place}", g.input))
                .or_default() += 1;
        }
        report.cases += 1;
        report.rejected += usize::from(outcome.rejected);
        report.claimed_rejections += usize::from(outcome.claimed_rejection);
        report.committed_properties += outcome.committed_properties;
        report.exact_targets += outcome.exact_targets;
        report.certain_compile += usize::from(outcome.certain_compile);
        if outcome.certain_references {
            *report
                .certain_references
                .entry(outcome.body_reference_kept)
                .or_default() += 1;
        }
        if outcome.certain_defines {
            *report
                .certain_defines
                .entry(outcome.other_user_define)
                .or_default() += 1;
        }
        if families.is_empty() {
            report.outside_families += 1;
            if let Some(imported) = outcome.msbuild_imported {
                *report.outside_imports.entry(imported).or_default() += 1;
            }
        }
        if outcome.findings.is_empty() {
            continue;
        }
        let unexplained: Vec<&Finding> = outcome
            .findings
            .iter()
            .filter(|f| !families.iter().any(|family| family.covers(f)))
            .collect();
        if !unexplained.is_empty() {
            let findings: Vec<String> = unexplained
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
        "sdk import graph: {} cases, {} rejected ({} of them claimed), {} committed property reads, \
         {} exact target reads, {} certain Compile sets, certain reference lists by whether \
         MSBuild kept the project's own: {:?}, certain define sets by whether another user's \
         file defined one: {:?}; {} cases outside every family, MSBuild's (props, targets) \
         imports among them: {:?}; known-family cases with findings: {:?}",
        report.cases,
        report.rejected,
        report.claimed_rejections,
        report.committed_properties,
        report.exact_targets,
        report.certain_compile,
        report.certain_references,
        report.certain_defines,
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
    // The reference axis grades lists both ways: ones MSBuild strips the
    // project's reference from (a user's file ran after the body) and ones it
    // keeps it in, so a walk that declined every list, or every list a file
    // after the body touches, would fail here.
    for kept in [true, false] {
        let n = report.certain_references.get(&kept).copied().unwrap_or(0);
        assert!(
            n >= 30,
            "only {n} certain reference lists in which MSBuild {} the project's own",
            if kept { "kept" } else { "stripped" }
        );
    }
    // The define axis grades sets both ways: ones a user's file other than the
    // project wrote into (a `Directory.Build.*` file, or a file a re-import
    // reached) and ones only the SDK and the project did, so a walk that
    // declined every set another file touches would fail here.
    for other in [true, false] {
        let n = report.certain_defines.get(&other).copied().unwrap_or(0);
        assert!(
            n >= 40,
            "only {n} certain define sets {} a define from another user's file",
            if other { "with" } else { "without" }
        );
    }
    // MSBuild rejects only the dangling-symlink imports and the SDK-qualified
    // rooted ones: a case it rejects grades little, so a generator drifting
    // into rejected shapes would hollow the sweep out.
    assert!(
        report.rejected * 5 < report.cases,
        "MSBuild rejected {} of {} generated projects",
        report.rejected,
        report.cases
    );
    // The walk claims the rejections it reaches for certain, each graded.
    assert!(
        report.claimed_rejections >= 20,
        "the walk claims only {} rejections",
        report.claimed_rejections
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
        "props_point=BehindUndecidedImport",
        "second_props_point=true",
        "targets_point=Absent",
        "targets_point=Standard",
        "targets_point=ConditionFalse",
        "targets_point=GateWrittenByProps",
        "targets_point=InImportGroup",
        "targets_point=BehindUndecidedImport",
        "props.present=false",
        "props.disables_targets_import=true",
        "props.opens_demo_gate=true",
        "props.redirects_props_path=true",
        "props.probes_exists=true",
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
        "reimport.spelling=RelativeElsewhere",
        "reimport.shape=Literal",
        "reimport.shape=ViaProperty",
        "reimport.shape=PropertyOnly",
        "reimport.shape=ViaPropertySdk",
        "reimport.shape=ViaPropertySdkAbsolute",
        "reimport.site=SdkPropsBeforePoint",
        "reimport.site=SdkProps",
        "reimport.site=SdkTargets",
        "reimport.site=Body",
        "reimport.site=DirectoryBuildTargets",
        "undecided.site=SdkProps",
        "undecided.site=Body",
        "undecided.site=SdkTargetsHelper",
        "undecided.input=PropsGate",
        "undecided.input=PropsPath",
        "undecided.input=TargetsGate",
        "undecided.input=TargetsPath",
        "undecided.how=UnderUndecidedCondition",
        "undecided.how=RefusedThenOverwritten",
        "undecided.how=RefusedThenStale",
        "point_doubt=Decided",
        "point_doubt=GateTrue",
        "point_doubt=GateFalse",
        "point_doubt=GateOr",
        "point_doubt=PathRefused",
        "repeat.target=File",
        "repeat.target=Child",
        "repeat.target=Grandchild",
        "repeat.site=Body",
        "repeat.site=SdkBeforePoint",
        "repeat.site=HiddenBeforePoint",
        "repeat.site=HiddenViaSdkFile",
        "repeat.site=SdkAfterPoint",
        "repeat.site=InChild",
        "repeat.site=InGrandchild",
        "repeat.with=Decided",
        "repeat.with=GateTrue",
        "repeat.with=GateFalse",
        "repeat.with=GateOr",
        "repeat.with=PathRefused",
        "gated.site=SdkProps",
        "gated.site=Body",
        "gated.site=SdkTargets",
        "gated.input=UnderUndecidedCondition",
        "gated.input=UnseededToolset",
        "gated.input=SdkTaintedOnly",
        "gated.input=RefusedThenOverwritten",
        "gated.input=HiddenRewrite",
        "gated.group=true",
        "gated.group=false",
        "gated.taken=true",
        "gated.taken=false",
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
    // And each re-import shape reaches a commit the oracle grades. Only with
    // the point decided: an undecided point withdraws the whole evaluation,
    // so the walk commits nothing after it, by design; nor after content it
    // cannot see, so the hidden sites have no commit to reach either.
    let uncommitted: Vec<String> = [
        "repeat_commit.site=Body",
        "repeat_commit.site=SdkBeforePoint",
        "repeat_commit.site=SdkAfterPoint",
        "repeat_commit.site=InChild",
        "repeat_commit.site=InGrandchild",
        "repeat_commit.target=File",
        "repeat_commit.target=Child",
        "repeat_commit.target=Grandchild",
        "repeat_commit.with=Decided",
    ]
    .into_iter()
    .filter(|key| report.census.get(*key).copied().unwrap_or(0) < 3)
    .map(str::to_owned)
    .collect();
    assert!(
        uncommitted.is_empty(),
        "re-import shapes that reached a graded commit fewer than 3 times: {uncommitted:?}"
    );
    // And a gate the walk decides exactly though it reads a doubted value (an
    // SDK-tainted one, a refused-then-overwritten one) leaves the Compile and
    // define sets certain, so the sweep grades them against MSBuild. Taint
    // arises in an SDK file alone.
    let ungraded: Vec<String> = [
        "gated_graded=SdkTaintedOnly@sdk",
        "gated_graded=RefusedThenOverwritten@user",
        "gated_graded=RefusedThenOverwritten@sdk",
    ]
    .into_iter()
    .filter(|key| report.census.get(*key).copied().unwrap_or(0) < 3)
    .map(str::to_owned)
    .collect();
    assert!(
        ungraded.is_empty(),
        "gated inputs whose Compile and define sets were graded fewer than 3 times: {ungraded:?}"
    );
}

/// An import point whose `Exists` is a disjunct beside a term the walk cannot
/// evaluate, over a certain path to a missing file: MSBuild takes the term,
/// imports the missing file and rejects the project (MSB4019), so the walk
/// must commit nothing.
#[test]
fn an_or_exists_point_over_a_missing_file_commits_nothing() {
    let mut shared = Shared::new();
    let case = Case {
        targets_present: false,
        point_doubt: PointDoubt::GateOr,
        ..Case::usual()
    };
    let (outcome, describe) = evaluate(&mut shared, &case);
    assert!(
        outcome.rejected,
        "MSBuild accepted the project:\n{describe}"
    );
    assert!(
        outcome.findings.is_empty(),
        "{:#?}\n{describe}",
        outcome.findings
    );
}

/// Content the walk cannot see imports `Directory.Build.props`, and the SDK's
/// point imports it again, which MSBuild skips (import-graph soak seed 112233,
/// case 9706): the walk must not commit the order its own import would give.
#[test]
fn a_point_after_a_hidden_import_of_its_file_commits_no_order() {
    let mut shared = Shared::new();
    let case = Case {
        repeat_which: Which::Props,
        repeats: vec![Repeat {
            target: RepeatTarget::File,
            site: RepeatSite::HiddenBeforePoint,
        }],
        ..Case::usual()
    };
    let (outcome, describe) = evaluate(&mut shared, &case);
    assert!(
        !outcome.rejected,
        "MSBuild rejected the project:\n{describe}"
    );
    assert!(
        outcome.findings.is_empty(),
        "{:#?}\n{describe}",
        outcome.findings
    );
}

/// Grade `case`'s item lists and define set alone: MSBuild accepts the
/// project, and the walk publishes MSBuild's Compile set, reference list and
/// define set, or declines each. The sweep grades what the hidden import
/// writes.
fn assert_items_exact_or_declined(case: &Case) {
    let mut shared = Shared::new();
    let (outcome, describe) = evaluate(&mut shared, case);
    assert!(
        !outcome.rejected,
        "MSBuild rejected the project:\n{describe}"
    );
    let items: Vec<&Finding> = outcome
        .findings
        .iter()
        .filter(|f| {
            matches!(
                f.kind,
                FindingKind::Compile | FindingKind::References | FindingKind::Defines
            )
        })
        .collect();
    assert!(items.is_empty(), "{items:#?}\n{describe}");
}

/// #819: with no import point and no `Directory.Build.*` file, nothing
/// withdraws the evaluation. MSBuild runs `child` and `grandchild` once, in
/// `Sdk.props` behind the import the walk cannot decide, and skips the body's
/// import of `child` as a duplicate; the walk must not commit the order its
/// own import at the body would give.
#[test]
fn a_plain_import_after_a_hidden_import_of_its_file_commits_no_order() {
    assert_items_exact_or_declined(&Case {
        props_point: PropsPoint::Absent,
        targets_point: TargetsPoint::Absent,
        props: Props::default(),
        targets_present: false,
        repeat_which: Which::Props,
        repeats: vec![
            Repeat {
                target: RepeatTarget::Child,
                site: RepeatSite::HiddenBeforePoint,
            },
            Repeat {
                target: RepeatTarget::Child,
                site: RepeatSite::Body,
            },
        ],
        ..Case::usual()
    });
}

/// #848: with no `Directory.Build.*` file the point withdraws nothing, and
/// `child` (with `grandchild`), which strips the project's reference, is
/// imported only by an import in `Sdk.targets` the walk cannot decide, after
/// the body. MSBuild's list lacks the project's reference, which the walk must
/// not publish as certain.
#[test]
fn a_hidden_sdk_import_of_a_user_file_after_the_body_commits_no_reference_list() {
    for site in [RepeatSite::HiddenBeforePoint, RepeatSite::HiddenViaSdkFile] {
        assert_items_exact_or_declined(&Case {
            props: Props::default(),
            targets_point: TargetsPoint::Absent,
            targets_present: false,
            repeat_which: Which::Targets,
            repeats: vec![Repeat {
                target: RepeatTarget::Child,
                site,
            }],
            ..Case::usual()
        });
    }
}

/// #862: with no `Directory.Build.*` file the point withdraws nothing, and
/// the SDK's own `Behind.props`, which appends `D_behindp`, is imported only
/// under a gate the walk cannot decide. MSBuild's define set holds it; the
/// walk must not publish one without it as certain, though the hidden file is
/// the SDK's.
#[test]
fn a_hidden_sdk_file_commits_no_define_set() {
    assert_items_exact_or_declined(&Case {
        props_point: PropsPoint::BehindUndecidedImport,
        props: Props::default(),
        targets_present: false,
        ..Case::usual()
    });
}

/// #821: with no `Directory.Build.*` file the point withdraws nothing, and
/// `child` (with `grandchild`), whose Compile items MSBuild compiles, is
/// imported only by an import in `Sdk.props` the walk cannot decide.
#[test]
fn a_hidden_sdk_import_of_a_user_file_commits_no_compile_set() {
    for site in [RepeatSite::HiddenBeforePoint, RepeatSite::HiddenViaSdkFile] {
        assert_items_exact_or_declined(&Case {
            props: Props::default(),
            targets_present: false,
            repeat_which: Which::Props,
            repeats: vec![Repeat {
                target: RepeatTarget::Child,
                site,
            }],
            ..Case::usual()
        });
    }
}

/// Every gated import, on the usual SDK shape: MSBuild accepts each project,
/// and the walk publishes MSBuild's Compile set, reference list and define set,
/// or declines each, whichever way MSBuild takes the gate. Where the walk
/// decides the gate exactly (an input it holds exactly, though one an SDK file
/// marked tainted or one a refused write left marked), every value it commits
/// is MSBuild's too, and it commits the Compile and define sets: such a gate is
/// decided in every build.
#[test]
fn a_gate_reading_a_doubted_value_is_exact_or_declined_on_every_axis() {
    let mut shared = Shared::new();
    let mut failures = Vec::new();
    for site in [GatedSite::SdkProps, GatedSite::Body, GatedSite::SdkTargets] {
        for input in [
            GateInput::UnderUndecidedCondition,
            GateInput::UnseededToolset,
            GateInput::SdkTaintedOnly,
            GateInput::RefusedThenOverwritten,
            GateInput::HiddenRewrite,
        ] {
            for group in [false, true] {
                for taken in [false, true] {
                    let gated = GatedImport {
                        site,
                        input,
                        group,
                        taken,
                    };
                    let case = Case {
                        gated: Some(gated),
                        ..Case::usual()
                    };
                    let (outcome, describe) = evaluate(&mut shared, &case);
                    let findings: Vec<&Finding> = outcome
                        .findings
                        .iter()
                        .filter(|f| {
                            !gated.undecided_to_the_walk() || f.kind != FindingKind::Property
                        })
                        .collect();
                    let ungraded = !gated.undecided_to_the_walk()
                        && !(outcome.certain_compile && outcome.certain_defines);
                    // The gate goes the way the case says in MSBuild, so both
                    // directions are graded.
                    let misdirected = outcome.msbuild_ran_gated != taken;
                    if outcome.rejected || !findings.is_empty() || ungraded || misdirected {
                        failures.push(format!(
                            "{}: rejected {}, MSBuild ran gated.props {}, Compile certain {}, \
                             defines certain {}, findings {findings:#?}\n{describe}",
                            brief(&case),
                            outcome.rejected,
                            outcome.msbuild_ran_gated,
                            outcome.certain_compile,
                            outcome.certain_defines,
                        ));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} gated cases failed:\n{}",
        failures.len(),
        failures.join("\n=====\n")
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
        if !outcome.findings.iter().any(|f| family.covers(f)) {
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
