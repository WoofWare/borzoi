//! The three axes a gate decides — the Compile items, the defines and the
//! `<ProjectReference>` list — agree on every gate, and each holds what it
//! commits to against MSBuild (#1181).
//!
//! A gate the walk cannot decide hides the same thing from every axis: whether
//! the content behind it is in the build. Each axis used to answer that on its
//! own, and the reference list answered it differently: a reference dropped by
//! such a gate was published as part of a certain list, while a Compile item
//! or a define in the same place was doubted. This grid crosses
//!
//! - **axis**: a `<Compile>` item, a `<DefineConstants>` write, a
//!   `<ProjectReference>`;
//! - **site**: the gate on the element, or on its group;
//! - **polarity**: the gate MSBuild evaluates true, or false;
//! - **gate**: one reading a write the walk refused to compute, one reading a
//!   write under a condition the walk does not model, a condition the walk
//!   does not model itself, one reading a toolset name the walk holds no
//!   value of, and two the walk decides (the controls): a literal, and an
//!   `Exists` probe that settles the gate whatever the doubted names hold;
//!
//! and holds, at every point:
//!
//! - **certain-implies-exact**: an axis that commits agrees with MSBuild
//!   exactly (the items' `FullPath`s, or the `DefineConstants` property);
//! - **agreement**: the three axes, behind the same gate at the same site and
//!   polarity, are all certain or all doubted;
//! - **must-commit / must-doubt**: behind the controls every axis commits;
//!   behind every other gate every axis doubts, so no cell passes by
//!   agreeing with MSBuild by luck.

mod common;

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use common::{Oracle, parse_fsproj_with_imports};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Axis {
    Compile,
    Defines,
    References,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Site {
    Element,
    Group,
}

/// What the gate reads, and whether the walk can decide it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gate {
    /// `'$(Seen)' {op} 'D'`, `Seen` a literal: the walk decides it.
    Literal,
    /// `'$(Refused)' {op} 'D'`, `Refused` written by a function the walk does
    /// not compute and MSBuild computes as `D`.
    Refused,
    /// `'$(Unpinned)' {op} 'D'`, `Unpinned` written `D` under a condition the
    /// walk does not model and MSBuild takes.
    Unpinned,
    /// A condition the walk does not model, MSBuild's value of which is the
    /// polarity's.
    Unmodelled,
    /// `'$(MSBuildStartupDirectory)' {op} ''`: a toolset name, which MSBuild
    /// sets to the directory its process started in and the walk, evaluating
    /// for no process, holds no value of.
    Toolset,
    /// An `Exists` probe of a file beside the project, which decides the gate
    /// whatever the refused and toolset names beside it hold: the walk
    /// decides it.
    ExistsDecides,
}

const AXES: [Axis; 3] = [Axis::Compile, Axis::Defines, Axis::References];
const SITES: [Site; 2] = [Site::Element, Site::Group];
const GATES: [Gate; 6] = [
    Gate::Literal,
    Gate::Refused,
    Gate::Unpinned,
    Gate::Unmodelled,
    Gate::Toolset,
    Gate::ExistsDecides,
];

/// The file [`Gate::ExistsDecides`] probes, beside the project.
const PRESENT: &str = "Present.txt";

/// The writes every document carries, whichever gate it uses.
const PROPERTIES: &str = "<PropertyGroup>\
    <Seen>D</Seen>\
    <Refused>$([System.String]::Copy('D'))</Refused>\
    <Unpinned Condition=\"'\u{c9}' == '\u{e9}'\">D</Unpinned>\
    </PropertyGroup>";

/// The condition text for `gate`, which MSBuild evaluates to `truth`.
fn condition(gate: Gate, truth: bool) -> String {
    let op = if truth { "==" } else { "!=" };
    match gate {
        Gate::Literal => format!("'$(Seen)' {op} 'D'"),
        Gate::Refused => format!("'$(Refused)' {op} 'D'"),
        Gate::Unpinned => format!("'$(Unpinned)' {op} 'D'"),
        // MSBuild compares case-insensitively: `É` and `é` are equal, `É` and
        // `Ê` are not. The walk does not model the comparison.
        Gate::Unmodelled if truth => "'\u{c9}' == '\u{e9}'".to_string(),
        Gate::Unmodelled => "'\u{c9}' == '\u{ca}'".to_string(),
        // MSBuild's startup directory is never empty.
        Gate::Toolset if truth => "'$(MSBuildStartupDirectory)' != ''".to_string(),
        Gate::Toolset => "'$(MSBuildStartupDirectory)' == ''".to_string(),
        Gate::ExistsDecides if truth => format!(
            "Exists('{PRESENT}') Or '$(Refused)' == 'x' Or '$(MSBuildStartupDirectory)' == ''"
        ),
        Gate::ExistsDecides => format!(
            "!Exists('{PRESENT}') And ('$(Refused)' == 'D' Or '$(MSBuildStartupDirectory)' != '')"
        ),
    }
}

/// The document for one cell.
fn document(axis: Axis, site: Site, gate: Gate, truth: bool) -> String {
    let condition = format!(" Condition=\"{}\"", condition(gate, truth));
    let (group, element) = match site {
        Site::Element => (String::new(), condition),
        Site::Group => (condition, String::new()),
    };
    let body = match axis {
        Axis::Compile => {
            format!("<ItemGroup{group}><Compile Include=\"Gated.fs\"{element} /></ItemGroup>")
        }
        Axis::References => format!(
            "<ItemGroup{group}><ProjectReference Include=\"Gated.fsproj\"{element} /></ItemGroup>"
        ),
        Axis::Defines => format!(
            "<PropertyGroup{group}><DefineConstants{element}>GATED</DefineConstants></PropertyGroup>"
        ),
    };
    format!("<Project>{PROPERTIES}{body}</Project>")
}

/// What the walk publishes for `axis`: the full paths of its items or the
/// defines, when it commits to them; `None` when it doubts them. Beside it,
/// for the references, the claim the list makes and the edges it holds,
/// which an incomplete list still claims are MSBuild's.
fn ours(
    axis: Axis,
    xml: &str,
    path: &Path,
) -> (Option<Vec<String>>, common::ReferenceClaim, Vec<String>) {
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(path, xml).expect("a full project path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("a well-formed document");
    let names = |items: &[borzoi_msbuild::ResolvedItem]| -> Vec<String> {
        items.iter().map(|item| full_path(&item.include)).collect()
    };
    let claim = common::reference_claim(&parsed);
    let held = names(&parsed.project_references);
    let committed = match axis {
        Axis::Compile => (!parsed.items_uncertain).then(|| names(&parsed.items)),
        Axis::References => (claim == common::ReferenceClaim::Exact).then(|| held.clone()),
        Axis::Defines => (!parsed.define_constants_uncertain).then_some(parsed.define_constants),
    };
    (committed, claim, held)
}

/// A path as the grid compares it: lexically normalised, so a committed item
/// is held to MSBuild's `FullPath` whole, not by its file name alone.
fn full_path(path: &Path) -> String {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            other => out.push(other),
        }
    }
    out.to_string_lossy().into_owned()
}

/// MSBuild's answer for `axis`, in the same currency as [`ours`].
fn theirs(oracle: &mut Oracle, axis: Axis, xml: &str, path: &Path) -> Vec<String> {
    match axis {
        Axis::Compile | Axis::References => {
            let item_type = if axis == Axis::Compile {
                "Compile"
            } else {
                "ProjectReference"
            };
            oracle
                .items(xml, path, item_type, &[])
                .unwrap_or_else(|| panic!("MSBuild evaluates the cell:\n{xml}"))
                .iter()
                .map(|full| full_path(&PathBuf::from(full)))
                .collect()
        }
        Axis::Defines => {
            let names = ["DefineConstants".to_string()];
            let properties = oracle
                .project(xml, &names, Some(path), &[])
                .unwrap_or_else(|| panic!("MSBuild evaluates the cell:\n{xml}"));
            properties
                .get("DefineConstants")
                .map(String::as_str)
                .unwrap_or("")
                .split(';')
                .map(str::trim)
                .filter(|define| !define.is_empty())
                .map(str::to_string)
                .collect()
        }
    }
}

#[test]
fn every_axis_doubts_the_gates_the_others_doubt_and_commits_only_to_msbuilds_answer() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    // Canonical, so the walk's paths and MSBuild's agree on the root.
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    std::fs::write(root.join(PRESENT), "").expect("the probed file");
    let mut oracle = Oracle::spawn();
    let mut failures = Vec::new();
    let mut points = 0;
    for gate in GATES {
        for site in SITES {
            for truth in [true, false] {
                let mut certain = Vec::new();
                for axis in AXES {
                    let xml = document(axis, site, gate, truth);
                    let (ours, claim, held) = ours(axis, &xml, &path);
                    let theirs = theirs(&mut oracle, axis, &xml, &path);
                    points += 1;
                    if axis == Axis::References
                        && let Err(failure) = common::check_reference_claim(claim, &held, &theirs)
                    {
                        failures.push(format!("{failure}:\n{xml}"));
                    }
                    // The control's answer is the polarity's, on both sides:
                    // otherwise the cell grades nothing.
                    let expected = if truth { 1 } else { 0 };
                    assert_eq!(
                        theirs.len(),
                        expected,
                        "MSBuild's answer is not the polarity's:\n{xml}\n{theirs:?}"
                    );
                    if let Some(ours) = &ours
                        && *ours != theirs
                    {
                        failures.push(format!(
                            "{axis:?} committed {ours:?}; MSBuild holds {theirs:?}:\n{xml}"
                        ));
                    }
                    let must_commit = matches!(gate, Gate::Literal | Gate::ExistsDecides);
                    if ours.is_some() != must_commit {
                        failures.push(format!(
                            "{axis:?} {} behind a {gate:?} gate on the {site:?} ({truth}):\n{xml}",
                            if must_commit { "doubted" } else { "committed" },
                        ));
                    }
                    certain.push((axis, ours.is_some()));
                }
                if certain.iter().any(|(_, c)| *c) && certain.iter().any(|(_, c)| !*c) {
                    failures.push(format!(
                        "the axes disagree behind a {gate:?} gate on the {site:?} ({truth}): \
                         {certain:?}"
                    ));
                }
            }
        }
    }
    assert_eq!(points, GATES.len() * SITES.len() * 2 * AXES.len());
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
