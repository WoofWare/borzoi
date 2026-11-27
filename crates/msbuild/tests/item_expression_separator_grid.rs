//! An item expression whose arguments hold a `;` is one item expression, not
//! two fragments: MSBuild splits an item spec at the separators *outside*
//! `@(…)`, so `Include="@(Helper, ';Wrong.fsproj;')"` makes the `Helper`
//! items joined by `;Wrong.fsproj;` as their separator — `A.fsproj` alone
//! for one `Helper` — and never an item `Wrong.fsproj`. A walk that splits at
//! every `;` makes `Wrong.fsproj` and `')` items MSBuild never makes.
//!
//! The grid crosses
//!
//! - **item type**: a `<Compile>` item, a `<ProjectReference>`, a
//!   `<PackageReference>`;
//! - **route**: the expression in the item's own `Include`, or in a helper
//!   item's that the item copies (`Include="@(H2)"`);
//! - **form**: an item expression whose separator argument holds a `;`, a
//!   transform whose quoted text holds one, both, a function transform whose
//!   quoted argument holds one, the plain `@(Helper)`, and a literal list
//!   (the control);
//! - **seam**: no glob resolver, and the shipped one (which routes an
//!   `Include` through its own fragment split);
//!
//! and holds, at every point, what the walk commits to against MSBuild: a
//! certain Compile list or package set is MSBuild's exactly, and a
//! `<ProjectReference>` list not flagged uncertain holds no item MSBuild lacks.
//! The literal control in the item's own `Include` must commit on every item
//! type and both seams, so the grid cannot pass by declining everything.

mod common;

use std::collections::HashMap;
use std::path::{Component, Path, PathBuf};

use borzoi_msbuild::{GlobResolver, glob_resolver};
use common::{Oracle, parse_fsproj_with_imports};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Compile,
    ProjectReference,
    PackageReference,
}

impl Kind {
    fn element(self) -> &'static str {
        match self {
            Kind::Compile => "Compile",
            Kind::ProjectReference => "ProjectReference",
            Kind::PackageReference => "PackageReference",
        }
    }

    fn extension(self) -> &'static str {
        match self {
            Kind::Compile => "fs",
            Kind::ProjectReference => "fsproj",
            Kind::PackageReference => "pkg",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Route {
    Direct,
    ThroughHelper,
}

/// The `Include` for each form, over a `Helper` list of one item `A.<ext>`.
fn forms(ext: &str) -> [(&'static str, String); 6] {
    [
        ("separator", format!("@(Helper, ';Wrong.{ext};')")),
        ("transform", format!("@(Helper->'%(Identity);Wrong.{ext}')")),
        (
            "transform and separator",
            format!("@(Helper->'%(Identity)', ';Wrong.{ext};')"),
        ),
        (
            "function transform",
            format!("@(Helper->Replace('A', 'A.{ext};Wrong'))"),
        ),
        ("plain", "@(Helper)".to_string()),
        ("literal", format!("A.{ext};B.{ext}")),
    ]
}

/// Lexically normalised, as MSBuild's `FullPath` is.
fn normalised(path: &Path) -> String {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            other => out.push(other),
        }
    }
    out.to_string_lossy().into_owned()
}

/// What MSBuild makes of `kind`'s items, in the currency [`ours`] uses: full
/// paths, or a package's id (the last component of its `FullPath`).
fn theirs(oracle: &mut Oracle, kind: Kind, xml: &str, path: &Path) -> Vec<String> {
    oracle
        .items(xml, path, kind.element(), &[])
        .unwrap_or_else(|| panic!("MSBuild evaluates the cell:\n{xml}"))
        .iter()
        .map(|full| match kind {
            Kind::PackageReference => full.rsplit('/').next().unwrap_or(full).to_string(),
            Kind::Compile | Kind::ProjectReference => normalised(Path::new(full)),
        })
        .collect()
}

/// Whether the walk commits to `kind`'s items, and what they are.
fn ours(kind: Kind, parsed: &borzoi_msbuild::ParsedProject) -> (bool, Vec<String>) {
    match kind {
        Kind::Compile => (
            !parsed.items_uncertain,
            parsed
                .items
                .iter()
                .filter(|item| item.kind == borzoi_msbuild::ItemKind::Compile)
                .map(|item| normalised(&item.include))
                .collect(),
        ),
        Kind::ProjectReference => (
            !parsed.project_references_uncertain,
            parsed
                .project_references
                .iter()
                .map(|item| normalised(&item.include))
                .collect(),
        ),
        Kind::PackageReference => (
            !parsed.package_references_uncertain,
            parsed
                .package_references
                .iter()
                .map(|package| package.id.clone())
                .collect(),
        ),
    }
}

#[test]
fn an_item_expression_holding_a_separator_makes_no_item_msbuild_lacks() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    let resolver: &GlobResolver<'_> = &glob_resolver::resolve;
    let mut oracle = Oracle::spawn();
    let mut failures = Vec::new();
    let mut points = 0;
    for kind in [
        Kind::Compile,
        Kind::ProjectReference,
        Kind::PackageReference,
    ] {
        let ext = kind.extension();
        let element = kind.element();
        for route in [Route::Direct, Route::ThroughHelper] {
            for (form, include) in forms(ext) {
                // A package reference names its version, or the walk declines
                // its set for that alone.
                let version = if kind == Kind::PackageReference {
                    " Version=\"1.0.0\""
                } else {
                    ""
                };
                let items = match route {
                    Route::Direct => format!("<{element} Include=\"{include}\"{version} />"),
                    Route::ThroughHelper => format!(
                        "<H2 Include=\"{include}\" /><{element} Include=\"@(H2)\"{version} />"
                    ),
                };
                let xml = format!(
                    "<Project><ItemGroup><Helper Include=\"A.{ext}\" />{items}</ItemGroup></Project>"
                );
                std::fs::write(&path, &xml).expect("the project");
                let theirs = theirs(&mut oracle, kind, &xml, &path);
                for with_resolver in [false, true] {
                    points += 1;
                    let parsed = parse_fsproj_with_imports(
                        &borzoi_msbuild::ProjectFile::buffer(&path, &xml).expect("a full path"),
                        &HashMap::new(),
                        &common::oracle_environment(),
                        None,
                        with_resolver.then_some(resolver),
                    )
                    .expect("a well-formed document");
                    let cell = format!("{kind:?} / {route:?} / {form} / resolver: {with_resolver}");
                    let (committed, ours) = ours(kind, &parsed);
                    if committed {
                        let holds = match kind {
                            Kind::Compile | Kind::PackageReference => ours == theirs,
                            Kind::ProjectReference => ours.iter().all(|p| theirs.contains(p)),
                        };
                        if !holds {
                            failures.push(format!(
                                "{cell}: committed {ours:?}, MSBuild holds {theirs:?}\n{xml}"
                            ));
                        }
                    } else if form == "literal" && route == Route::Direct {
                        failures.push(format!("{cell}: the control declined\n{xml}"));
                    }
                }
            }
        }
    }
    assert_eq!(points, 3 * 2 * 6 * 2);
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
