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
//! `<ProjectReference>` list is held to the claim it makes
//! (`common::check_reference_claim`: certain is MSBuild's exactly, incomplete
//! holds only MSBuild's references in order). The literal control in the
//! item's own `Include` must commit on every item type and both seams, a
//! reference list certainly, so the grid cannot pass by declining everything.

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
fn forms(ext: &str) -> [(&'static str, String); 8] {
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
        // MSBuild's tokenizer quotes with `'` only: a `;` inside `"…"`
        // before the expression's first unquoted `)` is still inside it.
        (
            "double-quoted separator",
            format!("@(Helper->Replace(\"A\", \"A.{ext};Wrong\"))"),
        ),
        // A `(` inside `"…"` opens nothing: the expression ends at its first
        // unquoted `)`, and the `;` after it separates a literal.
        (
            "double-quoted parenthesis then a literal",
            format!("@(Helper->Replace(\"(\", \"_\"));B.{ext}"),
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
        // Any claim but uncertain is a commitment (#1181): an incomplete
        // list's edges are still followed.
        Kind::ProjectReference => (
            common::reference_claim(parsed) != common::ReferenceClaim::Nothing,
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
                // An `Include` holding `"` is written in `'…'`, which none
                // of those forms holds.
                let attribute = if include.contains('"') {
                    format!("'{include}'")
                } else {
                    format!("\"{include}\"")
                };
                let items = match route {
                    Route::Direct => format!("<{element} Include={attribute}{version} />"),
                    Route::ThroughHelper => format!(
                        "<H2 Include={attribute} /><{element} Include=\"@(H2)\"{version} />"
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
                    let control = form == "literal" && route == Route::Direct;
                    if committed {
                        // The control's list is MSBuild's exactly, references
                        // included, so a walk that dropped every reference on
                        // one seam fails here.
                        // A reference list is graded by the claim it makes
                        // (`common::check_reference_claim`); the control's
                        // must be certain, so a walk that dropped every
                        // reference on one seam fails here.
                        let holds = match kind {
                            Kind::Compile | Kind::PackageReference => ours == theirs,
                            Kind::ProjectReference => {
                                let claim = common::reference_claim(&parsed);
                                (!control || claim == common::ReferenceClaim::Exact)
                                    && common::check_reference_claim(claim, &ours, &theirs).is_ok()
                            }
                        };
                        if !holds {
                            failures.push(format!(
                                "{cell}: committed {ours:?}, MSBuild holds {theirs:?}\n{xml}"
                            ));
                        }
                    } else if control {
                        failures.push(format!("{cell}: the control declined\n{xml}"));
                    }
                }
            }
        }
    }
    assert_eq!(points, 3 * 2 * 8 * 2);
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A metadata-only `Update` whose spec begins with an item expression strands
/// nothing in MSBuild's batch of `Update`s, whatever that expression's
/// arguments hold: MSBuild abandons batching at its first fragment. The walk
/// keeps the Compile list it would keep for the same `Update` without the
/// separator argument.
#[test]
fn an_update_beginning_with_an_item_expression_strands_nothing() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    let mut oracle = Oracle::spawn();
    for update in ["@(Helper)", "@(Helper, ';')", "@(Helper, ';X.fs;')"] {
        let xml = format!(
            "<Project><ItemGroup><Helper Include=\"A.fs\" />\
             <Compile Include=\"A.fs;B.fs\" />\
             <Compile Update=\"{update}\" Link=\"Elsewhere.fs\" /></ItemGroup></Project>"
        );
        std::fs::write(&path, &xml).expect("the project");
        let theirs = theirs(&mut oracle, Kind::Compile, &xml, &path);
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&path, &xml).expect("a full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("a well-formed document");
        let (committed, ours) = ours(Kind::Compile, &parsed);
        assert!(committed, "{update}: {:#?}\n{xml}", parsed.diagnostics);
        assert_eq!(ours, theirs, "{update}\n{xml}");
    }
}

/// The refusal declines the whole spec, so a literal fragment beside an item
/// expression holding a `;` goes with it, though MSBuild makes it whatever the
/// expression holds: pinned, so that splitting at top-level separators (#1198)
/// flips this test.
#[test]
fn literal_fragments_beside_a_spanning_expression_are_declined_with_it() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    let xml = "<Project><ItemGroup><Helper Include=\"A.fsproj\" />\
               <ProjectReference Include=\"Explicit.fsproj;@(Helper, ';')\" /></ItemGroup></Project>";
    std::fs::write(&path, xml).expect("the project");
    let theirs = theirs(&mut Oracle::spawn(), Kind::ProjectReference, xml, &path);
    let explicit = normalised(&root.join("Explicit.fsproj"));
    assert!(theirs.contains(&explicit), "MSBuild makes it: {theirs:?}");
    let parsed = parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&path, xml).expect("a full path"),
        &HashMap::new(),
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("a well-formed document");
    let (_, ours) = ours(Kind::ProjectReference, &parsed);
    assert!(ours.is_empty(), "the whole spec is declined: {ours:?}");
}

/// An item expression ends, as MSBuild's tokenizer ends it, at its first `)`
/// outside `'…'` quotes: a `(` inside a double-quoted argument opens nothing,
/// so the `;` after the expression separates a literal MSBuild makes, and the
/// walk keeps it.
#[test]
fn a_literal_after_an_expression_with_a_double_quoted_parenthesis_is_kept() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    let xml = "<Project><ItemGroup><Helper Include=\"A(B.fsproj\" />\
               <ProjectReference Include='@(Helper->Replace(\"(\", \"_\"));Explicit.fsproj' />\
               </ItemGroup></Project>";
    std::fs::write(&path, xml).expect("the project");
    let theirs = theirs(&mut Oracle::spawn(), Kind::ProjectReference, xml, &path);
    let explicit = normalised(&root.join("Explicit.fsproj"));
    assert!(theirs.contains(&explicit), "MSBuild makes it: {theirs:?}");
    let resolver: &GlobResolver<'_> = &glob_resolver::resolve;
    for with_resolver in [false, true] {
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&path, xml).expect("a full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            with_resolver.then_some(resolver),
        )
        .expect("a well-formed document");
        let (_, ours) = ours(Kind::ProjectReference, &parsed);
        assert!(
            ours.contains(&explicit),
            "resolver: {with_resolver}: {ours:?} {:#?}",
            parsed.diagnostics
        );
        if let Err(failure) =
            common::check_reference_claim(common::reference_claim(&parsed), &ours, &theirs)
        {
            panic!("resolver: {with_resolver}: {failure}");
        }
    }
}

/// A refused spec is reported as expanded, where the item expression is,
/// on both seams: `$(At)(Helper, ';')` with `At` holding `@` names
/// `@(Helper, ';')`.
#[test]
fn a_refused_spec_is_reported_as_expanded() {
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let root = borzoi_msbuild::observed::host_fs::canonicalize(dir.path()).expect("canonicalize");
    let path = root.join("Demo.fsproj");
    let xml = "<Project><PropertyGroup><At>@</At></PropertyGroup>\
               <ItemGroup><Helper Include=\"A.fsproj\" />\
               <ProjectReference Include=\"$(At)(Helper, ';')\" /></ItemGroup></Project>";
    let resolver: &GlobResolver<'_> = &glob_resolver::resolve;
    for with_resolver in [false, true] {
        let parsed = parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&path, xml).expect("a full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            with_resolver.then_some(resolver),
        )
        .expect("a well-formed document");
        let named: Vec<&str> = parsed
            .diagnostics
            .iter()
            .filter_map(|d| match &d.kind {
                borzoi_msbuild::DiagnosticKind::UnresolvedItemReference { reference } => {
                    Some(reference.as_str())
                }
                _ => None,
            })
            .collect();
        assert_eq!(named, ["@(Helper, ';')"], "resolver: {with_resolver}");
    }
}
