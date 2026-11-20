//! The target fold (Stage 4 of `docs/resolve-what-a-request-reads-plan.md`):
//! the surfaces of earlier files, and full walks against the state those
//! surfaces replay, answer exactly as the cold full fold does.
//!
//! - [`resolve_target`]'s full walk of file `i` equals the cold fold's
//!   `file(i)`, and its surfaces equal the cold fold's surfaces before `i`.
//! - [`ProjectSurfaces::resolve_file`] replays the state entering any `j` and
//!   walks `j` against it, equal to the cold fold's `file(j)`; and
//!   [`ProjectSurfaces::item_def`] answers every item the cold fold's files
//!   resolve to as [`ResolvedProject::item_def`] does.
//! - The incremental surface fold equals a cold surface fold after every edit
//!   of a generated script, and a body edit re-walks no other file.
//!
//! The generated projects mix named modules, headerless implementations
//! (whose values live under an implicit module named after the file),
//! signature-paired implementations (whose `.fsi` screens what later files
//! see), and union types, each referencing earlier files' values. The edits
//! touch bodies (moving positions), add exports, rename a headerless file and
//! drop a signature.

use std::path::PathBuf;

use borzoi_cst::parser::{parse, parse_sig};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile};
use borzoi_sema::{
    AssemblyEnv, ProjectFile, ProjectSurfaces, Resolution, ResolvedProject, SourceFile,
    SyntaxRecovery, qualified_names, resolve_project_files, resolve_project_files_prefix,
    resolve_project_surfaces, resolve_project_surfaces_incremental, resolve_target,
};
use proptest::prelude::*;

use crate::common::edit_script::generate;

// ============================================================================
// Generated projects
// ============================================================================

/// What one generated unit compiles to.
#[derive(Debug, Clone)]
enum Shape {
    /// `module Mk` with its values.
    Module,
    /// No header: its values live under the implicit module `Hk` (the
    /// file's name).
    Headerless,
    /// `Pk.fsi` declaring the first value, then `Pk.fs` defining every value:
    /// the rest are hidden from later files.
    Paired { signed: bool },
    /// `module Uk` declaring a union `Tk = Ak | Bk` and a value of it.
    Union,
}

/// One unit of a generated project: its shape, how many values it defines,
/// which earlier unit each value's body reads, and a body literal an edit
/// can change.
#[derive(Debug, Clone)]
struct Unit {
    shape: Shape,
    values: usize,
    reads: Vec<usize>,
    literal: u32,
    /// Blank lines before the first declaration: a body edit that moves
    /// every position in the file without changing what it exports.
    padding: usize,
    /// The headerless file's name suffix, so a rename changes its implicit
    /// module.
    rename: u32,
}

impl Unit {
    /// The module path later files reach this unit's values through.
    fn module(&self, k: usize) -> String {
        match self.shape {
            Shape::Module => format!("M{k}"),
            Shape::Headerless => format!("H{k}x{}", self.rename),
            Shape::Paired { .. } => format!("P{k}"),
            Shape::Union => format!("U{k}"),
        }
    }

    /// The names later files may read: what the signature leaves visible for
    /// a signed pair, every value otherwise.
    fn visible(&self, k: usize) -> Vec<String> {
        let all: Vec<String> = (0..self.values).map(|v| format!("v{k}_{v}")).collect();
        match self.shape {
            Shape::Paired { signed: true } => all.into_iter().take(1).collect(),
            _ => all,
        }
    }
}

/// A unit's body for value `v`: the literal, plus a read of an earlier
/// unit's first visible value when it has one.
fn body(units: &[Unit], k: usize, v: usize) -> String {
    let unit = &units[k];
    let earlier = unit.reads.get(v).copied().filter(|&e| e < k).and_then(|e| {
        units[e]
            .visible(e)
            .first()
            .map(|name| format!("{}.{name}", units[e].module(e)))
    });
    match earlier {
        Some(read) => format!("(let local{v} = {} in local{v}) + {read}", unit.literal),
        None => format!("(fun x -> x + {}) {v}", unit.literal),
    }
}

/// The Compile items of `units`, as `(path, source)` pairs in Compile order.
fn render(units: &[Unit]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for (k, unit) in units.iter().enumerate() {
        let pad = "\n".repeat(unit.padding);
        let lets = |units: &[Unit]| -> String {
            (0..unit.values)
                .map(|v| format!("let v{k}_{v} = {}\n", body(units, k, v)))
                .collect()
        };
        match unit.shape {
            Shape::Module => out.push((
                format!("M{k}.fs"),
                format!("module M{k}\n{pad}{}", lets(units)),
            )),
            Shape::Headerless => out.push((
                format!("H{k}x{}.fs", unit.rename),
                format!("{pad}{}", lets(units)),
            )),
            Shape::Paired { signed } => {
                if signed {
                    out.push((
                        format!("P{k}.fsi"),
                        format!("module P{k}\nval v{k}_0 : int\n"),
                    ));
                }
                out.push((
                    format!("P{k}.fs"),
                    format!("module P{k}\n{pad}{}", lets(units)),
                ));
            }
            Shape::Union => out.push((
                format!("U{k}.fs"),
                format!(
                    "module U{k}\n{pad}type T{k} = A{k} | B{k} of int\nlet u{k} = B{k} 1\n{}",
                    lets(units)
                ),
            )),
        }
    }
    out
}

/// Parse `sources` into the fold's Compile items.
fn project_files(sources: &[(String, String)]) -> Vec<ProjectFile> {
    project_files_reusing(sources, &[])
}

/// Parse `sources` into the fold's Compile items, keeping the parse of any
/// item whose path and text `earlier` (an earlier snapshot's sources and
/// items) already holds: the fold reuses only a tree it has seen, as the
/// LSP's parse cache hands it.
fn project_files_reusing(
    sources: &[(String, String)],
    earlier: &[(&(String, String), &ProjectFile)],
) -> Vec<ProjectFile> {
    let parsed: Vec<(SourceFile, SyntaxRecovery)> = sources
        .iter()
        .map(|source @ (name, src)| {
            if let Some((_, pf)) = earlier.iter().find(|(s, _)| *s == source) {
                (pf.file.clone(), pf.recovery.clone())
            } else if name.ends_with(".fsi") {
                let p = parse_sig(src);
                let recovery = SyntaxRecovery::of(&p);
                (
                    SourceFile::Sig(SigFile::cast(p.root).expect("sig")),
                    recovery,
                )
            } else {
                let p = parse(src);
                let recovery = SyntaxRecovery::of(&p);
                (
                    SourceFile::Impl(ImplFile::cast(p.root).expect("impl")),
                    recovery,
                )
            }
        })
        .collect();
    let paths: Vec<PathBuf> = sources.iter().map(|(n, _)| n.into()).collect();
    let srcs: Vec<SourceFile> = parsed.iter().map(|(f, _)| f.clone()).collect();
    parsed
        .into_iter()
        .zip(qualified_names(&srcs, &paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect()
}

fn shape() -> impl Strategy<Value = Shape> {
    prop_oneof![
        Just(Shape::Module),
        Just(Shape::Headerless),
        any::<bool>().prop_map(|signed| Shape::Paired { signed }),
        Just(Shape::Union),
    ]
}

fn unit() -> impl Strategy<Value = Unit> {
    (
        shape(),
        1usize..4,
        prop::collection::vec(0usize..8, 3),
        0u32..4,
    )
        .prop_map(|(shape, values, reads, literal)| Unit {
            shape,
            values,
            reads,
            literal,
            padding: 0,
            rename: 0,
        })
}

/// One edit of a generated project.
#[derive(Debug, Clone)]
enum Edit {
    /// Change a body literal: no export changes.
    Body(usize),
    /// Prepend blank lines: every position in the file moves, no export
    /// changes.
    Pad(usize),
    /// Add a value: the file exports one more item.
    AddValue(usize),
    /// Rename a headerless file: its implicit module moves.
    Rename(usize),
    /// Drop or restore a pair's signature.
    ToggleSignature(usize),
}

fn edit() -> impl Strategy<Value = Edit> {
    prop_oneof![
        (0usize..8).prop_map(Edit::Body),
        (0usize..8).prop_map(Edit::Pad),
        (0usize..8).prop_map(Edit::AddValue),
        (0usize..8).prop_map(Edit::Rename),
        (0usize..8).prop_map(Edit::ToggleSignature),
    ]
}

fn apply(units: &mut [Unit], edit: &Edit) {
    let n = units.len();
    match *edit {
        Edit::Body(k) => units[k % n].literal += 1,
        Edit::Pad(k) => units[k % n].padding += 1,
        Edit::AddValue(k) => units[k % n].values = (units[k % n].values + 1).min(4),
        Edit::Rename(k) => {
            if let Shape::Headerless = units[k % n].shape {
                units[k % n].rename += 1;
            }
        }
        Edit::ToggleSignature(k) => {
            if let Shape::Paired { signed } = &mut units[k % n].shape {
                *signed = !*signed;
            }
        }
    }
}

// ============================================================================
// The properties
// ============================================================================

/// Every target and every replayed walk of `files` answers as the cold full
/// fold does, and so does every `item_def` the cold fold's files reach.
fn check_target_fold(files: &[ProjectFile], env: &AssemblyEnv) -> Result<(), TestCaseError> {
    let full = resolve_project_files(files, env);
    let surfaces = resolve_project_surfaces(files, files.len(), env);
    prop_assert_eq!(surfaces.len(), files.len());
    for i in 0..files.len() {
        let target = resolve_target(files, i, env);
        prop_assert!(
            target.target() == full.file(i),
            "the target fold's walk of file {} differs from the cold fold's",
            i
        );
        prop_assert_eq!(target.surfaces().len(), i);
        for j in 0..i {
            prop_assert!(
                target.surfaces().surface(j) == Some(full.file(j).surface()),
                "the target fold's surface of file {} (target {}) differs",
                j,
                i
            );
        }
        prop_assert!(
            surfaces.resolve_file(files, i, env) == *full.file(i),
            "the walk of file {} against its replayed state differs",
            i
        );
    }
    check_item_defs(&surfaces, &full)
}

/// Every item a resolution of `full` names is answered by `surfaces` as by
/// `full`.
fn check_item_defs(
    surfaces: &ProjectSurfaces,
    full: &ResolvedProject,
) -> Result<(), TestCaseError> {
    for i in 0..full.len() {
        for res in full.file(i).resolutions().values() {
            if matches!(
                res,
                Resolution::Item(_) | Resolution::EarlierFileType { .. }
            ) {
                prop_assert_eq!(surfaces.item_def(*res), full.item_def(*res));
            }
        }
    }
    Ok(())
}

/// Fold `script`'s snapshots incrementally, surfaces only, each against the
/// last, and hold each to a cold surface fold. Returns how many steps reused
/// a file after recomputing an earlier one.
fn check_incremental(
    mut units: Vec<Unit>,
    script: &[Edit],
    env: &AssemblyEnv,
) -> Result<usize, TestCaseError> {
    let mut prev_sources = render(&units);
    let mut prev_files = project_files(&prev_sources);
    let mut prev = resolve_project_surfaces(&prev_files, prev_files.len(), env);
    let mut suffix_reuse = 0;
    for edit in script {
        apply(&mut units, edit);
        let sources = render(&units);
        let earlier: Vec<_> = prev_sources.iter().zip(&prev_files).collect();
        let files = project_files_reusing(&sources, &earlier);
        let (incremental, reused) =
            resolve_project_surfaces_incremental(&prev_files, &prev, &files, files.len(), env);
        let cold = resolve_project_surfaces(&files, files.len(), env);
        prop_assert!(
            incremental == cold,
            "the incremental surface fold differs from a cold one after {:?}",
            edit
        );
        if let Some(first) = reused.iter().position(|r| !r)
            && reused[first..].iter().any(|r| *r)
        {
            suffix_reuse += 1;
        }
        // Body-only edits change no surface's contribution, so every file but
        // the edited one is reused.
        if matches!(edit, Edit::Body(_) | Edit::Pad(_)) && files.len() == prev_files.len() {
            prop_assert!(
                reused.iter().filter(|r| !**r).count() <= 1,
                "a body edit re-walked more than the edited file: {:?}",
                reused
            );
        }
        check_item_defs(&incremental, &resolve_project_files(&files, env))?;
        prev_sources = sources;
        prev_files = files;
        prev = incremental;
    }
    Ok(suffix_reuse)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    #[test]
    fn target_fold_answers_as_the_full_fold(units in prop::collection::vec(unit(), 1..7)) {
        let files = project_files(&render(&units));
        check_target_fold(&files, &AssemblyEnv::default())?;
    }

    #[test]
    fn incremental_surfaces_equal_cold_surfaces(
        units in prop::collection::vec(unit(), 1..7),
        script in prop::collection::vec(edit(), 1..6),
    ) {
        check_incremental(units, &script, &AssemblyEnv::default())?;
    }

    /// The edit-script generator the incremental differential uses, whose
    /// files exercise `[<AutoOpen>]`, attributes and unions.
    #[test]
    fn target_fold_answers_as_the_full_fold_on_edit_scripts(
        nums in prop::collection::vec(any::<u32>(), 0..96),
    ) {
        let scenario = generate(nums);
        for snapshot in scenario.snapshots.iter().take(3) {
            let sources: Vec<(String, String)> = snapshot
                .iter()
                .enumerate()
                .map(|(k, src)| (format!("F{k}.fs"), src.clone()))
                .collect();
            check_target_fold(&project_files(&sources), &AssemblyEnv::default())?;
        }
    }
}

/// The generator reaches the reuse the incremental fold exists for: a file
/// reused after an earlier one was recomputed.
#[test]
fn generator_exercises_suffix_reuse() {
    let units = vec![
        Unit {
            shape: Shape::Module,
            values: 2,
            reads: vec![],
            literal: 0,
            padding: 0,
            rename: 0,
        },
        Unit {
            shape: Shape::Paired { signed: true },
            values: 2,
            reads: vec![0, 0],
            literal: 0,
            padding: 0,
            rename: 0,
        },
        Unit {
            shape: Shape::Headerless,
            values: 1,
            reads: vec![1],
            literal: 0,
            padding: 0,
            rename: 0,
        },
        Unit {
            shape: Shape::Union,
            values: 1,
            reads: vec![2],
            literal: 0,
            padding: 0,
            rename: 0,
        },
    ];
    let reused = check_incremental(
        units,
        &[Edit::Body(0), Edit::Pad(1)],
        &AssemblyEnv::default(),
    )
    .expect("the incremental surface fold matches");
    assert_eq!(reused, 2, "each body edit reuses every later file");
}

/// A prefix of the surface fold is the surface fold of the prefix, so a
/// target fold at `i` never depends on how far an earlier fold went.
#[test]
fn surfaces_of_a_prefix_are_a_prefix_of_the_surfaces() {
    let units = vec![
        Unit {
            shape: Shape::Paired { signed: true },
            values: 2,
            reads: vec![],
            literal: 0,
            padding: 0,
            rename: 0,
        },
        Unit {
            shape: Shape::Headerless,
            values: 2,
            reads: vec![0],
            literal: 0,
            padding: 0,
            rename: 0,
        },
        Unit {
            shape: Shape::Module,
            values: 1,
            reads: vec![1],
            literal: 0,
            padding: 0,
            rename: 0,
        },
    ];
    let files = project_files(&render(&units));
    let env = AssemblyEnv::default();
    let whole = resolve_project_surfaces(&files, files.len(), &env);
    for len in 0..=files.len() {
        let prefix = resolve_project_surfaces(&files, len, &env);
        for j in 0..len {
            assert!(
                prefix.surface(j) == whole.surface(j),
                "surface {j} of the {len}-prefix"
            );
        }
        let full = resolve_project_files_prefix(&files, len, &env);
        for j in 0..len {
            assert!(prefix.resolve_file(&files, j, &env) == *full.file(j));
        }
    }
}

/// What a whole project declares is read only off a fold that reached its
/// last Compile item: a prefix fold's extension names are unknowable, and a
/// fold to the end (prefix-shaped or not) reads them. The extension named
/// in the last file is what a prefix would miss.
#[test]
fn only_a_complete_fold_answers_for_the_whole_project() {
    use borzoi_sema::{ExtensionNames, NamesUnknowable};
    let sources = vec![
        ("A.fs".to_owned(), "module A\nlet x = 1\n".to_owned()),
        (
            "B.fs".to_owned(),
            "module B\ntype System.String with\n    member s.Shout() = 1\n".to_owned(),
        ),
    ];
    let files = project_files(&sources);
    let env = AssemblyEnv::default();
    for len in 0..files.len() {
        assert_eq!(
            resolve_project_files_prefix(&files, len, &env).extension_names(),
            ExtensionNames::Unknowable(NamesUnknowable::PartialFold),
            "the {len}-prefix"
        );
    }
    for whole in [
        resolve_project_files_prefix(&files, files.len(), &env),
        resolve_project_files(&files, &env),
    ] {
        assert!(whole.extension_names().may_have("Shout", false));
        assert!(whole.extension_names().unknowable().is_none());
    }
    // An unpaired signature last: FCS reports the missing implementation and
    // still imports the earlier file's extension, so the names are every
    // file's, not the last slot's, cold and incremental alike.
    let mut with_tail = sources.clone();
    with_tail.push((
        "Tail.fsi".to_owned(),
        "module Tail
val y: int
"
        .to_owned(),
    ));
    let tail_files = project_files(&with_tail);
    let cold = resolve_project_files(&tail_files, &env);
    let (incremental, _) = borzoi_sema::resolve_project_files_incremental(
        &files,
        &resolve_project_files(&files, &env),
        &tail_files,
        &env,
    );
    for (what, whole) in [("cold", cold), ("incremental", incremental)] {
        assert!(
            whole.extension_names().may_have("Shout", false),
            "{what}: a trailing signature drops the earlier files' names"
        );
    }
}
