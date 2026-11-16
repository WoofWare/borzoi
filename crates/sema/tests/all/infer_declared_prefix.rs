//! Stage 7a of `docs/resolve-what-a-request-reads-plan.md`: what a file's
//! inference reads of every earlier file, and what it reads only of the
//! files it references.
//!
//! A file's inference reads earlier files through `PrecedingTypes`. Three of
//! its reads are of the whole prefix (the constructor-like declarations of a
//! name, the unions and records F# seals, whether a type is declared at a
//! path), and an earlier file the target never references still moves them.
//! The rest are per item, and only one of those, an earlier value's type,
//! comes from inferring the earlier file's bodies.
//!
//! The property here is that the whole-prefix facts are a fold over the
//! earlier files' declarations alone: building each file's facts without
//! walking it, and folding those, gives the same table as the full fold, the
//! values' types aside ([`whole_prefix_facts_divergence`]). The census's
//! demand closure ([`inference_demand_closures`]) is what a file's inference
//! would then still need inferred: the files declaring the earlier values it
//! references, and theirs in turn.

use std::path::{Path, PathBuf};

use borzoi_cst::parser::{parse, parse_sig};
use borzoi_cst::syntax::{AstNode, ImplFile, SigFile, TextRange, TextSize};
use borzoi_sema::test_support::inference_demand::{
    inference_demand_closures, whole_prefix_facts_divergence,
};
use borzoi_sema::{
    AssemblyEnv, InferredProject, ProjectFile, ResolvedProject, SourceFile, SyntaxRecovery,
    infer_project, qualified_names, resolve_project_files,
};
use proptest::prelude::*;

use crate::common::edit_script::generate;
use crate::common::{fsharp_core_env, full_bcl_env};

fn parse_source(path: &Path, src: &str) -> (SourceFile, SyntaxRecovery) {
    if path.extension().is_some_and(|e| e == "fsi") {
        let p = parse_sig(src);
        let recovery = SyntaxRecovery::of(&p);
        (
            SourceFile::Sig(SigFile::cast(p.root).expect("sig file")),
            recovery,
        )
    } else {
        let p = parse(src);
        let recovery = SyntaxRecovery::of(&p);
        (
            SourceFile::Impl(ImplFile::cast(p.root).expect("impl file")),
            recovery,
        )
    }
}

struct Fold {
    files: Vec<ProjectFile>,
    resolved: ResolvedProject,
    inferred: InferredProject,
}

/// Resolve and infer the Compile items `sources`, as `(path, source)` pairs.
fn fold(sources: &[(String, String)], env: &AssemblyEnv) -> Fold {
    let paths: Vec<PathBuf> = sources.iter().map(|(p, _)| PathBuf::from(p)).collect();
    let parsed: Vec<(SourceFile, SyntaxRecovery)> = sources
        .iter()
        .zip(&paths)
        .map(|((_, src), path)| parse_source(path, src))
        .collect();
    let trees: Vec<SourceFile> = parsed.iter().map(|(f, _)| f.clone()).collect();
    let files: Vec<ProjectFile> = parsed
        .into_iter()
        .zip(qualified_names(&trees, &paths))
        .map(|((file, recovery), qnof)| ProjectFile::new(file, qnof, recovery))
        .collect();
    let resolved = resolve_project_files(&files, env);
    let inferred = infer_project(&files, &resolved, env);
    Fold {
        files,
        resolved,
        inferred,
    }
}

fn owned(sources: &[(&str, &str)]) -> Vec<(String, String)> {
    sources
        .iter()
        .map(|(p, s)| ((*p).to_string(), (*s).to_string()))
        .collect()
}

/// The range of the `n`th occurrence of `needle` in `src`.
fn nth_range(src: &str, needle: &str, n: usize) -> TextRange {
    let start = src
        .match_indices(needle)
        .nth(n)
        .unwrap_or_else(|| panic!("{needle:?} occurs fewer than {} times", n + 1))
        .0;
    TextRange::at(
        TextSize::try_from(start).expect("offset fits"),
        TextSize::try_from(needle.len()).expect("length fits"),
    )
}

fn assert_whole_prefix_facts_are_declared(fold: &Fold, env: &AssemblyEnv) {
    if let Some(divergence) =
        whole_prefix_facts_divergence(&fold.files, &fold.resolved, env, &fold.inferred)
    {
        panic!("{divergence}");
    }
}

/// D6's case: an earlier `let Red = 0` withholds the type of a later file's
/// use of its own case `Red`, though the later file references nothing of the
/// earlier one. So the earlier file is outside the later one's demand
/// closure, and still moves its inference, through a whole-prefix fact its
/// declarations alone decide.
#[test]
fn an_unreferenced_files_value_contests_a_case_name_through_its_declarations() {
    let env = fsharp_core_env();
    let colour = "module B\ntype Color = Red | Blue\nlet r = Red\n";
    let with_value = fold(
        &owned(&[("A.fs", "module A\nlet Red = 0\n"), ("B.fs", colour)]),
        env,
    );
    assert_whole_prefix_facts_are_declared(&with_value, env);
    let closures = inference_demand_closures(&with_value.resolved);
    assert!(
        closures[1].is_empty(),
        "B references nothing of A, so needs none of its inference: {closures:?}"
    );
    let red = nth_range(colour, "Red", 1);
    assert_eq!(
        with_value.inferred.file(1).and_then(|f| f.type_at(red)),
        None,
        "the earlier `Red` contests the case name, so the use is withheld"
    );
    let alone = fold(&owned(&[("B.fs", colour)]), env);
    assert!(
        alone
            .inferred
            .file(0)
            .and_then(|f| f.type_at(red))
            .is_some(),
        "without the earlier file the use is the case, and typed"
    );
}

/// The closure follows value reads transitively, and leaves out what the
/// target reads only through declarations: a file it does not reach, and a
/// union whose case it uses.
#[test]
fn the_demand_closure_follows_value_reads_and_not_case_uses() {
    let env = fsharp_core_env();
    let project = fold(
        &owned(&[
            ("A.fs", "module A\nlet a = 1\n"),
            ("B.fs", "module B\nlet b = A.a + 1\n"),
            ("C.fs", "module C\nlet c = B.b\n"),
            ("D.fs", "module D\nlet d = 2\n"),
            ("U.fs", "module U\ntype T = K | L of int\n"),
            ("E.fs", "module E\nlet e = C.c\nlet k = U.K\n"),
        ]),
        env,
    );
    assert_whole_prefix_facts_are_declared(&project, env);
    let closures = inference_demand_closures(&project.resolved);
    let set = |files: &[usize]| files.iter().copied().collect();
    assert_eq!(closures[0], set(&[]));
    assert_eq!(closures[1], set(&[0]));
    assert_eq!(closures[2], set(&[0, 1]));
    assert_eq!(closures[3], set(&[]));
    assert_eq!(closures[4], set(&[]));
    assert_eq!(
        closures[5],
        set(&[0, 1, 2]),
        "E reads C's value (and so B's and A's), not D, and U only for a case"
    );
}

/// A signature slot and the implementation it screens: the pair publishes
/// no declared types, cases or records, and the slot is inferred not at all,
/// in both folds.
#[test]
fn a_signatured_pair_declares_the_same_in_both_folds() {
    let env = full_bcl_env();
    let project = fold(
        &owned(&[
            ("P.fsi", "module P\ntype T = A | B\nval p : int\n"),
            ("P.fs", "module P\ntype T = A | B\nlet p = 1\n"),
            ("Q.fs", "module Q\nlet q = P.p\nlet t = P.A\n"),
        ]),
        env,
    );
    assert_whole_prefix_facts_are_declared(&project, env);
}

/// A case whose payload names an earlier file's record, and a record whose
/// field does: their schemes read the earlier file's declared types, so the
/// declarations-only fold must thread its own table to publish them. The
/// three files share a namespace, where the annotation bridge reaches the
/// earlier type by its bare name. The generated projects never bridge a type
/// across files in a declaration, so this is the case that catches a fold
/// which drops the earlier files' declared facts.
#[test]
fn declared_schemes_read_the_earlier_files_declared_types() {
    let env = full_bcl_env();
    let project = fold(
        &owned(&[
            ("A.fs", "namespace N\ntype R = { x : int }\n"),
            (
                "B.fs",
                "namespace N\ntype U = K of R | L\ntype S = { r : R }\n",
            ),
            (
                "C.fs",
                "module C\nopen N\nlet k (r : R) = K r\nlet s (v : S) = v.r\n",
            ),
        ]),
        env,
    );
    assert_whole_prefix_facts_are_declared(&project, env);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Over generated multi-file projects (unions, records, generic records,
    /// cases gaining payloads, `[<AutoOpen>]` modules, attributes), and each
    /// edit of them: the whole-prefix facts are a fold over declarations.
    #[test]
    fn whole_prefix_facts_are_a_fold_over_declarations(
        nums in prop::collection::vec(any::<u32>(), 0..400),
    ) {
        let env = full_bcl_env();
        let scenario = generate(nums);
        for snapshot in &scenario.snapshots {
            let sources: Vec<(String, String)> = snapshot
                .iter()
                .enumerate()
                .map(|(i, src)| (format!("F{i}.fs"), src.clone()))
                .collect();
            let project = fold(&sources, env);
            if let Some(divergence) = whole_prefix_facts_divergence(
                &project.files,
                &project.resolved,
                env,
                &project.inferred,
            ) {
                prop_assert!(false, "{divergence}\n{snapshot:#?}");
            }
        }
    }
}
