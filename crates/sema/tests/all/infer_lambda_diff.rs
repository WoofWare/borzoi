//! Lambdas, graded against FCS.
//!
//! FCS checks `fun p1 … pn -> body` against an expected type one parameter
//! at a time (`TcIteratedLambdas`): it splits the expected type into a domain
//! and a result (`UnifyFunctionType`: a function type is taken apart, a
//! variable is equated with a fresh function type, anything else is an error
//! that abandons the lambda), checks the parameter's pattern against the
//! domain, and goes on with the result; the body is checked against the last
//! result. A module-level binding's leading lambdas are its own parameters:
//! FCS folds them into the binding's arity, and its typed tree has no lambda
//! node for them.
//!
//! The grid crosses lambda shapes with the positions a lambda reaches —
//! a binding's right-hand side, a local's, an argument against an open, a
//! function and a non-function domain, a return annotation, a branch, a
//! tuple element, a callee — and holds every node and binder we type to
//! FCS's, with a must-commit obligation on the cell's binder (and, where the
//! position records it, the lambda's own node) in each modelled cell FCS
//! checks cleanly.

use std::collections::HashMap;

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange, TextSize};
use borzoi_sema::{PrecedingTypes, ProjectItems, SyntaxRecovery, infer_file, resolve_file};

use crate::common::{GradedDumps, full_bcl_env, temp_fs_file, try_invoke_fcs_dump};

/// The functions and values the cells use.
const HEADER: &str = "module M\n\
                      let app (f: 'a -> 'b) (x: 'a) = f x\n\
                      let idf x = x\n\
                      let gf (k: string -> int) = 0\n\
                      let go (o: obj) = 0\n\
                      let y = \"s\"\n\
                      let b = true\n";

/// `(id, lambda, modelled, ground)`. `modelled` says every parameter and
/// every part of the body is in the modelled subset; `ground` that the
/// lambda's type is ground whatever its context, so that a context FCS
/// generalises, or whose value restriction defaults a generic lambda to
/// `obj`, still gives it its own type. Whether FCS accepts the cell is read
/// from FCS.
const LAMBDAS: &[(&str, &str, bool, bool)] = &[
    ("ident", "fun x -> x", true, false),
    ("annot", "fun (x: int) -> x", true, true),
    ("annotAccess", "fun (s: string) -> s.Length", true, true),
    ("unit", "fun () -> 1", true, true),
    ("wild", "fun _ -> 2", true, false),
    ("parenName", "fun (x) -> x", true, false),
    ("two", "fun (a: int) (c: string) -> (a, c)", true, true),
    ("twoOpen", "fun a c -> (c, a)", true, false),
    (
        "nested",
        "fun (a: int) -> fun (c: string) -> (c, a)",
        true,
        true,
    ),
    ("outer", "fun x -> (x, y)", true, false),
    // The receiver is known at the access only where the domain is.
    ("access", "fun s -> s.Length", true, false),
    ("ifBody", "fun x -> if b then x else x", true, false),
    ("ifParam", "fun c -> if c then 1 else 2", true, true),
    (
        "matchBody",
        "fun (n: int) -> match n with 0 -> \"z\" | _ -> \"o\"",
        true,
        true,
    ),
    ("letBody", "fun (n: int) -> let m = n in (m, n)", true, true),
    ("appBody", "fun (s: string) -> idf s", true, true),
    (
        "lambdaBody",
        "fun (s: string) -> app (fun t -> t) s",
        true,
        true,
    ),
    ("annotMismatch", "fun (x: int) -> \"s\"", true, true),
    ("unitString", "fun () -> \"s\"", true, true),
    // FCS elaborates a tuple parameter through a `let`, which reshapes the
    // enclosing function's typed tree; not modelled.
    ("tuple", "fun (a, c) -> a", false, false),
    ("dup", "fun x x -> x", false, false),
    ("op", "fun x -> x + 1", false, false),
    // A body that records a local before it declines.
    (
        "letThenList",
        "fun (n: int) -> let m = n in [m]",
        false,
        false,
    ),
];

/// When a cell's binder must be committed, where FCS checks the line cleanly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Obligation {
    /// Always.
    Always,
    /// Only for a lambda whose type is ground on its own: the position
    /// generalises a generic lambda, or its value restriction defaults one
    /// to `obj`.
    Ground,
}

/// `(id, template, obligation, records_node)`: where the lambda `{L}` sits,
/// what the cell must commit, and whether FCS has a node at the lambda that
/// inference must commit too.
const CONTEXTS: &[(&str, &str, Obligation, bool)] = &[
    ("value", "let f{i} = {L}\n", Obligation::Ground, false),
    ("paren", "let f{i} = ({L})\n", Obligation::Ground, false),
    ("body", "let f{i} () = {L}\n", Obligation::Always, false),
    (
        "local",
        "let f{i} () = let g = {L} in g\n",
        Obligation::Ground,
        true,
    ),
    ("idf", "let f{i} = idf ({L})\n", Obligation::Ground, false),
    (
        "pipe",
        "let f{i} = ({L}) |> idf\n",
        Obligation::Ground,
        false,
    ),
    (
        "app",
        "let f{i} c = app ({L}) c\n",
        Obligation::Always,
        false,
    ),
    ("sink", "let f{i} = gf ({L})\n", Obligation::Always, false),
    (
        "objSink",
        "let f{i} = go ({L})\n",
        Obligation::Always,
        false,
    ),
    (
        "ret",
        "let f{i} () : int -> int = {L}\n",
        Obligation::Always,
        false,
    ),
    ("callee", "let f{i} = ({L}) 1\n", Obligation::Ground, true),
    // Applied to more arguments than it takes, which FCS rejects whole,
    // keeping nothing inside the application; or to an argument of the wrong
    // type, which it reports at the argument, keeping the lambda.
    (
        "overApplied",
        "let f{i} = ({L}) 1 2\n",
        Obligation::Ground,
        false,
    ),
    (
        "calleeString",
        "let f{i} = ({L}) \"s\"\n",
        Obligation::Ground,
        false,
    ),
    (
        "branch",
        "let f{i} = if b then ({L}) else ({L})\n",
        Obligation::Ground,
        false,
    ),
    (
        "element",
        "let f{i} = (({L}), 1)\n",
        Obligation::Ground,
        true,
    ),
];

#[derive(Default, Debug)]
struct Tally {
    cells: usize,
    committed: usize,
    committed_erroring: usize,
    nodes_obligated: usize,
    exprs: usize,
    binders: usize,
    /// Cells FCS's dump cannot check even alone: an error FCS does not
    /// recover from in a binding's own right-hand side leaves it no
    /// implementation file at all.
    unchecked: Vec<String>,
    missed: Vec<String>,
}

/// One cell: its declaration, its binder's name, whether its binder is
/// obligated, the lambda's span in the declaration where its node is
/// obligated, and its label.
struct Cell {
    text: String,
    name: String,
    modelled: bool,
    ground: bool,
    obligation: Obligation,
    lambda: Option<(usize, usize)>,
    label: String,
}

/// What [`grade`] read: our binders by `(name, line)`, our nodes, and FCS's
/// dumps.
type Graded = (
    HashMap<(String, u32), String>,
    HashMap<(usize, usize), String>,
    GradedDumps,
);

/// Grade `source` against FCS: every node and binder we commit is FCS's, the
/// same. `None` where FCS's dump cannot check the file.
fn grade(source: &str, tally: &mut Tally) -> Option<Graded> {
    let parsed = parse(source);
    assert!(parsed.errors.is_empty(), "{:?}\n{source}", parsed.errors);
    let recovery = SyntaxRecovery::of(&parsed);
    let file = ImplFile::cast(parsed.root).expect("impl file");
    let env = full_bcl_env();
    let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
    let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());
    let path = temp_fs_file("infer_lambda", source);
    let jsons = try_invoke_fcs_dump("types", &path)
        .and_then(|t| try_invoke_fcs_dump("binder-types", &path).map(|b| (t, b)));
    let _ = std::fs::remove_file(&path);
    let (types_json, binders_json) = jsons.ok()?;
    let dumps = GradedDumps::read(&types_json, &binders_json, source, Some(&file))
        .expect("every declaration is placeable");
    let line_of = |offset: usize| source[..offset].matches('\n').count() as u32 + 1;
    let mut nodes = HashMap::new();
    for (range, ty) in inferred.types() {
        let key = (
            u32::from(range.start()) as usize,
            u32::from(range.end()) as usize,
        );
        if dumps.is_ungraded(key) {
            continue;
        }
        let ours = ty.render(env);
        let theirs = dumps.types.get(&key).unwrap_or_else(|| {
            panic!(
                "we inferred `{ours}` at {key:?} (`{}`, line {}) but FCS reports no node \
                 there\n{source}",
                &source[key.0..key.1],
                line_of(key.0)
            )
        });
        assert_eq!(
            &ours,
            theirs,
            "expression type mismatch at {key:?} (`{}`, line {})\n{source}",
            &source[key.0..key.1],
            line_of(key.0)
        );
        tally.exprs += 1;
        nodes.insert(key, ours);
    }
    let mut ours_by_name = HashMap::new();
    for (def_id, ty) in inferred.def_types() {
        let def = resolved.def(*def_id);
        let key = (
            u32::from(def.range.start()) as usize,
            u32::from(def.range.end()) as usize,
        );
        if dumps.is_ungraded(key) {
            continue;
        }
        let ours = ty.render(env);
        let theirs = dumps.binders.get(&key).unwrap_or_else(|| {
            panic!(
                "we inferred `{ours}` for binder `{}` at {key:?} (line {}) but FCS reports \
                 no binder there\n{source}",
                def.spelling(env),
                line_of(key.0)
            )
        });
        assert_eq!(
            &ours,
            theirs,
            "binder type mismatch for `{}` at {key:?} (line {})\n{source}",
            def.spelling(env),
            line_of(key.0)
        );
        assert!(
            !dumps.hides_constraint(key, &ours),
            "binder `{}` typed `{ours}`, which FCS constrains\n{source}",
            def.spelling(env)
        );
        tally.binders += 1;
        ours_by_name.insert((def.spelling(env).into_owned(), line_of(key.0)), ours);
    }
    Some((ours_by_name, nodes, dumps))
}

/// Grade `cells` in one file after [`HEADER`], and hold each to its
/// obligations. A file FCS's dump cannot check is graded again a cell at a
/// time.
fn check(cells: &[&Cell], tally: &mut Tally) {
    let mut source = HEADER.to_string();
    let mut placed = Vec::new();
    for cell in cells {
        placed.push((source.matches('\n').count() as u32 + 1, source.len()));
        source.push_str(&cell.text);
    }
    let Some((ours_by_name, nodes, dumps)) = grade(&source, tally) else {
        if let [cell] = cells {
            tally.unchecked.push(cell.label.clone());
        } else {
            for cell in cells {
                check(&[cell], tally);
            }
        }
        return;
    };
    let line_of = |offset: usize| source[..offset].matches('\n').count() as u32 + 1;
    for (cell, &(line, start)) in cells.iter().zip(&placed) {
        tally.cells += 1;
        let erroring = dumps.errors.iter().any(|e| e.line == line);
        let fcs = dumps.binders.iter().find_map(|(&(s, e), ty)| {
            (line_of(s) == line && source[s..e] == cell.name).then(|| ty.clone())
        });
        let obligated = cell.modelled
            && !erroring
            && match cell.obligation {
                Obligation::Always => true,
                Obligation::Ground => cell.ground,
            };
        match ours_by_name.get(&(cell.name.clone(), line)) {
            Some(_) => {
                tally.committed += 1;
                tally.committed_erroring += usize::from(erroring);
            }
            None if obligated => {
                tally.missed.push(format!(
                    "{}: binder, FCS `{}`",
                    cell.label,
                    fcs.unwrap_or_default()
                ));
            }
            None => {}
        }
        if !obligated {
            continue;
        }
        let Some(at) = cell.lambda.map(|(s, e)| (start + s, start + e)) else {
            continue;
        };
        let Some(theirs) = dumps.types.get(&at) else {
            continue;
        };
        if theirs.contains('\'') {
            continue;
        }
        tally.nodes_obligated += 1;
        if !nodes.contains_key(&at) {
            tally.missed.push(format!(
                "{}: lambda node `{}`, FCS `{theirs}`",
                cell.label,
                &source[at.0..at.1]
            ));
        }
    }
}

fn program(context: &(&str, &str, Obligation, bool)) -> Vec<Cell> {
    let (cid, template, obligation, records_node) = *context;
    LAMBDAS
        .iter()
        .enumerate()
        .map(|(i, (id, lambda, modelled, ground))| {
            let text = template.replace("{i}", &i.to_string());
            let hole = text.find("{L}").expect("a template has a hole");
            Cell {
                text: text.replace("{L}", lambda),
                name: format!("f{i}"),
                modelled: *modelled,
                ground: *ground,
                obligation,
                lambda: records_node.then_some((hole, hole + lambda.len())),
                label: format!("{cid}/{id}"),
            }
        })
        .collect()
}

#[test]
fn every_lambda_in_every_context_agrees_with_fcs() {
    let mut tally = Tally::default();
    for context in CONTEXTS {
        let cells = program(context);
        check(&cells.iter().collect::<Vec<_>>(), &mut tally);
    }
    eprintln!("{tally:?}");
    assert!(
        tally.missed.is_empty(),
        "{} obligations declined:\n{}",
        tally.missed.len(),
        tally.missed.join("\n")
    );
    assert!(tally.committed >= 150, "{tally:?}");
    assert!(tally.nodes_obligated >= 20, "{tally:?}");
    assert!(
        tally.committed_erroring >= 5,
        "the ill-typed cells commit nothing: {tally:?}"
    );
}

/// A lambda's parameter typed from its domain reaches a member access in the
/// body: the member is resolved there, and the access is typed, where FCS
/// fixes the domain before it checks the lambda — an application's argument
/// against a known parameter, or the pipe's, whose left operand is checked
/// first. A lambda checked before what fixes its domain — applied where it is
/// written, or an argument before the one that fixes the type variable it
/// shares — has its parameter open at the access, which FCS reports
/// (FS0072): nothing is resolved there.
#[test]
fn a_parameter_typed_by_its_domain_resolves_a_member_in_the_body() {
    let cases: &[(&str, &str)] = &[
        ("let f1 = gf (fun s -> s.Length)", "System.Int32"),
        (
            "let f2 (xs: string list) = xs |> List.map (fun s -> s.Length)",
            "Microsoft.FSharp.Collections.FSharpList<System.String> -> \
             Microsoft.FSharp.Collections.FSharpList<System.Int32>",
        ),
        (
            "let f3 (xs: string list) = List.map (fun (s: string) -> s.Length) xs",
            "Microsoft.FSharp.Collections.FSharpList<System.String> -> \
             Microsoft.FSharp.Collections.FSharpList<System.Int32>",
        ),
        ("let f5 = (fun s -> s.Length) \"s\"", ""),
        (
            "let f6 (z: string) = z |> (fun s -> s.Length)",
            "System.String -> System.Int32",
        ),
        (
            "let f7 = gf (fun s -> s |> (fun t -> t.Length))",
            "System.Int32",
        ),
        (
            "let f4 (z: string) = app (fun s -> s.Length) z",
            // `app`'s lambda is checked before `z`: `s` is open at the
            // access, which FCS reports (FS0072); nothing is claimed.
            "",
        ),
    ];
    let env = full_bcl_env();
    for &(case, binder) in cases {
        let src = format!("{HEADER}{case}\n");
        let mut tally = Tally::default();
        let (ours, _, dumps) = grade(&src, &mut tally).expect("FCS checks the case");
        let line = HEADER.matches('\n').count() as u32 + 1;
        let name = case["let ".len()..].split(' ').next().expect("a name");
        let committed = ours.get(&(name.to_string(), line));
        let at = src.rfind("Length").expect("an access");
        let range = TextRange::new(
            TextSize::from(u32::try_from(at).expect("small")),
            TextSize::from(u32::try_from(at + "Length".len()).expect("small")),
        );
        let parsed = parse(&src);
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root).expect("impl file");
        let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
        let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());
        let member = inferred.member_resolution_at(range);
        if binder.is_empty() {
            assert!(
                member.is_none(),
                "{case}: `Length` resolved on a receiver open at the access"
            );
            continue;
        }
        assert!(
            dumps.errors.is_empty(),
            "{case}: FCS rejects it: {:?}",
            dumps.errors
        );
        assert_eq!(committed.map(String::as_str), Some(binder), "{case}");
        assert!(member.is_some(), "{case}: `Length` not resolved");
    }
}
