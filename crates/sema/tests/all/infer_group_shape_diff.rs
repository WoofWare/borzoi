//! Method calls on real BCL method groups, graded against FCS: the regime a
//! call's arguments are checked under is FCS's (#662 L3).
//!
//! FCS checks a method call's arguments under one of three regimes, chosen
//! before any argument is checked (`TcMethodApplication`): when exactly one
//! candidate of the group has the call's shape (`UnifyUniqueOverloading`), its
//! parameters are related to the arguments' types and its return to the
//! call's expected type first, so each argument is checked against its
//! parameter; when several have it, each argument is checked against a fresh
//! type and the call is resolved after; when none has it, the call is an
//! error. How many candidates a group has at a call is not the number of its
//! methods of that many parameters: a `[<ParamArray>]` method is two
//! candidates at exactly its declared count and one at any other it admits,
//! trailing optional or `out` parameters may be omitted only when each is one
//! xor the other, and a single method of one parameter takes a call's several
//! arguments as one tuple. Checking an argument under the wrong regime
//! commits what FCS does not: `both p LIT` against a fresh type fixes `p` to
//! the literal's type, where against an `int` parameter FCS fixes `p : int`.
//!
//! # The programs
//!
//! The groups are read from the env, not listed: every public method name of
//! a handful of BCL types, instance (on `y: string`, `sb: StringBuilder`) and
//! static (`System.String`, `System.Console`, `System.Int32`,
//! `System.IO.Path`, `System.Math`, `System.Char`, `System.Convert`), at every
//! argument count from one to one more than the group's longest method, with
//! a probe at each position and fresh parameters `q0 …` at the others:
//!
//! ```text
//! let gK (y: string) (sb: System.Text.StringBuilder) p q0 q1 = (RECV.M(q0, PROBE, q1), p, q0, q1)
//! ```
//!
//! where `PROBE` is `both p LIT` (`LIT` an `int`, a `string` or a `char`
//! literal) or `idf p`. `p` is open until the call's regime fixes it, so what
//! inference makes of it shows which regime it checked the argument under.
//!
//! # The properties
//!
//! - **Certain implies exact**, over every case: every expression and binder
//!   type inference commits, FCS has, the same.
//! - **Must commit `p`**, where FCS accepts the case and has a ground type for
//!   `p`, in a *plain* group: every method of it non-generic, not a
//!   constructor, of one argument group, with no `byref`, `out`, optional or
//!   `[<ParamArray>]` parameter and every parameter of a type the bridge
//!   carries (a primitive, or a named type that is neither generic nor
//!   nested). There a group's candidates at `n` arguments are exactly its
//!   methods of `n` parameters, and inference knows each one's parameter
//!   types, so it decides the call as FCS does: against the one candidate's
//!   parameter, or against a fresh type.
//!
//! The census of cases by kind of group — plain with one candidate, plain
//! with several, plain with none, and the rest — and by verdict is printed,
//! and each plain kind must reach must-commit points.

use std::collections::BTreeMap;

use borzoi_assembly::{Member, MethodLike, ParamDefault, Primitive, TypeRef};
use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile};
use borzoi_sema::{
    AssemblyEnv, PrecedingTypes, ProjectItems, SyntaxRecovery, infer_file, resolve_file,
};

use crate::common::{GradedDumps, env_usize_or, full_bcl_env, temp_fs_file, try_invoke_fcs_dump};

/// The shared header.
const HEADER: &str = "module GroupShape\n\
                      let idf x = x\n\
                      let both (x: 'a) (y: 'a) = x\n";

/// The receivers whose groups the cases call: how a call spells the receiver,
/// the type's namespace and name, and whether its static members are called.
/// A type the env lacks is skipped.
const RECEIVERS: &[(&str, &[&str], &str, bool)] = &[
    ("y", &["System"], "String", false),
    ("sb", &["System", "Text"], "StringBuilder", false),
    ("System.String", &["System"], "String", true),
    ("System.Console", &["System"], "Console", true),
    ("System.Int32", &["System"], "Int32", true),
    ("System.IO.Path", &["System", "IO"], "Path", true),
    ("System.Math", &["System"], "Math", true),
    ("System.Char", &["System"], "Char", true),
    ("System.Convert", &["System"], "Convert", true),
];

/// The probes, each fixing `p` by what the argument is checked against.
const PROBES: &[&str] = &["both p 1", "both p \"s\"", "both p 'c'", "idf p"];

/// What kind of group a case calls, at its argument count.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    /// A plain group with exactly one method of the call's arity.
    PlainOne,
    /// A plain group with several.
    PlainSeveral,
    /// A plain group with none: FCS reports the call.
    PlainNone,
    /// Any other group: optional, `out`, `byref` or `[<ParamArray>]`
    /// parameters, generic methods, parameters the bridge does not carry, or
    /// a group the env does not hold complete.
    Other,
}

/// Whether a parameter's type is one inference's bridge carries.
fn bridged(ty: &TypeRef) -> bool {
    match ty {
        TypeRef::Primitive(p) => *p != Primitive::Void,
        TypeRef::Named {
            type_args, name, ..
        } => type_args.is_empty() && !name.contains('/'),
        TypeRef::Var { .. } | TypeRef::Array { .. } => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

/// Whether every method of a group is plain (see the module doc).
fn plain(group: &[&MethodLike]) -> bool {
    group.iter().all(|m| {
        m.generic_parameters.is_empty()
            && !m.is_constructor
            && (m.signature.parameters.len() <= 1 || m.arg_group_count == Some(1))
            && m.signature.parameters.iter().all(|p| {
                !p.is_byref
                    && !p.is_out
                    && !p.is_param_array
                    && matches!(p.default, ParamDefault::None)
                    && bridged(&p.ty)
            })
    })
}

/// One generated case.
struct Case {
    text: String,
    kind: Kind,
    group: String,
    probe: &'static str,
    /// The `p` at the case's end, relative to its start.
    p_node: (usize, usize),
}

/// The groups of `RECEIVERS`, each with the cases that call it, at most
/// `per_group` of them, spread over its argument counts, positions and probes.
fn cases(env: &AssemblyEnv, per_group: usize, found: &mut usize) -> Vec<Case> {
    let mut out = Vec::new();
    for &(recv, namespace, name, statics) in RECEIVERS {
        let namespace: Vec<String> = namespace.iter().map(|s| s.to_string()).collect();
        // The test env is the reference pack's core: a type it lacks is
        // skipped, and the sweep asserts most are there.
        let Some(handle) = env.lookup_type(&namespace, name, 0) else {
            continue;
        };
        *found += 1;
        let mut names: Vec<&str> = env
            .entity(handle)
            .members
            .iter()
            .filter_map(|m| match m {
                Member::Method(m)
                    if m.is_static == statics
                        && matches!(m.access, borzoi_assembly::Access::Public)
                        && !m.is_constructor
                        && !["get_", "set_", "add_", "remove_", "op_"]
                            .iter()
                            .any(|pre| m.name.starts_with(pre)) =>
                {
                    Some(m.name.as_str())
                }
                _ => None,
            })
            .collect();
        names.sort();
        names.dedup();
        for method in names {
            let group = if statics {
                env.static_method_group(handle, method)
            } else {
                env.instance_method_group(handle, method)
            };
            let methods: Vec<&MethodLike> = group
                .as_ref()
                .map(|g| g.iter().map(|(_, _, m)| *m).collect())
                .unwrap_or_default();
            let longest = methods
                .iter()
                .map(|m| m.signature.parameters.len())
                .max()
                .unwrap_or(1);
            let is_plain = group.is_some() && plain(&methods);
            let mut shapes = Vec::new();
            for n in 1..=(longest + 1).min(4) {
                for at in 0..n {
                    for probe in PROBES {
                        shapes.push((n, at, *probe));
                    }
                }
            }
            // Spread the kept shapes over the list rather than keep its head.
            let stride = shapes.len().div_ceil(per_group.max(1)).max(1);
            for &(n, at, probe) in shapes.iter().step_by(stride) {
                let kind = if !is_plain {
                    Kind::Other
                } else {
                    match methods
                        .iter()
                        .filter(|m| m.signature.parameters.len() == n)
                        .count()
                    {
                        0 => Kind::PlainNone,
                        1 => Kind::PlainOne,
                        _ => Kind::PlainSeveral,
                    }
                };
                let qs: Vec<String> = (0..n - 1).map(|j| format!("q{j}")).collect();
                let mut args = qs.clone();
                args.insert(at, probe.to_string());
                let mut head = "let gKKK (y: string) (sb: System.Text.StringBuilder) p".to_string();
                for q in &qs {
                    head.push(' ');
                    head.push_str(q);
                }
                let mut body = format!(" = ({recv}.{method}({}), ", args.join(", "));
                let p_at = head.len() + body.len();
                body.push('p');
                for q in &qs {
                    body.push_str(", ");
                    body.push_str(q);
                }
                body.push(')');
                out.push(Case {
                    text: head + &body,
                    kind,
                    group: format!("{recv}.{method}/{n}"),
                    probe,
                    p_node: (p_at, p_at + 1),
                });
            }
        }
    }
    out
}

/// Cases per file.
const CASES_PER_FILE: usize = 24;

#[derive(Debug, Default)]
struct Tally {
    /// Cases by kind, and by whether FCS accepts them.
    cases: BTreeMap<(Kind, bool), usize>,
    /// Must-commit points graded, by kind.
    must: BTreeMap<Kind, usize>,
    /// `p` committed, by kind.
    committed: BTreeMap<Kind, usize>,
    certain: usize,
    uncheckable: usize,
}

#[test]
fn method_calls_check_their_arguments_under_fcss_regime() {
    let per_group = env_usize_or("BORZOI_GROUP_SHAPE_PER_GROUP", 6);
    let env = full_bcl_env();
    let mut found = 0;
    let all = cases(env, per_group, &mut found);
    assert!(
        found * 3 >= RECEIVERS.len() * 2,
        "only {found} of the receivers' types are in the env"
    );
    let mut tally = Tally::default();
    let mut unsound = Vec::new();
    let mut missed = Vec::new();
    for (f, chunk) in all.chunks(CASES_PER_FILE).enumerate() {
        let mut src = HEADER.to_string();
        let mut starts = Vec::new();
        for (k, case) in chunk.iter().enumerate() {
            starts.push(src.len());
            src.push_str(&case.text.replacen("gKKK", &format!("g{:03}", k), 1));
            src.push('\n');
        }
        let parsed = parse(&src);
        assert!(parsed.errors.is_empty(), "{:?}\n{src}", parsed.errors);
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root).expect("impl file");
        let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
        let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());
        let path = temp_fs_file("infer_group_shape", &src);
        let jsons = try_invoke_fcs_dump("types", &path)
            .and_then(|t| try_invoke_fcs_dump("binder-types", &path).map(|b| (t, b)));
        let _ = std::fs::remove_file(&path);
        let Some(dumps) = jsons
            .ok()
            .and_then(|(t, b)| GradedDumps::read(&t, &b, &src, Some(&file)))
        else {
            tally.uncheckable += 1;
            continue;
        };
        let header_lines = HEADER.matches('\n').count() as u32;
        assert!(
            dumps.errors.iter().all(|e| e.line > header_lines),
            "FCS rejects the header in file {f}: {:?}",
            dumps.errors
        );
        let span = |r: borzoi_cst::syntax::TextRange| {
            (u32::from(r.start()) as usize, u32::from(r.end()) as usize)
        };
        let ours_types: BTreeMap<(usize, usize), String> = inferred
            .types()
            .iter()
            .map(|(r, t)| (span(*r), t.render(env)))
            .collect();
        let ours_binders: BTreeMap<(usize, usize), String> = inferred
            .def_types()
            .iter()
            .map(|(d, t)| (span(resolved.def(*d).range), t.render(env)))
            .collect();
        for (table, ours, theirs) in [
            ("node", &ours_types, &dumps.types),
            ("binder", &ours_binders, &dumps.binders),
        ] {
            for (&at, ty) in ours {
                if dumps.is_ungraded(at) {
                    continue;
                }
                tally.certain += 1;
                if theirs.get(&at) != Some(ty) {
                    let line_start = src[..at.0].rfind('\n').map_or(0, |i| i + 1);
                    let line_end = src[at.0..].find('\n').map_or(src.len(), |i| at.0 + i);
                    unsound.push(format!(
                        "{table} `{}` ours {ty}, FCS {:?}: {}",
                        &src[at.0..at.1],
                        theirs.get(&at),
                        &src[line_start..line_end]
                    ));
                }
            }
        }
        let line_of = |offset: usize| src[..offset].matches('\n').count() as u32 + 1;
        for (case, &start) in chunk.iter().zip(&starts) {
            let clean = !dumps.errors.iter().any(|e| e.line == line_of(start));
            *tally.cases.entry((case.kind, clean)).or_default() += 1;
            let at = (start + case.p_node.0, start + case.p_node.1);
            if ours_types.contains_key(&at) {
                *tally.committed.entry(case.kind).or_default() += 1;
            }
            // With several candidates FCS checks the probe against a fresh
            // type, so `both p LIT` fixes `p` there and `idf p` leaves it to
            // the resolution, which FCS may take on an open argument and
            // inference does not.
            let decided = match case.kind {
                Kind::PlainOne => true,
                Kind::PlainSeveral => case.probe.starts_with("both"),
                Kind::PlainNone | Kind::Other => false,
            };
            if !(decided && clean) {
                continue;
            }
            let Some(fcs) = dumps.types.get(&at) else {
                continue;
            };
            if fcs.contains('\'') || dumps.is_ungraded(at) {
                continue;
            }
            *tally.must.entry(case.kind).or_default() += 1;
            if ours_types.get(&at) != Some(fcs) {
                let text = &src[start..start + case.text.len()];
                missed.push(format!(
                    "{:?} {}: `p` FCS {fcs}, ours {:?}, census {:?}: {text}",
                    case.kind,
                    case.group,
                    ours_types.get(&at),
                    inferred
                        .incompleteness()
                        .get(2 + starts.iter().position(|&s| s == start).unwrap())
                ));
            }
        }
    }
    eprintln!("group-shape sweep: {} cases, {tally:?}", all.len());
    assert!(
        unsound.is_empty(),
        "{} commits FCS does not have:\n{}",
        unsound.len(),
        unsound.join("\n")
    );
    assert!(
        missed.is_empty(),
        "{} `p`s FCS fixes in a plain group, missed:\n{}",
        missed.len(),
        missed.join("\n")
    );
    let files = all.len().div_ceil(CASES_PER_FILE);
    assert!(
        tally.uncheckable * 10 <= files,
        "FCS could not check {} of {files} files",
        tally.uncheckable
    );
    for kind in [Kind::PlainOne, Kind::PlainSeveral] {
        let n = tally.must.get(&kind).copied().unwrap_or(0);
        assert!(
            n >= 10,
            "only {n} must-commit points in {kind:?} groups: {tally:?}"
        );
    }
    for kind in [Kind::PlainNone, Kind::Other] {
        let n: usize = [true, false]
            .iter()
            .map(|&clean| tally.cases.get(&(kind, clean)).copied().unwrap_or(0))
            .sum();
        assert!(n >= 20, "only {n} cases in {kind:?} groups: {tally:?}");
    }
}
