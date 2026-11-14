//! Argument checks decided at the argument's **entry**, as FCS decides them,
//! graded against FCS on generated programs.
//!
//! FCS checks an application `f a` against an expected type by first
//! relating `f`'s result to that type (`Propagate`), and only then checking
//! `a` against `f`'s domain. So when an argument is itself an application, its
//! result is related to the outer domain before its own arguments are
//! checked: in `g (singleton y)` with `g : obj list -> int` and `y : string`,
//! `singleton`'s element type becomes `obj` and `y` coerces to it, where
//! walking `singleton y` first would fix it to `string` and then fail against
//! `obj list`. A tuple argument against a tuple domain, a lambda against a
//! function domain, an `if` or `match` branch against the expected type, a
//! body against its return annotation, and a method's argument against the
//! parameter of the one overload its arity leaves (`UnifyUniqueOverloading`)
//! likewise see the expected type before their parts are checked. Stage L2 of
//! #662 decides each argument check at that point, under the binding's
//! faithful prefix (the flag that says inference still knows FCS's table), and
//! treats an expected type it does not decide against as unknown from that
//! point on.
//!
//! # The programs
//!
//! Most cases are one function of a generated file of the form
//!
//! ```text
//! let cK (y: string) (n: int) (b: bool) x p = (idf 3, SINK (ARG), EXTRA…, idf "w", p)
//! ```
//!
//! `SINK` takes one of a handful of domains (`obj list`, `string list`,
//! `int`, `obj`, `int * string`, `string -> int`, `obj option`), and `ARG` is
//! generated against that domain from generic combinators (`idf`,
//! `singleton`, `both : 'a -> 'a -> 'a`, `fst`, `Some`, `app`, the pipe),
//! tuples, `if` and `match` over the domain, method calls whose arguments hold
//! checks of their own (`y.Insert(ARG, "z")`), and leaves (`y`, `n`, `p`,
//! literals, `box`). The `EXTRA` elements, when there are any, are method
//! calls with checks in their arguments — one against a tuple-typed parameter
//! (`xs.Add((I, S))`), one against `obj` (`(box 1).Equals((I, S))`) — and a
//! parameter fixed to `obj -> int` and then applied (`applyObj x, x (A)`;
//! the head takes `x` only then).
//! `p` may be used several times, so the first relation FCS applies to it is
//! the one that fixes it. With a probability drawn per file, a leaf is
//! replaced by one of the wrong type (an ill-typed argument), and a
//! subexpression is put under a lambda (`app (fun z -> A) B`), which inference
//! does not model. `idf 3` and `idf "w"` are **witnesses**: each is typed only
//! by its own argument check, so whether it is committed shows whether the
//! checks around it fired. `p` is open until something fixes it, so its node
//! and the function's binder show what the checks did to it.
//!
//! The other cases are a body under a return annotation,
//! `let cK (y: string) (n: int) (b: bool) p : T = ARG`, with `ARG` generated
//! against `T` (`let c4 p : string = both p (gi p)`).
//!
//! # The properties
//!
//! - **Certain implies exact**, everywhere: every expression and binder type
//!   we commit, FCS has, the same, on clean and ill-typed cases alike.
//! - **Must commit**, per point:
//!   - the witness *before* the sink, whatever follows it: what comes after it
//!     cannot change what FCS decided at it, so the prefix is still faithful
//!     there;
//!   - the witness after the sink, `p`'s node, and the binders, in a case FCS
//!     accepts built only from the plain constructs — no lambda, no ill-typed
//!     leaf, no second use of `p`, no branch, method call, applied parameter
//!     or return annotation: every check in it is one inference models,
//!     decided where FCS decides it. The richer constructs are graded by
//!     certain-implies-exact alone, since L2 may soundly decline inside them.
//!
//!   Each only where FCS's type is ground.
//!
//! The generator's regime — its depth, and how often it injects each
//! construct — is drawn per file, and the sweep asserts it reached every
//! construct and both verdicts in quantity.

use std::collections::BTreeMap;

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile};
use borzoi_sema::{PrecedingTypes, ProjectItems, SyntaxRecovery, infer_file, resolve_file};

use crate::common::{GradedDumps, env_usize_or, full_bcl_env, temp_fs_file, try_invoke_fcs_dump};
use crate::infer_local_let_diff::Rng;

/// The shared header: the combinators and sinks the cases apply.
const HEADER: &str = "module EntryOrder\n\
                      let idf x = x\n\
                      let singleton x = List.singleton x\n\
                      let both (x: 'a) (y: 'a) = x\n\
                      let app (f: 'a -> 'b) (x: 'a) = f x\n\
                      let applyObj (k: obj -> int) = k\n\
                      let monos (t: string) = 2\n\
                      let mono (b: bool) = 1\n\
                      let g (xs: obj list) = 0\n\
                      let gs (xs: string list) = 0\n\
                      let gi (i: int) = 0\n\
                      let go (o: obj) = 0\n\
                      let gt (t: int * string) = 0\n\
                      let gf (k: string -> int) = 0\n\
                      let gpo (o: obj option) = 0\n\
                      let xs = ResizeArray<int * string>()\n";

/// The types the generator builds an argument against.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Want {
    Int,
    Str,
    Obj,
    List(Box<Want>),
    Opt(Box<Want>),
    /// `int * string`.
    Pair,
    /// `string -> int`.
    StrToInt,
}

impl Want {
    /// The type as F# spells it in an annotation.
    fn spelled(&self) -> String {
        match self {
            Want::Int => "int".into(),
            Want::Str => "string".into(),
            Want::Obj => "obj".into(),
            Want::List(t) => format!("{} list", t.spelled()),
            Want::Opt(t) => format!("{} option", t.spelled()),
            Want::Pair => "(int * string)".into(),
            Want::StrToInt => "(string -> int)".into(),
        }
    }
}

/// Each sink, and its domain.
fn sinks() -> Vec<(&'static str, Want)> {
    vec![
        ("g", Want::List(Box::new(Want::Obj))),
        ("gs", Want::List(Box::new(Want::Str))),
        ("gi", Want::Int),
        ("go", Want::Obj),
        ("gt", Want::Pair),
        ("gf", Want::StrToInt),
        ("gpo", Want::Opt(Box::new(Want::Obj))),
    ]
}

/// What a generated case contains, for the distribution the sweep asserts
/// and for the must-commit rule.
#[derive(Debug, Default, Clone, Copy)]
struct Features {
    lambda: bool,
    ill_typed: bool,
    /// A string or int leaf under an `obj` element of a combinator's result:
    /// the shape whose entry and exit orders differ.
    coerced_inside: bool,
    nested: bool,
    infix: bool,
    tuple: bool,
    open_param: bool,
    /// `p` used more than once.
    multi_p: bool,
    /// An `if` or `match` over the expected type.
    branch: bool,
    /// A method call whose argument holds a check.
    method_arg: bool,
    /// A parameter fixed to `obj -> int`, then applied.
    applied_fn: bool,
    /// The body is under a return annotation.
    annotated: bool,
}

impl Features {
    /// Whether the case uses only the plain constructs, so that its points
    /// after the sink are must-commit where FCS accepts it.
    fn plain(&self) -> bool {
        !(self.lambda
            || self.ill_typed
            || self.multi_p
            || self.branch
            || self.method_arg
            || self.applied_fn
            || self.annotated)
    }
}

/// The generator's regime for one file.
#[derive(Debug, Clone, Copy)]
struct Regime {
    depth: usize,
    lambda_pct: usize,
    ill_pct: usize,
    /// The chance that a leaf may be a further use of `p`.
    multi_p_pct: usize,
    branch_pct: usize,
    method_pct: usize,
    /// The chance of each of up to two extra elements.
    extra_pct: usize,
    annotated_pct: usize,
}

struct ArgGen<'r> {
    rng: &'r mut Rng,
    regime: Regime,
    features: Features,
    /// How many times the case has used `p`.
    p_uses: usize,
}

impl ArgGen<'_> {
    /// An expression FCS checks against `want`: well-typed unless an
    /// ill-typed leaf is injected or `p` is used at two types. `under_obj_element`
    /// says the position is an `obj` element of a combinator's instantiated
    /// result, where a leaf of another type coerces only because the domain
    /// reached it first.
    fn expr(&mut self, want: &Want, depth: usize, under_obj_element: bool) -> String {
        if depth > 0 && self.rng.chance(self.regime.lambda_pct) {
            self.features.lambda = true;
            let body = self.expr(want, depth - 1, false);
            let x = self.leaf(&Want::Int, false);
            return format!("app (fun z -> {body}) ({x})");
        }
        if depth > 0 && self.rng.chance(self.regime.branch_pct) {
            self.features.branch = true;
            let a = self.expr(want, depth - 1, under_obj_element);
            let c = self.expr(want, depth - 1, under_obj_element);
            return if self.rng.chance(50) {
                format!("(if b then {a} else {c})")
            } else {
                format!("(match n with 0 -> {a} | _ -> {c})")
            };
        }
        if depth > 0 && self.rng.chance(self.regime.method_pct) {
            match want {
                Want::Str => {
                    self.features.method_arg = true;
                    return if self.rng.chance(50) {
                        let i = self.expr(&Want::Int, depth - 1, false);
                        format!("y.Insert({i}, \"z\")")
                    } else {
                        let s = self.expr(&Want::Str, depth - 1, false);
                        format!("y.Insert(0, {s})")
                    };
                }
                Want::Obj => {
                    self.features.method_arg = true;
                    let i = self.expr(&Want::Int, depth - 1, false);
                    let s = self.expr(&Want::Str, depth - 1, false);
                    return format!("(box 1).Equals(({i}, {s}))");
                }
                _ => {}
            }
        }
        if depth == 0 || self.rng.chance(25) {
            return self.leaf(want, under_obj_element);
        }
        let d = depth - 1;
        match want {
            Want::List(t) if self.rng.chance(50) => {
                self.features.nested = true;
                let inner = self.expr(t, d, **t == Want::Obj);
                if self.rng.chance(25) {
                    self.features.infix = true;
                    format!("({inner}) |> singleton")
                } else {
                    format!("singleton ({inner})")
                }
            }
            Want::Opt(t) if self.rng.chance(50) => {
                self.features.nested = true;
                let inner = self.expr(t, d, **t == Want::Obj);
                format!("Some ({inner})")
            }
            Want::Pair if self.rng.chance(50) => {
                self.features.tuple = true;
                let a = self.expr(&Want::Int, d, false);
                let b = self.expr(&Want::Str, d, false);
                format!("({a}, {b})")
            }
            _ => {
                self.features.nested = true;
                match self.rng.below(4) {
                    0 => format!("idf ({})", self.expr(want, d, under_obj_element)),
                    1 => {
                        let a = self.expr(want, d, under_obj_element);
                        let b = self.expr(want, d, under_obj_element);
                        format!("both ({a}) ({b})")
                    }
                    2 => {
                        self.features.tuple = true;
                        let a = self.expr(want, d, under_obj_element);
                        let b = self.expr(&Want::Int, d, false);
                        format!("fst ({a}, {b})")
                    }
                    _ => {
                        self.features.infix = true;
                        format!("({}) |> idf", self.expr(want, d, under_obj_element))
                    }
                }
            }
        }
    }

    fn leaf(&mut self, want: &Want, under_obj_element: bool) -> String {
        let p_allowed = self.p_uses == 0 || self.rng.chance(self.regime.multi_p_pct);
        if p_allowed && self.rng.chance(20) {
            self.p_uses += 1;
            self.features.open_param = true;
            self.features.multi_p |= self.p_uses > 1;
            return "p".into();
        }
        let ill = self.rng.chance(self.regime.ill_pct);
        if ill {
            self.features.ill_typed = true;
        }
        match (want, ill) {
            (Want::Int, false) | (Want::Str, true) => {
                if self.rng.chance(50) { "n" } else { "1" }.into()
            }
            (Want::Str, false) | (Want::Int, true) => {
                if self.rng.chance(50) { "y" } else { "\"s\"" }.into()
            }
            (Want::Obj, _) => {
                // Any value is an `obj`; a string or int here is a coercion.
                match self.rng.below(3) {
                    0 => "(box 1)".into(),
                    1 => {
                        self.features.coerced_inside |= under_obj_element;
                        "y".into()
                    }
                    _ => {
                        self.features.coerced_inside |= under_obj_element;
                        "n".into()
                    }
                }
            }
            (Want::List(t), false) => format!("singleton ({})", self.leaf(t, **t == Want::Obj)),
            (Want::List(_), true) => "[true]".into(),
            (Want::Opt(t), false) => format!("Some ({})", self.leaf(t, **t == Want::Obj)),
            (Want::Opt(_), true) => "(Some true)".into(),
            (Want::Pair, false) => {
                self.features.tuple = true;
                let a = self.leaf(&Want::Int, false);
                let b = self.leaf(&Want::Str, false);
                format!("({a}, {b})")
            }
            (Want::Pair, true) => "(\"s\", 1)".into(),
            (Want::StrToInt, false) => if self.rng.chance(50) {
                "String.length"
            } else {
                "monos"
            }
            .into(),
            (Want::StrToInt, true) => "mono".into(),
        }
    }

    /// An element after the sink: a method call whose argument holds checks,
    /// or a parameter fixed to `obj -> int` and then applied.
    fn extra(&mut self, depth: usize) -> String {
        match self.rng.below(4) {
            0 => {
                self.features.method_arg = true;
                let i = self.expr(&Want::Int, depth, false);
                format!("y.Insert({i}, \"z\")")
            }
            1 => {
                self.features.method_arg = true;
                self.features.tuple = true;
                let i = self.expr(&Want::Int, depth, false);
                let s = self.expr(&Want::Str, depth, false);
                format!("xs.Add(({i}, {s}))")
            }
            2 => {
                self.features.method_arg = true;
                self.features.tuple = true;
                let i = self.expr(&Want::Int, depth, false);
                let s = self.expr(&Want::Str, depth, false);
                format!("(box 1).Equals(({i}, {s}))")
            }
            _ => {
                self.features.applied_fn = true;
                let a = self.expr(&Want::Obj, depth, false);
                format!("applyObj x, x ({a})")
            }
        }
    }
}

/// One generated case.
#[derive(Debug, Clone)]
struct Case {
    /// Its offset in the file, and its text (one line, no newline).
    start: usize,
    text: String,
    features: Features,
    /// The ranges of its points, relative to `start`: the witness before the
    /// sink, the witness after it, and the `p` node at the end. A case under a
    /// return annotation has none of them.
    before: Option<(usize, usize)>,
    after: Option<(usize, usize)>,
    p_node: Option<(usize, usize)>,
    /// The function's name and its parameter `p`, relative to `start`.
    name: (usize, usize),
    p_binder: (usize, usize),
}

fn regime_for(seed: u64) -> Regime {
    let mut rng = Rng(seed ^ 0x0e47_0e4d);
    Regime {
        depth: [1, 2, 3][rng.below(3)],
        lambda_pct: [0, 10, 30][rng.below(3)],
        ill_pct: [0, 8, 25][rng.below(3)],
        multi_p_pct: [0, 40, 80][rng.below(3)],
        branch_pct: [0, 10, 25][rng.below(3)],
        method_pct: [0, 10, 25][rng.below(3)],
        extra_pct: [0, 25, 50][rng.below(3)],
        annotated_pct: [0, 15, 30][rng.below(3)],
    }
}

/// Cases per file.
const CASES_PER_FILE: usize = 24;

fn file_for(seed: u64) -> (String, Vec<Case>) {
    let regime = regime_for(seed);
    let mut rng = Rng(seed ^ 0xe7e7_0d0d_a5a5);
    let mut src = HEADER.to_string();
    let mut cases = Vec::new();
    let sinks = sinks();
    for k in 0..CASES_PER_FILE {
        let (sink, domain) = &sinks[rng.below(sinks.len())];
        let annotated = rng.chance(regime.annotated_pct);
        let extras = if annotated {
            0
        } else {
            usize::from(rng.chance(regime.extra_pct)) + usize::from(rng.chance(regime.extra_pct))
        };
        let mut g = ArgGen {
            rng: &mut rng,
            regime,
            features: Features::default(),
            p_uses: 0,
        };
        // The body first, then the head: `x` is a parameter only where an
        // element applies it, since FCS generalises an unused one and the
        // function's type is then not ground.
        let mut body = String::new();
        let (before, after, p_node);
        if annotated {
            g.features.annotated = true;
            // `both p (ARG)` half the time, so that `p` is related to the
            // annotation before the argument is checked (`c4`).
            let expr = if g.rng.chance(50) {
                g.p_uses += 1;
                g.features.open_param = true;
                let a = g.expr(domain, regime.depth, false);
                format!("both p ({a})")
            } else {
                g.expr(domain, regime.depth, false)
            };
            body.push_str(&format!(" : {} = {expr}", domain.spelled()));
            before = None;
            after = None;
            p_node = None;
        } else {
            let arg = g.expr(domain, regime.depth, false);
            let extra: Vec<String> = (0..extras).map(|_| g.extra(regime.depth)).collect();
            body.push_str(" = (");
            let before_at = body.len();
            body.push_str("idf 3");
            before = Some((before_at, body.len()));
            body.push_str(&format!(", {sink} ({arg}), "));
            for e in &extra {
                body.push_str(e);
                body.push_str(", ");
            }
            let after_at = body.len();
            body.push_str("idf \"w\"");
            after = Some((after_at, body.len()));
            body.push_str(", ");
            let p_at = body.len();
            body.push('p');
            p_node = Some((p_at, body.len()));
            body.push(')');
        }
        let x = if g.features.applied_fn { " x" } else { "" };
        let head = format!("let c{k:03} (y: string) (n: int) (b: bool){x} p");
        let name = (4, 8);
        let p_binder = (head.len() - 1, head.len());
        let shift = |r: Option<(usize, usize)>| r.map(|(s, e)| (s + head.len(), e + head.len()));
        let (before, after, p_node) = (shift(before), shift(after), shift(p_node));
        let text = head + &body;
        let features = g.features;
        let start = src.len();
        src.push_str(&text);
        src.push('\n');
        cases.push(Case {
            start,
            text,
            features,
            before,
            after,
            p_node,
            name,
            p_binder,
        });
    }
    (src, cases)
}

/// The sweep's tallies, asserted for liveness.
#[derive(Debug, Default)]
struct Tally {
    cases: usize,
    clean: usize,
    rejected: usize,
    with: BTreeMap<&'static str, usize>,
    /// Must-commit points graded, by kind.
    must: BTreeMap<&'static str, usize>,
    /// Commits graded by certain-implies-exact.
    certain: usize,
    uncheckable: usize,
}

#[test]
fn argument_checks_are_decided_at_the_arguments_entry() {
    let files = env_usize_or("BORZOI_ENTRY_ORDER_FILES", 24);
    let env = full_bcl_env();
    let mut tally = Tally::default();
    let mut unsound: Vec<String> = Vec::new();
    let mut missing: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    for seed in 0..files as u64 {
        let (src, cases) = file_for(seed);
        let parsed = parse(&src);
        assert!(parsed.errors.is_empty(), "{:?}\n{src}", parsed.errors);
        let recovery = SyntaxRecovery::of(&parsed);
        let file = ImplFile::cast(parsed.root).expect("impl file");
        let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
        let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());

        let path = temp_fs_file("infer_entry_order", &src);
        let jsons = try_invoke_fcs_dump("types", &path)
            .and_then(|t| try_invoke_fcs_dump("binder-types", &path).map(|b| (t, b)));
        let _ = std::fs::remove_file(&path);
        let Ok((types_json, binders_json)) = jsons else {
            tally.uncheckable += 1;
            continue;
        };
        let Some(dumps) = GradedDumps::read(&types_json, &binders_json, &src, Some(&file)) else {
            tally.uncheckable += 1;
            continue;
        };
        // The header is well-typed.
        let header_lines = HEADER.matches('\n').count() as u32;
        assert!(
            dumps.errors.iter().all(|e| e.line > header_lines),
            "FCS rejects the header: {:?}",
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
        // Certain implies exact, over the whole file.
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
        let census = inferred.incompleteness();
        assert!(census.len() >= CASES_PER_FILE, "one entry per case");
        let first_case = census.len() - CASES_PER_FILE;
        for (k, case) in cases.iter().enumerate() {
            let reasons = &census[first_case + k];
            tally.cases += 1;
            let line = line_of(case.start);
            let clean = !dumps.errors.iter().any(|e| e.line == line);
            if clean {
                tally.clean += 1;
            } else {
                tally.rejected += 1;
            }
            let f = case.features;
            for (name, on) in [
                ("lambda", f.lambda),
                ("ill-typed", f.ill_typed),
                ("coerced-inside", f.coerced_inside),
                ("nested", f.nested),
                ("infix", f.infix),
                ("tuple", f.tuple),
                ("open-param", f.open_param),
                ("multi-use p", f.multi_p),
                ("branch", f.branch),
                ("method argument", f.method_arg),
                ("applied parameter", f.applied_fn),
                ("annotated", f.annotated),
                (
                    "clean-coerced-inside",
                    clean && f.coerced_inside && f.plain(),
                ),
                ("clean-plain", clean && f.plain()),
            ] {
                if on {
                    *tally.with.entry(name).or_default() += 1;
                }
            }
            let abs = |(s, e): (usize, usize)| (case.start + s, case.start + e);
            let mut grade = |kind: &'static str, at: (usize, usize), table: &str| {
                let (ours, theirs) = match table {
                    "node" => (&ours_types, &dumps.types),
                    _ => (&ours_binders, &dumps.binders),
                };
                let Some(fcs) = theirs.get(&at) else { return };
                if fcs.contains('\'') || dumps.is_ungraded(at) {
                    return;
                }
                *tally.must.entry(kind).or_default() += 1;
                if ours.get(&at) != Some(fcs) {
                    missing.entry(kind).or_default().push(format!(
                        "`{}` FCS {fcs}, ours {:?}{}, census {reasons:?}: {}",
                        &src[at.0..at.1],
                        ours.get(&at),
                        if clean { "" } else { " (FCS rejects the case)" },
                        case.text
                    ));
                }
            };
            if let Some(before) = case.before {
                grade("witness before", abs(before), "node");
            }
            // After the sink, only where the case is built from the plain
            // constructs: an injected ill-typed leaf may be one FCS converts
            // (an `obj` element takes `[true]`), but it may be unmodelled
            // too, which ends the faithful prefix; and inside a branch, a
            // method argument or under a second use of `p`, L2 may soundly
            // decline.
            if clean && f.plain() {
                if let Some(after) = case.after {
                    grade("witness after", abs(after), "node");
                }
                if let Some(p_node) = case.p_node {
                    grade("p node", abs(p_node), "node");
                }
                grade("function binder", abs(case.name), "binder");
                grade("p binder", abs(case.p_binder), "binder");
            }
        }
    }
    eprintln!("entry-order sweep: {tally:?}");
    let missing_report: Vec<String> = missing
        .iter()
        .map(|(kind, items)| {
            let mut items = items.clone();
            items.sort_by_key(String::len);
            format!(
                "{kind}: {} missed, e.g.\n  {}",
                items.len(),
                items
                    .iter()
                    .take(4)
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("\n  ")
            )
        })
        .collect();
    assert!(
        unsound.is_empty() && missing.is_empty(),
        "{} commits FCS does not have:\n{}\n\ncommits FCS makes where the prefix is faithful, \
         missed:\n{}",
        unsound.len(),
        unsound.join("\n"),
        missing_report.join("\n")
    );
    assert!(
        tally.uncheckable * 4 <= files,
        "FCS could not check {} files",
        tally.uncheckable
    );
    // The sweep reached every construct, and both verdicts, in quantity.
    let min = files * CASES_PER_FILE / 40;
    for name in [
        "lambda",
        "ill-typed",
        "coerced-inside",
        "nested",
        "infix",
        "tuple",
        "open-param",
        "multi-use p",
        "branch",
        "method argument",
        "applied parameter",
        "annotated",
        "clean-coerced-inside",
        "clean-plain",
    ] {
        let n = tally.with.get(name).copied().unwrap_or(0);
        assert!(n >= min, "only {n} cases with {name}: {tally:?}");
    }
    assert!(
        tally.clean >= min * 4 && tally.rejected >= min,
        "the sweep should reach both verdicts in quantity: {tally:?}"
    );
    for kind in [
        "witness before",
        "witness after",
        "p node",
        "function binder",
        "p binder",
    ] {
        let n = tally.must.get(kind).copied().unwrap_or(0);
        assert!(
            n >= min,
            "only {n} must-commit points of kind {kind}: {tally:?}"
        );
    }
}

/// The generated files parse, and each case's points are where the grader
/// looks for them.
#[test]
fn generated_cases_parse_and_place_their_points() {
    for seed in 0..64 {
        let (src, cases) = file_for(seed);
        let parsed = parse(&src);
        assert!(parsed.errors.is_empty(), "{:?}\n{src}", parsed.errors);
        for case in &cases {
            let at = |(s, e): (usize, usize)| &case.text[s..e];
            if let Some(before) = case.before {
                assert_eq!(at(before), "idf 3", "{}", case.text);
            }
            if let Some(after) = case.after {
                assert_eq!(at(after), "idf \"w\"", "{}", case.text);
            }
            if let Some(p_node) = case.p_node {
                assert_eq!(at(p_node), "p", "{}", case.text);
            }
            assert_eq!(
                case.before.is_none(),
                case.features.annotated,
                "{}",
                case.text
            );
            assert!(at(case.name).starts_with('c'), "{}", case.text);
            assert_eq!(at(case.p_binder), "p", "{}", case.text);
            assert_eq!(&src[case.start..case.start + case.text.len()], case.text);
        }
    }
}
