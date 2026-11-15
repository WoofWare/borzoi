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
//! the head takes `x` only then), and three forms whose own expected type FCS
//! relates at their entry, each mentioning `p` both where that relation fixes
//! it and where a check inside would fix it otherwise: a conversion
//! (`both p (int (both (p) (S)))`), a loop (`both p (while p do ())`) and a
//! `let` pattern of structure (`let (u, w) = pick p (both (p) (S)) in u`).
//! `p` may be used several times, so the first relation FCS applies to it is
//! the one that fixes it. With a probability drawn per file, a leaf is
//! replaced by one of the wrong type (an ill-typed argument), and a
//! subexpression is put under a lambda (`app (fun z -> A) B`), which inference
//! does not model. `idf 3` and `idf "w"` are **witnesses**: each is typed only
//! by its own argument check, so whether it is committed shows whether the
//! checks around it fired. `p` is open until something fixes it, so its node
//! and the function's binder show what the checks did to it.
//!
//! Two further axes reach what happens once the faithful prefix has ended.
//! With a probability drawn per file a construct inference does not model is
//! put before the sink (`(p : int)`, `(fun () -> gt p)`, `(while false do
//! ignore (gi p))`, `y.Insert(0, p)`, or one that leaves `p` alone), most of
//! them fixing `p` in FCS where inference cannot see it. And up to two
//! **term-position contexts** follow the extras: a term whose type FCS may
//! know and inference, after such a construct, does not (`idf p`, `[y]`, `p
//! 1`, …) related to a type of the context's own — a `let` pattern with a term
//! position (`let () = z`, `let (a, ()) = (1, T)`), a union case pattern, a
//! match pattern of structure, a condition, an argument, an operand, a
//! branch, a receiver. These are mostly ill-typed: FCS types the term, then
//! rejects the context, and inference must not type the term by the context
//! (`let x2 p = ((p : string), (let z = idf p in (let () = z in z)), p)`
//! keeps `z : string`, #774).
//!
//! # The alphabet
//!
//! The random cases reach forms by what the generator happens to draw.
//! [`every_arm_in_every_context_is_certain_implies_exact`] reaches them all,
//! by construction: one case per cell of every modelled form ([`Arm`], one
//! per arm of `Gen::infer_construct`, the dispatching arms split) × every
//! context that hands it an expected type ([`Context`]) × the prefix
//! faithful or lost before it, each graded certain-implies-exact against
//! FCS, and each checked to parse as the arm its cell names.
//! [`the_alphabet_names_every_arm_inference_models`] reads
//! `Gen::infer_construct`'s arms from its source, so an arm inference gains
//! fails it until the alphabet has a form for it.
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
//!     leaf, no second use of `p`, no branch, method call, applied parameter,
//!     return annotation, construct ending the prefix or term-position
//!     context: every check in it is one inference models,
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
use borzoi_cst::syntax::{AstNode, Expr, ImplFile, Pat, SyntaxKind, SyntaxNode, TextRange};
use borzoi_sema::{
    Incomplete, PrecedingTypes, ProjectFile, ProjectItems, SourceFile, SyntaxRecovery, infer_file,
    infer_project, qualified_names, resolve_file, resolve_project_files,
};

use crate::common::{GradedDumps, env_usize_or, full_bcl_env, temp_fs_file, try_invoke_fcs_dump};
use crate::infer_local_let_diff::Rng;

/// The shared header: the combinators and sinks the cases apply.
const HEADER: &str = "module EntryOrder\n\
                      let idf x = x\n\
                      let singleton x = List.singleton x\n\
                      let both (x: 'a) (y: 'a) = x\n\
                      let pick (x: 'a) (y: 'b) = x\n\
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
                      let xs = ResizeArray<int * string>()\n\
                      type U1 = U1 of (obj * int)\n\
                      type U2 = U2 of obj * int\n\
                      type 'a W = WA of 'a | WN\n\
                      type K = static member M (s: string) = s\n";

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
    /// A built-in conversion (`int (S)`), whose result its signature fixes.
    conversion: bool,
    /// A `while` loop or a `let` pattern of structure in an argument.
    statement_form: bool,
    /// A construct inference does not model before the sink, which ends the
    /// binding's faithful prefix there ([`ArgGen::loss`]).
    lost: bool,
    /// A context that relates a term to a type of its own — a `let`
    /// pattern with a term position, a match pattern, a condition, an
    /// argument ([`ArgGen::context`]).
    term_position: bool,
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
            || self.annotated
            || self.conversion
            || self.statement_form
            || self.lost
            || self.term_position)
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
    /// The chance of a construct that ends the prefix before the sink.
    lost_pct: usize,
    /// The chance of each of up to two term-position contexts.
    context_pct: usize,
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
        if depth > 0 && *want == Want::Int && self.rng.chance(self.regime.method_pct) {
            self.features.conversion = true;
            let s = self.expr(&Want::Str, depth - 1, false);
            return format!("int ({s})");
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

    /// A construct inference does not model, put before the sink so that
    /// everything after it is walked once the binding's faithful prefix has
    /// ended. Most fix `p` in FCS — to `int`, `string`, `int * string` or
    /// `int -> string` — through what inference does not see (a type
    /// annotation on an expression, a lambda's body, a loop's body, a method
    /// argument); the rest leave `p` as it was.
    fn loss(&mut self) -> String {
        self.features.lost = true;
        let fixed = match self.rng.below(4) {
            0 => ("int", "gi"),
            1 => ("string", "monos"),
            2 => ("(int * string)", "gt"),
            _ => ("(int -> string)", ""),
        };
        let form = match self.rng.below(7) {
            0 | 1 => format!("(p : {})", fixed.0),
            2 if !fixed.1.is_empty() => format!("(fun () -> {} p)", fixed.1),
            3 if !fixed.1.is_empty() => format!("(while false do ignore ({} p))", fixed.1),
            4 => "y.Insert(0, p)".into(),
            5 => return "(y : string)".into(),
            6 => return "(fun () -> 1)".into(),
            _ => format!("(p : {})", fixed.0),
        };
        self.p_uses += 1;
        self.features.open_param = true;
        self.features.multi_p |= self.p_uses > 1;
        form
    }

    /// A term whose type FCS may know where inference, once the prefix has
    /// ended, does not: one built from `p`, or a list expression (which
    /// inference does not model) of a parameter whose type both know.
    fn term(&mut self, depth: usize) -> String {
        let mut uses_p = true;
        let t = match self.rng.below(18) {
            // Method calls, whose node FCS types by the expected type itself
            // under a `let` pattern, resolved or not.
            14 => {
                uses_p = false;
                "y.Insert(0, \"s\")".into()
            }
            15 => {
                uses_p = false;
                "System.Int32.TryParse(y)".into()
            }
            16 => {
                uses_p = false;
                "K.M(y)".into()
            }
            17 => "y.Insert(0, p)".into(),
            0 => "p".into(),
            1 => "idf p".into(),
            2 => "both p p".into(),
            3 => "(if b then p else p)".into(),
            4 => "(match n with 0 -> p | _ -> p)".into(),
            5 => "fst (p, 1)".into(),
            6 => "singleton p".into(),
            7 => "Some p".into(),
            8 => "(p, 1)".into(),
            9 => "[p]".into(),
            10 => "p 1".into(),
            11 => {
                uses_p = false;
                if self.rng.chance(50) { "[y]" } else { "[n]" }.into()
            }
            12 => {
                uses_p = false;
                let want = if self.rng.chance(50) {
                    Want::Int
                } else {
                    Want::Str
                };
                format!("idf ({})", self.expr(&want, depth, false))
            }
            _ => "(0; p)".into(),
        };
        if uses_p {
            self.p_uses += 1;
            self.features.open_param = true;
            self.features.multi_p |= self.p_uses > 1;
        }
        t
    }

    /// A context that relates a term ([`Self::term`]) to a type of its own,
    /// by each form that carries an expected type or a pattern: a `let`
    /// pattern with a term position (`()`, or a tuple holding one), a union
    /// case pattern, a match pattern of structure, a condition, an
    /// application's or a method's argument, an operator's or a conversion's
    /// operand, a statement, a branch, a union case's field, a loop
    /// condition, a member access's receiver. Many are ill-typed at the type
    /// FCS gives the term, which is the point: FCS types the term before it
    /// rejects the context, and inference must not type it by the context.
    fn context(&mut self, depth: usize) -> String {
        self.features.term_position = true;
        let t = self.term(depth);
        match self.rng.below(28) {
            0 => format!("(let () = {t} in 0)"),
            1 => format!("(let z = {t} in (let () = z in z))"),
            2 => format!("(let (a, ()) = (1, {t}) in a)"),
            3 => format!("(let ((), a) = ({t}, 1) in a)"),
            4 => format!("(let (a, b) = {t} in (let () = a in b))"),
            5 => format!("(let z = {t} in (let (a, ()) = (z, z) in a))"),
            6 => format!("(match {t} with 1 -> 1 | _ -> 2)"),
            7 => format!("(match {t} with \"s\" -> 1 | _ -> 2)"),
            8 => format!("(match {t} with (1, _) -> 1 | _ -> 2)"),
            9 => format!("(if {t} then 1 else 2)"),
            10 => format!("gi ({t})"),
            11 => format!("monos ({t})"),
            12 => format!("y.Insert({t}, \"z\")"),
            13 => format!("-({t})"),
            14 => format!("int ({t})"),
            15 => format!("({t}; 0)"),
            16 => format!("(if b then {t})"),
            17 => format!("(if b then {t} else 1)"),
            18 => format!("(if b then \"s\" else {t})"),
            19 => format!("U1 ({t}, 1)"),
            20 => format!("(while {t} do ())"),
            21 => format!("({t}).Length"),
            22 => format!("both ({t}) 1"),
            23 => format!("(let (WA ()) = WA ({t}) in 0)"),
            24 => format!("(let z = WA ({t}) in (let (WA ()) = z in 0))"),
            25 => format!("(let z = {t} in (match z with 1 -> 1 | _ -> 2))"),
            26 => format!("(let z = {t} in (if z then 1 else 2))"),
            _ => format!("(let z = {t} in (let (a, b) = z in a))"),
        }
    }

    /// An element after the sink: a method call whose argument holds checks,
    /// or a parameter fixed to `obj -> int` and then applied.
    fn extra(&mut self, depth: usize) -> String {
        // The last three relate an expected type at a form's entry that a
        // decision inside the form would otherwise run ahead of: each mentions
        // `p` where the entry relation fixes it, and again where a check would
        // fix it otherwise.
        match self.rng.below(17) {
            16 => {
                // A union case whose result fails its expected type: FCS
                // never checks its fields, so they fix nothing of `p`.
                self.features.statement_form = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                let case = if self.rng.chance(50) { "U1" } else { "U2" };
                if self.rng.chance(50) {
                    format!("gi ({case} (p, 1)), monos p")
                } else {
                    format!("(let () = {case} (p, 1) in 0), monos p")
                }
            }
            15 => {
                // An unmodelled construct may fix `p` (to `int`, here), after
                // which nothing may bind it otherwise: a later pattern meets
                // it at `unit`, which FCS rejects.
                self.features.statement_form = true;
                self.p_uses += 3;
                self.features.multi_p = true;
                "(idf p, (p : int), (let () = p in ()))".into()
            }
            13 => {
                // A pattern of structure the right-hand side's branches do
                // not fit: FCS keeps nothing of them at their own types.
                self.features.statement_form = true;
                let a = self.expr(&Want::Int, depth, false);
                format!("(let () = (if b then {a} else 2) in 0)")
            }
            14 => {
                self.features.statement_form = true;
                let a = self.expr(&Want::Int, depth, false);
                format!("(let () = (match n with 0 -> {a} | _ -> 2) in 0)")
            }
            12 => {
                // An `if` without `else` is `unit`, a strict equality FCS
                // takes before its branch, failing here against `int`.
                self.features.statement_form = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                "gi (if b then p), monos p".into()
            }
            11 => {
                // An operator's operand is checked against the type its
                // signature shares with its result, fixed here to `int64`.
                self.features.conversion = true;
                self.p_uses += 1;
                self.features.multi_p |= self.p_uses > 1;
                "both (int64 0) (-(if b then p else 1))".into()
            }
            9 => {
                // A homogeneous operator shares its operand's type with its
                // result, related before the operand is checked.
                self.features.conversion = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                "both p (-(monos p))".into()
            }
            10 => {
                // A method is looked up on its receiver at the dot, before
                // its arguments: on an unknown receiver FCS reports FS0072.
                self.features.method_arg = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                "p.Substring(monos p)".into()
            }
            7 => {
                // A pattern of structure over branches: the `else` branch is
                // checked against the type the `then` branch fixed, and
                // coerces to it.
                self.features.statement_form = true;
                self.p_uses += 1;
                self.features.multi_p |= self.p_uses > 1;
                let a = self.expr(&Want::Str, depth, false);
                format!("(let (u, w) = (if b then (p, 1) else ({a}, 2)) in u)")
            }
            8 => {
                // A union case's one tuple-typed field against two fields:
                // each is one field to flex, or not.
                self.features.statement_form = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                let case = if self.rng.chance(50) { "U1" } else { "U2" };
                format!("{case} (p, 1), gi p")
            }
            4 => {
                // The loop's `unit` is related before its condition.
                self.features.statement_form = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                "both p (while p do ())".into()
            }
            5 => {
                // The pattern's tuple is related to `pick`'s result before
                // its arguments are checked.
                self.features.statement_form = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                let a = self.expr(&Want::Str, depth, false);
                format!("(let (u, w) = pick p (both (p) ({a})) in u)")
            }
            6 => {
                // The conversion's `int` is related before its operand.
                self.features.conversion = true;
                self.p_uses += 2;
                self.features.multi_p = true;
                let a = self.expr(&Want::Str, depth, false);
                format!("both p (int (both (p) ({a})))")
            }
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
    let mut regime = Regime {
        depth: [1, 2, 3][rng.below(3)],
        lambda_pct: [0, 10, 30][rng.below(3)],
        ill_pct: [0, 8, 25][rng.below(3)],
        multi_p_pct: [0, 40, 80][rng.below(3)],
        branch_pct: [0, 10, 25][rng.below(3)],
        method_pct: [0, 10, 25][rng.below(3)],
        extra_pct: [10, 40, 70][rng.below(3)],
        annotated_pct: [0, 15, 30][rng.below(3)],
        // Half the files reach past the prefix's end; the other half keep the
        // plain cases the must-commit points need.
        lost_pct: 0,
        context_pct: 0,
    };
    if rng.chance(50) {
        regime.lost_pct = [30, 60][rng.below(2)];
        regime.context_pct = [40, 70][rng.below(2)];
    }
    regime
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
        let lost = !annotated && rng.chance(regime.lost_pct);
        let contexts = if annotated {
            0
        } else {
            usize::from(rng.chance(regime.context_pct))
                + usize::from(rng.chance(regime.context_pct))
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
            let loss = lost.then(|| g.loss());
            let arg = g.expr(domain, regime.depth, false);
            let mut extra: Vec<String> = (0..extras).map(|_| g.extra(regime.depth)).collect();
            extra.extend((0..contexts).map(|_| g.context(regime.depth)));
            body.push_str(" = (");
            let before_at = body.len();
            body.push_str("idf 3");
            before = Some((before_at, body.len()));
            if let Some(loss) = &loss {
                body.push_str(", ");
                body.push_str(loss);
            }
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
    let files = env_usize_or("BORZOI_ENTRY_ORDER_FILES", 32);
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
                ("conversion", f.conversion),
                ("statement form", f.statement_form),
                ("lost before", f.lost),
                ("term position", f.term_position),
                ("lost before a term position", f.lost && f.term_position),
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
        "conversion",
        "statement form",
        "lost before",
        "term position",
        "lost before a term position",
        "clean-coerced-inside",
        "clean-plain",
    ] {
        let n = tally.with.get(name).copied().unwrap_or(0);
        // A clean case with a coercion inside needs a lambda-free,
        // ill-typed-free draw that reaches an `obj` element: rarer than the
        // rest by about half.
        let floor = if name == "clean-coerced-inside" {
            min / 3
        } else {
            min
        };
        assert!(n >= floor, "only {n} cases with {name}: {tally:?}");
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

// ---------------------------------------------------------------------------
// The alphabet: every modelled form in every expected-carrying context, with
// the prefix faithful and with it lost before the form.
// ---------------------------------------------------------------------------

/// A form inference models: one arm of `Gen::infer_construct`, with the
/// arms that dispatch on what they hold split by it — a literal from `()`,
/// an `if` with an `else` from one without, an application by what it
/// applies, a dotted name by its head, a `let` by its pattern.
///
/// [`Arm::variant`] names the `Expr` variant each matches, and
/// [`the_alphabet_names_every_arm_inference_models`] holds the set of them to
/// the arms `Gen::infer_construct` has, read from its source: an arm added
/// there with no form here fails it, and so does a form here whose arm
/// inference does not have.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Arm {
    Literal,
    Unit,
    Ident,
    Paren,
    Tuple,
    If,
    ElselessIf,
    Match,
    Lambda,
    While,
    /// A value applied to an argument.
    Apply,
    /// An infix operator's application (`a |> f`).
    Infix,
    /// A built-in conversion (`int x`).
    Convert,
    /// A built-in prefix operator (`-x`).
    Operator,
    MethodCall,
    /// A union case applied to its field.
    CaseApply,
    /// `v.Member`, whose head is a value.
    MemberAccess,
    /// `M.v`, whose head is a module.
    ModuleValue,
    DotGet,
    /// `let x = … in …`.
    Let,
    /// `let (…) = … in …`, a pattern of structure.
    LetPattern,
    Sequential,
}

impl Arm {
    const ALL: [Arm; 22] = [
        Arm::Literal,
        Arm::Unit,
        Arm::Ident,
        Arm::Paren,
        Arm::Tuple,
        Arm::If,
        Arm::ElselessIf,
        Arm::Match,
        Arm::Lambda,
        Arm::While,
        Arm::Apply,
        Arm::Infix,
        Arm::Convert,
        Arm::Operator,
        Arm::MethodCall,
        Arm::CaseApply,
        Arm::MemberAccess,
        Arm::ModuleValue,
        Arm::DotGet,
        Arm::Let,
        Arm::LetPattern,
        Arm::Sequential,
    ];

    /// The arm's position in [`Self::ALL`]: an exhaustive match, so a new
    /// arm cannot compile without a place there.
    fn index(self) -> usize {
        match self {
            Arm::Literal => 0,
            Arm::Unit => 1,
            Arm::Ident => 2,
            Arm::Paren => 3,
            Arm::Tuple => 4,
            Arm::If => 5,
            Arm::ElselessIf => 6,
            Arm::Match => 7,
            Arm::Lambda => 8,
            Arm::While => 9,
            Arm::Apply => 10,
            Arm::Infix => 11,
            Arm::Convert => 12,
            Arm::Operator => 13,
            Arm::MethodCall => 14,
            Arm::CaseApply => 15,
            Arm::MemberAccess => 16,
            Arm::ModuleValue => 17,
            Arm::DotGet => 18,
            Arm::Let => 19,
            Arm::LetPattern => 20,
            Arm::Sequential => 21,
        }
    }

    /// The `Expr` variant `Gen::infer_construct` matches this arm on.
    fn variant(self) -> &'static str {
        match self {
            Arm::Literal | Arm::Unit => "Const",
            Arm::Ident => "Ident",
            Arm::Paren => "Paren",
            Arm::Tuple => "Tuple",
            Arm::If | Arm::ElselessIf => "IfThenElse",
            Arm::Match => "Match",
            Arm::Lambda => "Fun",
            Arm::While => "While",
            Arm::Apply
            | Arm::Infix
            | Arm::Convert
            | Arm::Operator
            | Arm::MethodCall
            | Arm::CaseApply => "App",
            Arm::MemberAccess | Arm::ModuleValue => "LongIdent",
            Arm::DotGet => "DotGet",
            Arm::Let | Arm::LetPattern => "LetOrUse",
            Arm::Sequential => "Sequential",
        }
    }

    /// A form of this arm, its parts drawn from `g` ([`ArgGen::term`]): terms
    /// whose type FCS may know where inference does not.
    fn production(self, g: &mut ArgGen<'_>, depth: usize) -> String {
        match self {
            Arm::Literal => ["1", "\"s\"", "true"][g.rng.below(3)].into(),
            Arm::Unit => "()".into(),
            Arm::Ident => {
                if g.rng.chance(50) {
                    g.p_uses += 1;
                    "p".into()
                } else {
                    ["y", "n"][g.rng.below(2)].into()
                }
            }
            Arm::Paren => format!("({})", g.term(depth)),
            Arm::Tuple => format!("{}, 1", g.term(depth)),
            Arm::If => format!("if b then {} else {}", g.term(depth), g.term(depth)),
            Arm::ElselessIf => format!("if b then {}", g.term(depth)),
            Arm::Match => format!(
                "match n with 0 -> {} | _ -> {}",
                g.term(depth),
                g.term(depth)
            ),
            Arm::Lambda => format!("fun () -> {}", g.term(depth)),
            Arm::While => format!("while b do ignore ({})", g.term(depth)),
            Arm::Apply => format!("idf ({})", g.term(depth)),
            Arm::Infix => format!("({}) |> idf", g.term(depth)),
            Arm::Convert => format!("int ({})", g.term(depth)),
            Arm::Operator => format!("-({})", g.term(depth)),
            Arm::MethodCall => format!("y.Insert(n, {})", g.term(depth)),
            Arm::CaseApply => format!("Some ({})", g.term(depth)),
            Arm::MemberAccess => {
                if g.rng.chance(50) {
                    g.p_uses += 1;
                    "p.Length".into()
                } else {
                    "y.Length".into()
                }
            }
            Arm::ModuleValue => "List.empty".into(),
            Arm::DotGet => format!("({}).Length", g.term(depth)),
            Arm::Let => format!("let z = {} in z", g.term(depth)),
            Arm::LetPattern => format!("let (a, ()) = ({}, ()) in a", g.term(depth)),
            Arm::Sequential => format!("ignore 1; {}", g.term(depth)),
        }
    }
}

/// The arm an expression is, or `None` for a form inference does not model.
/// An exhaustive match over the union's `Expr`, so a variant the parser
/// gains cannot compile without being placed here.
fn arm_of(e: &Expr) -> Option<Arm> {
    match e {
        Expr::Const(c) => Some(if c.syntax().text().to_string().trim() == "()" {
            Arm::Unit
        } else {
            Arm::Literal
        }),
        Expr::Ident(_) => Some(Arm::Ident),
        Expr::Paren(_) => Some(Arm::Paren),
        Expr::Tuple(t) => (!t.is_struct()).then_some(Arm::Tuple),
        Expr::IfThenElse(i) => Some(if i.else_branch().is_some() {
            Arm::If
        } else {
            Arm::ElselessIf
        }),
        Expr::Match(_) => Some(Arm::Match),
        Expr::Fun(_) => Some(Arm::Lambda),
        Expr::While(_) => Some(Arm::While),
        Expr::App(a) if a.is_infix() || a.is_bracket_indexer() => None,
        Expr::App(a) => Some(match a.func()? {
            Expr::App(inner) if inner.is_infix() => Arm::Infix,
            Expr::DotGet(_) => Arm::MethodCall,
            Expr::LongIdent(li) => {
                let segments = li.long_ident()?.idents().count();
                if segments >= 2 {
                    Arm::MethodCall
                } else {
                    Arm::Operator
                }
            }
            Expr::Ident(i) => match i.ident()?.text() {
                "int" | "int64" | "string" => Arm::Convert,
                "Some" | "WA" | "U1" | "U2" => Arm::CaseApply,
                _ => Arm::Apply,
            },
            _ => Arm::Apply,
        }),
        Expr::LongIdent(li) => {
            let head = li.long_ident()?.idents().next()?;
            Some(if matches!(head.text(), "List" | "Option" | "Seq") {
                Arm::ModuleValue
            } else {
                Arm::MemberAccess
            })
        }
        Expr::DotGet(_) => Some(Arm::DotGet),
        Expr::LetOrUse(l) if l.is_bang() || l.is_use() || l.is_rec() => None,
        Expr::LetOrUse(l) => {
            let named = l
                .bindings()
                .next()
                .and_then(|b| b.pat())
                .is_some_and(|p| matches!(p, Pat::Named(_)));
            Some(if named { Arm::Let } else { Arm::LetPattern })
        }
        Expr::Sequential(_) => Some(Arm::Sequential),
        Expr::MeasureLit(_)
        | Expr::Null(_)
        | Expr::Typar(_)
        | Expr::Dynamic(_)
        | Expr::DotLambda(_)
        | Expr::DotIndexedGet(_)
        | Expr::TypeApp(_)
        | Expr::IndexRange(_)
        | Expr::IndexFromEnd(_)
        | Expr::AddressOf(_)
        | Expr::New(_)
        | Expr::ObjExpr(_)
        | Expr::InferredUpcast(_)
        | Expr::InferredDowncast(_)
        | Expr::Lazy(_)
        | Expr::Assert(_)
        | Expr::Fixed(_)
        | Expr::Assign(_)
        | Expr::Typed(_)
        | Expr::TypeTest(_)
        | Expr::Upcast(_)
        | Expr::Downcast(_)
        | Expr::Cons(_)
        | Expr::JoinIn(_)
        | Expr::InterpString(_)
        | Expr::Quote(_)
        | Expr::InlineIl(_)
        | Expr::TraitCall(_)
        | Expr::StaticOptimization(_)
        | Expr::LibraryOnlyFieldGet(_)
        | Expr::DotMissing(_)
        | Expr::Computation(_)
        | Expr::Record(_)
        | Expr::AnonRecd(_)
        | Expr::ArrayOrList(_)
        | Expr::Yield(_)
        | Expr::DoBang(_)
        | Expr::Do(_)
        | Expr::MatchLambda(_)
        | Expr::MatchBang(_)
        | Expr::WhileBang(_)
        | Expr::ForEach(_)
        | Expr::For(_)
        | Expr::Try(_) => None,
    }
}

/// A position that hands an expression an expected type, as FCS's checking
/// order does ([`Context::template`]): each [`Expected`] state, reached
/// through each form that passes one down.
///
/// [`Expected`]: the walk's `Expected` in `borzoi_sema::infer`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Context {
    /// A `let`'s right-hand side: no expected type.
    LetRhs,
    /// An application's argument: its domain.
    Argument,
    /// An `if`'s branch, under an application's domain.
    BranchUnderArgument,
    /// An `else` branch: the type its `then` branch fixed.
    Else,
    /// A later `match` arm: the type the first arm fixed.
    LaterArm,
    /// A `()` pattern's right-hand side: an equality.
    UnitPattern,
    /// A tuple element under a pattern of structure: an equality, split.
    TuplePattern,
    /// A method's argument: a type inference does not know.
    MethodArg,
    /// An operator's operand: a type its signature shares.
    Operand,
    /// A conversion's operand: a fresh type.
    ConvertOperand,
    /// A statement: a fresh type, related to `unit` after.
    Statement,
    /// A `match`'s scrutinee: no expected type.
    Scrutinee,
    /// A member access's receiver: no expected type.
    Receiver,
    /// A union case's field: its (loosened) type.
    CaseField,
    /// A body under a return annotation.
    Annotated,
}

impl Context {
    const ALL: [Context; 15] = [
        Context::LetRhs,
        Context::Argument,
        Context::BranchUnderArgument,
        Context::Else,
        Context::LaterArm,
        Context::UnitPattern,
        Context::TuplePattern,
        Context::MethodArg,
        Context::Operand,
        Context::ConvertOperand,
        Context::Statement,
        Context::Scrutinee,
        Context::Receiver,
        Context::CaseField,
        Context::Annotated,
    ];

    /// The context's position in [`Self::ALL`]: an exhaustive match, so a
    /// new context cannot compile without a place there.
    fn index(self) -> usize {
        match self {
            Context::LetRhs => 0,
            Context::Argument => 1,
            Context::BranchUnderArgument => 2,
            Context::Else => 3,
            Context::LaterArm => 4,
            Context::UnitPattern => 5,
            Context::TuplePattern => 6,
            Context::MethodArg => 7,
            Context::Operand => 8,
            Context::ConvertOperand => 9,
            Context::Statement => 10,
            Context::Scrutinee => 11,
            Context::Receiver => 12,
            Context::CaseField => 13,
            Context::Annotated => 14,
        }
    }

    /// The text around the hole, `{H}` marking it, always in parentheses of
    /// its own so that every form fits it; [`Context::Annotated`] is the
    /// case's head instead ([`alphabet_case`]).
    fn template(self) -> &'static str {
        match self {
            Context::LetRhs => "(let z = ({H}) in z)",
            Context::Argument => "gi ({H})",
            Context::BranchUnderArgument => "gi (if b then ({H}) else 1)",
            Context::Else => "(let z = (if b then 1 else ({H})) in z)",
            Context::LaterArm => "(let z = (match n with 0 -> 1 | _ -> ({H})) in z)",
            Context::UnitPattern => "(let () = ({H}) in 0)",
            Context::TuplePattern => "(let (a, ()) = (({H}), ()) in a)",
            Context::MethodArg => "y.Insert(0, ({H}))",
            Context::Operand => "-({H})",
            Context::ConvertOperand => "int ({H})",
            Context::Statement => "(({H}); 0)",
            Context::Scrutinee => "(match ({H}) with _ when b -> 1 | _ -> 2)",
            Context::Receiver => "({H}).Length",
            Context::CaseField => "WA ({H})",
            Context::Annotated => "({H})",
        }
    }
}

/// One cell of the alphabet: a form, the context it is put in, and whether
/// a construct that ends the prefix comes before it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Cell {
    arm: Arm,
    context: Context,
    lost: bool,
}

/// Every cell, in a fixed order.
fn alphabet() -> Vec<Cell> {
    let mut cells = Vec::new();
    for lost in [false, true] {
        for context in Context::ALL {
            for arm in Arm::ALL {
                cells.push(Cell { arm, context, lost });
            }
        }
    }
    cells
}

/// One alphabet case: its text, and the range of its form within it.
struct AlphabetCase {
    cell: Cell,
    text: String,
    hole: (usize, usize),
}

/// The case for `cell`, its parts drawn from `seed`:
///
/// ```text
/// let aK (y: string) (n: int) (b: bool) p = (BEFORE, CONTEXT[FORM], p)
/// let aK (y: string) (n: int) (b: bool) p : int = (ignore (BEFORE); (FORM))
/// ```
///
/// `BEFORE` is a construct that ends the prefix ([`ArgGen::loss`]) when the
/// cell says so, and the witness `idf 3` otherwise.
fn alphabet_case(k: usize, cell: Cell, seed: u64) -> AlphabetCase {
    let mut rng = Rng(seed ^ (k as u64).wrapping_mul(0x9e37_79b9));
    let regime = regime_for(seed);
    let mut g = ArgGen {
        rng: &mut rng,
        regime: Regime {
            depth: 1,
            lambda_pct: 0,
            ill_pct: 0,
            ..regime
        },
        features: Features::default(),
        p_uses: 0,
    };
    let before = if cell.lost { g.loss() } else { "idf 3".into() };
    let form = cell.arm.production(&mut g, 1);
    let (head, prefix, suffix) = if cell.context == Context::Annotated {
        (
            format!("let a{k:03} (y: string) (n: int) (b: bool) p : int = "),
            format!("(ignore ({before}); "),
            ")".to_string(),
        )
    } else {
        (
            format!("let a{k:03} (y: string) (n: int) (b: bool) p = "),
            format!("({before}, "),
            ", p)".to_string(),
        )
    };
    let (pre, post) = cell
        .context
        .template()
        .split_once("{H}")
        .expect("a template has one hole");
    let start = head.len() + prefix.len() + pre.len();
    let text = format!("{head}{prefix}{pre}{form}{post}{suffix}");
    AlphabetCase {
        cell,
        text,
        hole: (start, start + form.len()),
    }
}

/// A case for each of `cells`, drawn for `round`, in files of
/// [`CASES_PER_FILE`].
fn alphabet_files(cells: &[Cell], round: usize) -> Vec<(String, Vec<(usize, AlphabetCase)>)> {
    let cases: Vec<AlphabetCase> = cells
        .iter()
        .enumerate()
        .map(|(k, &cell)| {
            let i = alphabet().iter().position(|&c| c == cell).expect("a cell");
            alphabet_case(k, cell, (round * 7919 + i) as u64)
        })
        .collect();
    let mut files = Vec::new();
    let mut cases = cases.into_iter().peekable();
    while cases.peek().is_some() {
        let mut src = HEADER.to_string();
        let mut placed = Vec::new();
        for case in cases.by_ref().take(CASES_PER_FILE) {
            let start = src.len();
            src.push_str(&case.text);
            src.push('\n');
            placed.push((start, case));
        }
        files.push((src, placed));
    }
    files
}

/// The expression whose range is exactly `at`, outermost first.
fn expr_at(root: &SyntaxNode, at: (usize, usize)) -> Option<Expr> {
    root.descendants().find_map(|n| {
        let r = n.text_range();
        let span = (u32::from(r.start()) as usize, u32::from(r.end()) as usize);
        if span == at { Expr::cast(n) } else { None }
    })
}

/// How many rounds a cell may take to draw a case FCS grades: a form is
/// drawn from a few spellings ([`Arm::production`]), not every one of which
/// FCS's dump grades in every context (`-("s")` is a declaration it does not
/// convert), so a cell left ungraded is drawn again.
const ALPHABET_ROUNDS: usize = 40;

/// The cells FCS's dump grades no case of, however the form is drawn, each
/// with why, for both prefix states. An operator's or a conversion's operand
/// of a type the operator has no implementation for (`-()`, `int (1, 1)`,
/// `-(Some 1)`) leaves the operator's static constraint unsolved, and FCS's
/// dump converts no declaration that holds one; nor one where such an
/// operator's result is equated with `unit` or passed to a method. The
/// sweep asserts each is still ungraded, so an entry that FCS starts to grade
/// fails until it is removed.
const FCS_UNGRADED: &[(Arm, Context, &str)] = &[
    (Arm::Unit, Context::Operand, "`-()`: no `~-` on unit"),
    (
        Arm::Tuple,
        Context::Operand,
        "`-(t, 1)`: no `~-` on a tuple",
    ),
    (Arm::ElselessIf, Context::Operand, "`-(if b then t)`: unit"),
    (Arm::While, Context::Operand, "`-(while …)`: unit"),
    (
        Arm::MethodCall,
        Context::Operand,
        "`-(y.Insert(…))`: string",
    ),
    (Arm::CaseApply, Context::Operand, "`-(Some t)`: an option"),
    (
        Arm::ModuleValue,
        Context::Operand,
        "`-(List.empty)`: a list",
    ),
    (
        Arm::Unit,
        Context::ConvertOperand,
        "`int ()`: no conversion from unit",
    ),
    (Arm::Tuple, Context::ConvertOperand, "`int (t, 1)`: a tuple"),
    (
        Arm::ElselessIf,
        Context::ConvertOperand,
        "`int (if b then t)`: unit",
    ),
    (Arm::While, Context::ConvertOperand, "`int (while …)`: unit"),
    (
        Arm::ModuleValue,
        Context::ConvertOperand,
        "`int List.empty`: a list",
    ),
    (
        Arm::Operator,
        Context::UnitPattern,
        "`let () = -(t)`: `~-` at unit",
    ),
    (
        Arm::Operator,
        Context::MethodArg,
        "`y.Insert(0, -(t))`: `~-` at an unknown type",
    ),
];

/// Whether FCS's dump grades no case of `cell` ([`FCS_UNGRADED`]).
fn fcs_ungraded(cell: Cell) -> bool {
    FCS_UNGRADED
        .iter()
        .any(|&(arm, context, _)| arm == cell.arm && context == cell.context)
}

/// Every modelled form, in every context that hands it an expected type,
/// with the prefix faithful and with it lost before the form, graded
/// against FCS: what inference commits anywhere in the file, FCS has, the
/// same. A cell counts as graded only where FCS's dump grades its form's
/// range, and is drawn again until it is. And each case's form is the arm
/// its cell names, so the alphabet is what the cells say it is.
#[test]
fn every_arm_in_every_context_is_certain_implies_exact() {
    let per_cell = env_usize_or("BORZOI_ALPHABET_PER_CELL", 1);
    let env = full_bcl_env();
    let mut graded: BTreeMap<Cell, usize> = BTreeMap::new();
    let mut misplaced = Vec::new();
    let mut unsound = Vec::new();
    let (mut certain, mut files) = (0, 0);
    let mut uncheckable: Vec<String> = Vec::new();
    let mut receivers = ReceiverClaim::default();
    let pending = |graded: &BTreeMap<Cell, usize>| -> Vec<Cell> {
        alphabet()
            .into_iter()
            .filter(|&c| !fcs_ungraded(c))
            .flat_map(|c| {
                let have = graded.get(&c).copied().unwrap_or(0);
                std::iter::repeat_n(c, per_cell.saturating_sub(have))
            })
            .collect()
    };
    let mut rounds = 0;
    while rounds < ALPHABET_ROUNDS && !pending(&graded).is_empty() {
        // The cells FCS grades nothing of are drawn too, so that one it starts
        // to grade is seen, in files of their own: FCS may fail to check a file
        // that holds one at all, which would take the other cells with it.
        let mut batch = alphabet_files(&pending(&graded), rounds);
        if rounds < 4 {
            let exempt: Vec<Cell> = alphabet()
                .into_iter()
                .filter(|&c| fcs_ungraded(c))
                .collect();
            batch.extend(alphabet_files(&exempt, rounds));
        }
        for (src, cases) in batch {
            files += 1;
            let parsed = parse(&src);
            assert!(parsed.errors.is_empty(), "{:?}\n{src}", parsed.errors);
            let root = parsed.root.clone();
            for (start, case) in &cases {
                let at = (start + case.hole.0, start + case.hole.1);
                let found = expr_at(&root, at).as_ref().and_then(arm_of);
                if found != Some(case.cell.arm) {
                    misplaced.push(format!("{:?} reads as {found:?}: {}", case.cell, case.text));
                }
            }
            let recovery = SyntaxRecovery::of(&parsed);
            let file = ImplFile::cast(parsed.root).expect("impl file");
            let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
            let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());
            let path = temp_fs_file("infer_alphabet", &src);
            let jsons = try_invoke_fcs_dump("types", &path)
                .and_then(|t| try_invoke_fcs_dump("binder-types", &path).map(|b| (t, b)))
                .and_then(|(t, b)| {
                    try_invoke_fcs_dump("check-diagnostics", &path).map(|d| (t, b, d))
                });
            let _ = std::fs::remove_file(&path);
            let dumps = match jsons {
                Ok((types_json, binders_json, diagnostics_json)) => {
                    GradedDumps::read(&types_json, &binders_json, &src, Some(&file))
                        .map(|dumps| (dumps, diagnostics_json))
                        .ok_or_else(|| "a declaration FCS's dump does not place".to_string())
                }
                Err(e) => Err(format!("{e:?}")),
            };
            // A file FCS cannot check grades none of its cells, which are drawn
            // again.
            let (dumps, diagnostics_json) = match dumps {
                Ok(dumps) => dumps,
                Err(why) => {
                    uncheckable.push(why);
                    continue;
                }
            };
            receivers.grade(&src, file.syntax(), &inferred, &diagnostics_json);
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
            for (table, ours, theirs) in [
                ("node", &ours_types, &dumps.types),
                ("binder", &ours_binders, &dumps.binders),
            ] {
                for (&at, ty) in ours {
                    if dumps.is_ungraded(at) {
                        continue;
                    }
                    certain += 1;
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
            for (start, case) in &cases {
                let at = (start + case.hole.0, start + case.hole.1);
                if !dumps.is_ungraded(at) {
                    *graded.entry(case.cell).or_default() += 1;
                }
            }
        }
        rounds += 1;
    }
    eprintln!(
        "alphabet sweep: {} cells graded in {rounds} rounds, {files} files, {certain} commits \
         graded, {} uncheckable: {uncheckable:?}",
        graded.len(),
        uncheckable.len()
    );
    assert!(
        misplaced.is_empty(),
        "{} forms are not the arm their cell names:\n{}",
        misplaced.len(),
        misplaced.join("\n")
    );
    assert!(
        unsound.is_empty(),
        "{} commits FCS does not have:\n{}",
        unsound.len(),
        unsound.join("\n")
    );
    assert!(
        uncheckable.len() * 10 <= files,
        "FCS could not check {} of {files} alphabet files: {uncheckable:?}",
        uncheckable.len()
    );
    let missing = pending(&graded);
    assert!(
        missing.is_empty(),
        "cells FCS graded no case of in {ALPHABET_ROUNDS} rounds: {missing:?}"
    );
    let now_graded: Vec<&Cell> = graded.keys().filter(|&&c| fcs_ungraded(c)).collect();
    assert!(
        now_graded.is_empty(),
        "FCS grades cells `FCS_UNGRADED` says it does not; remove them: {now_graded:?}"
    );
    assert!(certain > 0, "nothing committed, so nothing graded");
    receivers.assert_holds();
}

/// The FCS-graded claim on the receiver types inference records at each
/// access ([`borzoi_sema::InferredFile::receiver_type_at`]): FCS reports no
/// FS0072 (a lookup on an object of indeterminate type) at any access where
/// one is recorded. Completion offers the members of a recorded receiver, so
/// one FCS does not know at the access would offer members FCS rejects.
///
/// FCS's FS0072 spans the access from its receiver to the end of its member
/// path, whichever dot of the path the failing lookup is at. Inference
/// records a receiver at a dot only if it recorded one at every dot before it
/// in the path (it resolves each member on the receiver before it), so a
/// receiver recorded at the span's **last** dot means one recorded at the
/// failing lookup: that is what the claim checks, with no false alarm when
/// the failing lookup is an earlier dot whose receiver is not recorded.
///
/// It covers accesses whose member is written, as every one in the
/// alphabet's clean files is. Under a missing member FCS reports nothing
/// (`DiscardAfterMissingQualificationAfterDot`), so a recovered access's
/// receiver is held by [`deleting_a_member_keeps_the_receiver_and_isolates_the_declaration`]
/// and `infer_receiver_at`, not by FCS.
#[derive(Debug, Default)]
struct ReceiverClaim {
    /// How many receiver types the graded files record.
    recorded: usize,
    /// How many FS0072s the graded files hold, and how many span a dot.
    fs0072: usize,
    fs0072_with_a_dot: usize,
    violations: Vec<String>,
}

impl ReceiverClaim {
    fn grade(
        &mut self,
        src: &str,
        root: &SyntaxNode,
        inferred: &borzoi_sema::InferredFile,
        diagnostics_json: &str,
    ) {
        self.recorded += inferred.receiver_types().count();
        // FCS's lines are 1-based and its columns UTF-16 code units, which
        // are bytes in the generated (ASCII) source.
        assert!(src.is_ascii(), "the generated source is ASCII");
        let line_starts: Vec<usize> = std::iter::once(0)
            .chain(src.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let offset = |line: &serde_json::Value, col: &serde_json::Value| -> usize {
            let line = line.as_u64().expect("a line") as usize;
            line_starts[line - 1] + col.as_u64().expect("a column") as usize
        };
        let dots: Vec<TextRange> = root
            .descendants_with_tokens()
            .filter_map(|el| el.into_token())
            .filter(|t| t.kind() == SyntaxKind::DOT_TOK)
            .map(|t| t.text_range())
            .collect();
        let reply: serde_json::Value =
            serde_json::from_str(diagnostics_json).expect("check-diagnostics JSON");
        let diagnostics = reply["Diagnostics"]
            .as_array()
            .expect("check-diagnostics has a Diagnostics array");
        for d in diagnostics.iter().filter(|d| d["Code"] == 72) {
            self.fs0072 += 1;
            let (start, end) = (
                offset(&d["StartLine"], &d["StartCol"]),
                offset(&d["EndLine"], &d["EndCol"]),
            );
            let Some(&last) = dots
                .iter()
                .rev()
                .find(|r| usize::from(r.start()) >= start && usize::from(r.end()) <= end)
            else {
                continue;
            };
            self.fs0072_with_a_dot += 1;
            if let Some(ty) = inferred.receiver_type_at(last) {
                let line_start = src[..start].rfind('\n').map_or(0, |i| i + 1);
                let line_end = src[start..].find('\n').map_or(src.len(), |i| start + i);
                self.violations.push(format!(
                    "FS0072 at `{}`, where the receiver before its last dot is recorded as {}: {}",
                    &src[start..end],
                    ty.render(full_bcl_env()),
                    &src[line_start..line_end]
                ));
            }
        }
    }

    fn assert_holds(&self) {
        eprintln!(
            "receiver claim: {} receivers recorded, {} FS0072 ({} spanning a dot)",
            self.recorded, self.fs0072, self.fs0072_with_a_dot
        );
        assert!(
            self.violations.is_empty(),
            "{} receivers recorded at an access FCS reports FS0072 at:\n{}",
            self.violations.len(),
            self.violations.join("\n")
        );
        assert!(self.recorded > 0, "no receiver recorded, so none graded");
        assert!(
            self.fs0072_with_a_dot > 0,
            "no FS0072 at an access, so the claim was never tested"
        );
    }
}

/// [`Arm::ALL`] and [`Context::ALL`] hold each value once, at its index.
#[test]
fn the_alphabet_lists_are_closed() {
    for (i, arm) in Arm::ALL.iter().enumerate() {
        assert_eq!(arm.index(), i, "{arm:?}");
    }
    for (i, context) in Context::ALL.iter().enumerate() {
        assert_eq!(context.index(), i, "{context:?}");
    }
}

/// The `Expr` variants the alphabet's arms name ([`Arm::variant`]) are the
/// ones `Gen::infer_construct` has arms for, read from its source with
/// `syn`: an arm inference gains with no form in the alphabet fails here,
/// and so does a form for an arm inference does not have.
#[test]
fn the_alphabet_names_every_arm_inference_models() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/infer/expr.rs");
    let source = std::fs::read_to_string(&path).expect("read infer/expr.rs");
    let file = syn::parse_file(&source).expect("parse infer/expr.rs");
    struct Arms(std::collections::BTreeSet<String>, bool);
    impl<'ast> syn::visit::Visit<'ast> for Arms {
        fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) {
            if f.sig.ident == "infer_construct" {
                self.1 = true;
                syn::visit::visit_impl_item_fn(self, f);
                self.1 = false;
            }
        }
        fn visit_arm(&mut self, arm: &'ast syn::Arm) {
            if self.1 {
                let mut pats = vec![&arm.pat];
                while let Some(p) = pats.pop() {
                    match p {
                        syn::Pat::Or(or) => pats.extend(or.cases.iter()),
                        syn::Pat::TupleStruct(ts) => {
                            let segs: Vec<String> = ts
                                .path
                                .segments
                                .iter()
                                .map(|s| s.ident.to_string())
                                .collect();
                            if let [head, variant] = segs.as_slice()
                                && head == "Expr"
                            {
                                self.0.insert(variant.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            syn::visit::visit_arm(self, arm);
        }
    }
    let mut arms = Arms(Default::default(), false);
    syn::visit::Visit::visit_file(&mut arms, &file);
    assert!(
        !arms.0.is_empty(),
        "no `Expr` arm found in `infer_construct`"
    );
    let named: std::collections::BTreeSet<String> =
        Arm::ALL.iter().map(|a| a.variant().to_string()).collect();
    assert_eq!(
        arms.0, named,
        "the alphabet's arms and `Gen::infer_construct`'s differ: add a form for each arm \
         inference models ([`Arm`]), and none for one it does not"
    );
}

fn span(r: TextRange) -> (usize, usize) {
    (u32::from(r.start()) as usize, u32::from(r.end()) as usize)
}

/// What one file's inference publishes, keyed so two files that share a
/// prefix compare there: by range, a binder by its defining range, a module
/// value by its path.
#[derive(Debug, PartialEq, Eq)]
struct Published {
    types: BTreeMap<(usize, usize), String>,
    binders: BTreeMap<(usize, usize), String>,
    members: BTreeMap<(usize, usize), String>,
    receivers: BTreeMap<(usize, usize), String>,
    incompleteness: Vec<Vec<Incomplete>>,
    module_values: BTreeMap<Vec<String>, String>,
}

/// Infer `src`, which may not parse cleanly, as a one-file project (the
/// fold module values are published through), returning what it publishes
/// and its tree.
fn publish(src: &str) -> (Published, ImplFile, SyntaxRecovery) {
    let env = full_bcl_env();
    let parsed = parse(src);
    let recovery = SyntaxRecovery::of(&parsed);
    let tree = ImplFile::cast(parsed.root.clone()).expect("impl file");
    let file = SourceFile::Impl(tree.clone());
    let qnof = qualified_names(
        std::slice::from_ref(&file),
        &[std::path::PathBuf::from("/probe/Probe.fs")],
    )
    .pop()
    .expect("one name per file");
    let files = vec![ProjectFile::new(file, qnof, recovery.clone())];
    let resolved = resolve_project_files(&files, env);
    let project = infer_project(&files, &resolved, env);
    let inferred = project.file(0).expect("an implementation file");
    let resolved_file = resolved.file(0);
    let published = Published {
        types: inferred
            .types()
            .iter()
            .map(|(r, t)| (span(*r), t.render(env)))
            .collect(),
        binders: inferred
            .def_types()
            .iter()
            .map(|(d, t)| (span(resolved_file.def(*d).range), t.render(env)))
            .collect(),
        members: inferred
            .member_resolutions()
            .iter()
            .map(|(r, res)| (span(*r), format!("{res:?}")))
            .collect(),
        receivers: inferred
            .receiver_types()
            .map(|(dot, t)| (span(dot), t.render(env)))
            .collect(),
        incompleteness: inferred.incompleteness().to_vec(),
        module_values: resolved_file
            .exports()
            .iter()
            .map(|item| {
                let path = item
                    .qualified_path(env)
                    .unwrap_or_else(|| vec![item.name(env).to_string()]);
                let value = match project.item_type(item.id()) {
                    Ok(ty) => ty.render(env),
                    Err(gap) => format!("declined {gap:?}"),
                };
                (path, value)
            })
            .collect(),
    };
    (published, tree, recovery)
}

/// Every member access's dot in `tree` with a written member after it: the
/// dot's range and the end of the path it is in, so deleting from the dot's
/// end to the path's end leaves the access's member unwritten.
fn written_member_dots(tree: &ImplFile) -> Vec<(TextRange, usize)> {
    tree.syntax()
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::LONG_IDENT)
        .filter(|path| {
            path.parent().is_some_and(|access| {
                matches!(
                    access.kind(),
                    SyntaxKind::LONG_IDENT_EXPR | SyntaxKind::DOT_GET_EXPR
                )
            })
        })
        .flat_map(|path| {
            let end = u32::from(path.text_range().end()) as usize;
            path.children_with_tokens()
                .filter_map(|el| el.into_token())
                .filter(|t| t.kind() == SyntaxKind::DOT_TOK)
                .filter(|dot| {
                    dot.next_token()
                        .is_some_and(|t| t.kind() == SyntaxKind::IDENT_TOK)
                })
                .map(move |dot| (dot.text_range(), end))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The tally of [`deleting_a_member_keeps_the_receiver_and_isolates_the_declaration`].
#[derive(Debug, Default)]
struct DeletionTally {
    accesses: usize,
    /// Deletions whose damaged file's first recovery is not the dot (`s.(1)`
    /// is an indexer, `s..B` another recovery): not this property's input.
    not_first_recovery: usize,
    graded: usize,
    /// Graded deletions whose dot has a receiver type in the damaged file,
    /// and in the clean one.
    some: usize,
    clean_some: usize,
    violations: Vec<String>,
}

/// Member deletion, oracle-free and metamorphic, over the alphabet's files
/// (every modelled form in every context, so every access shape): delete
/// the member written after a dot of a clean generated file (`s.Length` becomes `s.`), so that
/// the dot is the damaged file's first recovery, and the damaged file must
///
/// - (a) record at that dot nothing, or what the clean file records there:
///   everything before the dot parsed alike, and the receiver's type at the
///   access depends on nothing after it;
/// - (b) publish exactly what the file truncated at the damaged
///   declaration's start publishes — expression, binder and receiver types
///   before it, member resolutions, the census and module values — plus
///   only receiver types inside the damaged declaration up to the dot, each
///   what the clean file records there: the damaged declaration is walked
///   for those receivers alone, and nothing after it is walked;
/// - (c) record a receiver at the dot often enough to be evidence.
///
/// FCS cannot grade these files: it reports nothing under a missing
/// qualification (`DiscardAfterMissingQualificationAfterDot`), so this and
/// `infer_receiver_at`'s cases are what hold the recovered declaration's
/// walk.
#[test]
fn deleting_a_member_keeps_the_receiver_and_isolates_the_declaration() {
    let rounds = env_usize_or("BORZOI_DELETION_ROUNDS", 2);
    let mut tally = DeletionTally::default();
    let sources = (0..rounds)
        .flat_map(|round| alphabet_files(&alphabet(), round))
        .map(|(src, _)| src);
    for src in sources {
        let (clean, tree, _) = publish(&src);
        for (dot, path_end) in written_member_dots(&tree) {
            tally.accesses += 1;
            let at = u32::from(dot.end()) as usize;
            let damaged_src = format!("{}{}", &src[..at], &src[path_end..]);
            let (damaged, damaged_tree, recovery) = publish(&damaged_src);
            let first = recovery.first_is_trailing_dot(damaged_tree.syntax());
            if first.as_ref().map(|t| t.text_range()) != Some(dot) {
                tally.not_first_recovery += 1;
                continue;
            }
            let decl_start = first
                .and_then(|t| t.parent())
                .and_then(|n| n.ancestors().find(|a| a.kind() == SyntaxKind::LET_DECL))
                .map(|d| u32::from(d.text_range().start()) as usize)
                .expect("a generated access sits in a `let`");
            tally.graded += 1;
            let mut fail = |what: String| {
                tally.violations.push(format!(
                    "{what}\n--- damaged at {} ---\n{damaged_src}",
                    span(dot).0
                ))
            };
            // (a)
            if clean.receivers.contains_key(&span(dot)) {
                tally.clean_some += 1;
            }
            let at_dot = damaged.receivers.get(&span(dot));
            if let Some(ty) = at_dot {
                tally.some += 1;
                if clean.receivers.get(&span(dot)) != Some(ty) {
                    fail(format!(
                        "(a) receiver {ty} at the dot, clean {:?}",
                        clean.receivers.get(&span(dot))
                    ));
                }
            }
            // (b)
            let (truncated, _, _) = publish(&src[..decl_start]);
            let (before, inside): (BTreeMap<_, _>, BTreeMap<_, _>) = damaged
                .receivers
                .iter()
                .map(|(k, v)| (*k, v.clone()))
                .partition(|((s, _), _)| *s < decl_start);
            for ((s, e), ty) in &inside {
                if *s > span(dot).0 || clean.receivers.get(&(*s, *e)) != Some(ty) {
                    fail(format!(
                        "(b) receiver {ty} at {s}..{e} in the damaged declaration, clean {:?}",
                        clean.receivers.get(&(*s, *e))
                    ));
                }
            }
            // The damaged declaration's binders, and every later one's, are
            // values the truncated file does not declare: each declines.
            let (module_values, later): (BTreeMap<_, _>, BTreeMap<_, _>) = damaged
                .module_values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .partition(|(path, _)| truncated.module_values.contains_key(path));
            for (path, value) in &later {
                if !value.starts_with("declined") {
                    fail(format!(
                        "(b) {path:?}, declared from the damaged declaration on, is {value}"
                    ));
                }
            }
            let damaged_rest = Published {
                receivers: before,
                module_values,
                ..damaged
            };
            if damaged_rest != truncated {
                fail(format!(
                    "(b) not the truncated file's:\n damaged   {damaged_rest:?}\n truncated {truncated:?}"
                ));
            }
        }
    }
    eprintln!(
        "member deletion: {} accesses, {} graded, {} not the first recovery, {} with a receiver \
         ({} in the clean file)",
        tally.accesses, tally.graded, tally.not_first_recovery, tally.some, tally.clean_some
    );
    assert!(
        tally.violations.is_empty(),
        "{} violations; the first:\n{}",
        tally.violations.len(),
        tally.violations.first().map_or("", String::as_str)
    );
    // (c): most of the alphabet's accesses are on a receiver FCS does not
    // know either (`p.Length`) or on a module (`List.empty`), so the floor
    // is on the count, and on recovering most of what the clean file has.
    assert!(
        tally.some >= 50 && tally.some * 10 >= tally.clean_some * 9,
        "too few deletions record a receiver to be evidence: {tally:?}"
    );
}
