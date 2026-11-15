//! Where FCS takes its order-dependent decisions, pinned on the shapes that
//! tell its checking order from the order of the text.
//!
//! FCS checks an application's argument with the expected type the function
//! gives it, so it unifies the application's result with what the context
//! expects before it checks the arguments (`Propagate`), and a lambda's
//! parameters with its expected domain before its body. An argument's
//! relation is decided at the argument's **entry**: whatever the argument's
//! sub-expressions then do, they do knowing the domain. Inference today
//! decides its argument checks at the binding's end, after the argument has
//! been walked, which is the **exit** order. The two agree on most programs;
//! these are the shapes where they do not, beside controls where they do.
//!
//! Each case is one `let` of the file [`SOURCE`], against FCS. For every FCS
//! expression node and binder in the case, and every type we commit there,
//! the manifest pins both sides, and it pins the case's census entry and FCS's
//! error codes, so a stage of #662 that moves a decision from exit to entry
//! shows up as a line diff here. Certain-implies-exact is asserted on top:
//! what we commit, FCS has, the same.
//!
//! Regenerate with
//! `BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-sema --test all infer_check_order_pins::`.

use std::collections::BTreeMap;

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile};
use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{PrecedingTypes, ProjectItems, SyntaxRecovery, infer_file, resolve_file};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::common::{GradedDumps, full_bcl_env, invoke_fcs_dump, temp_fs_file};

/// The shared header: the functions the cases apply. `singleton` is
/// `List.singleton`'s application rather than `[x]`, a list expression
/// inference does not model, which would leave it untyped and every case
/// applying it silent whatever the order.
const HEADER: &str = "module Pins\n\
                      let idf x = x\n\
                      let singleton x = List.singleton x\n\
                      let g (xs: obj list) = 0\n\
                      let gs (xs: string list) = 0\n\
                      let apply (k: string -> int) = k \"x\"\n\
                      let monos (t: string) = 2\n\
                      let gi (i: int) = 0\n\
                      let both (x: 'a) (y: 'a) = x\n\
                      let applyObj (k: obj -> int) = k\n\
                      let uu = fst ((7, \"u\"), 1)\n\
                      type T =\n    \
                          static member M (f: int -> int, s: string) = 1\n    \
                          static member M (f: string -> int, i: int) = 2\n\
                      type T2 =\n    \
                          static member N (s: string, f: int -> int) = 1\n    \
                          static member N (i: int, f: string -> int) = 2\n\
                      type T3 =\n    \
                          static member I (x: int, y: string) = \"\"\n";

/// Each case: its name, its `let`, and what entry and exit order each make of
/// it.
const CASES: &[(&str, &str, &str)] = &[
    (
        "singleton-into-obj-list",
        "let r1 (y: string) = g (singleton y)",
        "entry: `singleton y` is checked against `obj list`, so its element type is `obj` \
         before `y` is checked, and `y` coerces to it; FCS accepts. exit: walking \
         `singleton y` first fixes its element type to `string`, and `string list` is \
         not `obj list`",
    ),
    (
        "singleton-into-obj-list-beside-a-check",
        "let r9 (y: string) = (g (singleton y), idf 3)",
        "entry: as `r1`, and `idf 3`'s check is decided at its own argument. exit: the \
         failed check of `singleton y` against `obj list` is one FCS never made, and \
         it takes every check of the binding with it, `idf 3`'s included",
    ),
    (
        "singleton-into-string-list",
        "let r2 (y: string) = gs (singleton y)",
        "control: both orders give `string list`",
    ),
    (
        "id-wrapped-lambda-access",
        "let r3 = apply (idf (fun s -> s.Length))",
        "entry: `idf`'s result is unified with `string -> int` before its argument is \
         checked, so the lambda's `s` is a string at `s.Length`. exit: `s` is open at the \
         access (FS0072)",
    ),
    (
        "lambda-access",
        "let r4 = apply (fun s -> s.Length)",
        "entry: the lambda is checked against `string -> int`, so `s` is a string at the \
         access. exit: `s` is open there",
    ),
    (
        "id-wrapped-access",
        "let r5 (x: string) = (idf x).Length",
        "control: the receiver's type is known once `idf x` is checked, in either order",
    ),
    (
        "access-before-grounding",
        "let r6 x = (x.Length, monos x)",
        "control: in either order `x` is open at the access, which FCS rejects (FS0072) \
         before `monos x` grounds it",
    ),
    (
        "argument-check-before-a-complete-suffix",
        "let r7 () = (idf uu, None)",
        "the argument check of `idf uu` fires only in a complete binding today, as at the \
         binding's end; FCS decides it at the argument",
    ),
    (
        "argument-check-before-an-unmodelled-suffix",
        "let r8 () = (idf uu, Unchecked.defaultof<_>)",
        "as above, with a suffix inference does not model: today the binding is \
         incomplete and the check never fires; FCS's type for `idf uu` is the same",
    ),
    (
        "condition-before-a-check",
        "let r10 x = if x then (gi x, x) else (0, x)",
        "the condition fixes `x` to `bool` before `gi x` is checked, so FCS rejects the \
         check and keeps `x : bool`. A check decided at its argument must see the \
         condition's equality, which inference applies to the parameter's private slot \
         and not to the variable its uses read",
    ),
    (
        "declared-variable-fixed-by-a-check",
        "let r11<'a> (x: 'a) = gi x",
        "the check of `x` against `int` fixes the declared `'a`, which FCS rejects \
         (FS0670 or FS0064): nothing of the declaration may be published",
    ),
    (
        "declared-variable-beside-a-failed-check",
        "let r12<'a> (x: 'a) = (gi \"s\", gi (both x 1))",
        "a check failing between ground types, with no other check discharged \
         before it, then one that fixes the declared `'a` through `both`",
    ),
    (
        "branch-relates-before-its-arguments",
        "let c1 b p = ((if b then \"s\" else both p (gi p)), p)",
        "FCS relates the else-branch's result to `string` before checking its \
         arguments, so `both`'s `'a`, and `p` with it, are `string` when `gi p` is \
         checked, which FCS rejects. A relation dropped at the branch's exit leaves \
         `p` open there, and `gi p` would fix it to `int`",
    ),
    (
        "unique-overload-relates-before-its-arguments",
        "let c2 (s: string) p = (both p (s.Insert(gi p, \"z\")), p)",
        "`Insert` has one overload of two arguments, whose return FCS relates to the \
         call's expected type, `both`'s `'a`, before the arguments are checked \
         (`UnifyUniqueOverloading`): `p` is `string` when `gi p` is checked",
    ),
    (
        "annotation-relates-before-the-body",
        "let c4 p : string = both p (gi p)",
        "the return annotation is the body's expected type before the body is \
         checked, so `p` is `string` at `gi p`",
    ),
    (
        "parameter-loosened-once-known",
        "let c6 x y = (applyObj x, x y, y)",
        "once `applyObj x` fixes `x : obj -> int`, FCS loosens `x` at its next use, \
         so `x y` leaves `y` generic rather than fixing it to `obj`",
    ),
    (
        "unit-pattern-after-a-loss-over-an-applied-parameter",
        "let x1 p = ((p : int -> string), (let z = p 1 in (let () = z in z)), p)",
        "the annotation on an expression, which inference does not model, fixes `p : int -> \
         string`, so `p 1` and `z` are `string`, and FCS rejects the `()` pattern; inference \
         must not type `z` by the pattern it does not know is ill-typed (#774)",
    ),
    (
        "unit-pattern-after-a-loss-over-an-application",
        "let x2 p = ((p : string), (let z = idf p in (let () = z in z)), p)",
        "as `x1`: `idf p` and `z` are `string` by an annotation inference does not see, and \
         the `()` pattern is FCS's error (#774)",
    ),
    (
        "unit-pattern-after-a-loss-over-a-list",
        "let y3 (s: string) = ((s : string), (let z = [s] in (let () = z in z)), s)",
        "a list expression, which inference does not model, is `string list`; `z` is that, \
         and the `()` pattern is FCS's error (#774)",
    ),
    (
        "lambda-method-argument-checked-before-resolution",
        "let m1 (y: string) = (y.Insert(0, (fun () -> 1)), 0)",
        "FCS checks a lambda argument against its parameter before it resolves the call: \
         the lambda does not convert to `string`, and the call is `'a`, not `Insert`'s \
         `string` (an argument that is not a lambda, `y.Insert(0, 1)`, keeps `string`)",
    ),
    (
        "lambda-method-argument-control",
        "let m2 (y: string) = (y.Insert(0, idf (fun () -> 1)), 0)",
        "control: a lambda under an application is not a lambda argument, and FCS types \
         the call `string` by the single-candidate shortcut",
    ),
    (
        "overload-argument-checked-against-a-fresh-type",
        "let k1 (s: string) = s.StartsWith(idf \"h\")",
        "`StartsWith` has two overloads of one argument, so FCS checks `idf \"h\"` against a \
         fresh type, which it decides (`string`), and then resolves the call to \
         `StartsWith(string)` (#775). Checking the argument against a type inference does \
         not know leaves it open at the call, which is then declined",
    ),
    (
        "arity-unique-overload-fixes-its-argument",
        "let k2 (s: string) p = (s.Substring(p), p)",
        "`Substring` has one overload of one argument, whose parameter FCS relates to the \
         argument's type before it checks `p` (`UnifyUniqueOverloading`), so `p : int`",
    ),
    (
        "arity-unique-overload-relates-its-return-first",
        "let k3 (s: string) p = (both p (s.Substring(gi p)), p)",
        "the one overload's return is related to the call's expected type, `both`'s `'a`, \
         before the arguments are checked, so `p` is `string` when `gi p` is checked, which \
         FCS rejects",
    ),
    (
        "failed-return-relation-still-checks-the-arguments",
        "let k4 (s: string) p = (gi (s.Insert(p, \"z\")), p)",
        "the one candidate's return, `string`, does not relate to `gi`'s `int`; FCS reports \
         that after it has checked the arguments, so `p : int` all the same",
    ),
    (
        "lambda-argument-before-the-argument-that-picks-the-overload",
        "let k5 = T.M((fun x -> x.Length), 1)",
        "FCS checks a method's arguments in order: when the lambda is checked, both \
         overloads are still candidates and disagree about its parameter, so `x` is open \
         at `x.Length` (FS0072); the `1` after it is not seen first",
    ),
    (
        "lambda-argument-after-the-argument-that-picks-the-overload",
        "let k6 = T2.N(1, (fun x -> x.Length))",
        "control: the `1` checked first leaves one overload whose parameter is a function, \
         which gives the lambda's `x : string` before its body is checked",
    ),
    (
        "object-member-on-a-variable-receiver",
        "let k7 x = (x.ToString(), (x: int))",
        "FCS looks `ToString` up on a receiver whose type is a variable as on `obj`, and \
         accepts; inference declines an access whose receiver is a variable there, whatever \
         FCS makes of it",
    ),
    (
        "receiver-canonicalised-before-the-lookup",
        "let k8 x = ((x + 1).ToString(), x)",
        "FCS solves what it can of the receiver's type before a lookup on a variable \
         (`CanonicalizePartialInferenceProblem`), which defaults `+` to `int` here",
    ),
    (
        "overload-with-an-argument-open-at-the-call",
        "let k9 (s: string) p = (s.Contains(idf p), monos p)",
        "`Contains` has overloads of one argument, and `idf p` is open when FCS resolves \
         the call (FS0041); `monos p` fixes `p` only after it",
    ),
    (
        "shaped-argument-against-the-one-candidate",
        "let h1 p = (both p (T3.I(1, (fun x -> x))), p)",
        "FCS gives the lambda a function type before it relates `I`'s parameters, \
         relates them in order and stops at the first that fails (`string` against the \
         lambda's), so `I`'s return is never related to `both`'s `'a` and `p` stays \
         generic (FS0193). Relating the return first would fix `p : string`",
    ),
    (
        "shaped-argument-after-an-argument-the-candidate-fixes",
        "let h2 p q = (both p (T3.I(q, (fun x -> x))), p, q)",
        "as `h1`: `I`'s first parameter is related before the lambda's fails, so `q : int`, \
         and `p` stays generic",
    ),
    (
        "shaped-argument-against-a-bcl-candidate",
        "let h3 (s: string) p q = (both p (s.Insert(q, (fun x -> x))), p, q)",
        "`h2` on `String.Insert(int, string)`, the one candidate of two arguments: `q : int`, \
         `p` generic",
    ),
    (
        "no-candidate-of-the-call-shape",
        "let h5 (s: string) p = (s.Insert(both p (\"s\", \"t\")), p)",
        "`Insert` has no candidate of one argument; FCS checks a single argument to a method \
         of several plain parameters as a tuple of them (the \"single named item\" rule), so \
         `p : int * string`. Checking it against a fresh type would fix `p : string * string`",
    ),
    (
        "named-argument-related-to-the-candidate",
        "let h6 (s: string) p = (s.Insert(startIndex = both p \"s\", value = \"z\"), p)",
        "a named argument is related to its parameter like a positional one: `p : int`. \
         Inference does not read named arguments, so it commits nothing here",
    ),
    (
        "member-not-found-checks-no-argument",
        "let h7 (s: string) p = (s.Foo(gi p), p)",
        "FCS reports `Foo` (FS0039) before it checks the argument, so `gi p` fixes nothing \
         and `p` stays generic; checking the argument anyway would fix `p : int`",
    ),
    (
        "overload-resolution-that-binds-an-open-argument",
        "let k10 (s: string) p = (s.Equals(p), p)",
        "FCS resolves `Equals` with `p` open, preferring `Equals(string)`, and fixes `p` by \
         it: an overload decided on an open argument, which inference declines",
    ),
];

/// The file every case is a `let` of.
fn source() -> (String, Vec<(usize, usize)>) {
    let mut src = HEADER.to_string();
    let mut spans = Vec::new();
    for (_, text, _) in CASES {
        let start = src.len();
        src.push_str(text);
        spans.push((start, src.len()));
        src.push('\n');
    }
    (src, spans)
}

#[test]
fn checking_order_cases_are_pinned() {
    let (src, spans) = source();
    let parsed = parse(&src);
    assert!(parsed.errors.is_empty(), "{:?}\n{src}", parsed.errors);
    let recovery = SyntaxRecovery::of(&parsed);
    let file = ImplFile::cast(parsed.root).expect("impl file");
    let env = full_bcl_env();
    let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
    let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());

    let path = temp_fs_file("infer_check_order_pins", &src);
    let types_json = invoke_fcs_dump("types", &path);
    let binders_json = invoke_fcs_dump("binder-types", &path);
    let _ = std::fs::remove_file(&path);
    let dumps = GradedDumps::read(&types_json, &binders_json, &src, Some(&file))
        .expect("every declaration placed");

    // Header bindings come first in the census, one entry per counted binding.
    let census = inferred.incompleteness();
    let header_bindings = HEADER.matches("\nlet ").count();
    assert_eq!(
        census.len(),
        header_bindings + CASES.len(),
        "one census entry per binding: {census:?}"
    );
    let ours: BTreeMap<(usize, usize), String> = inferred
        .types()
        .iter()
        .map(|(r, t)| {
            (
                (u32::from(r.start()) as usize, u32::from(r.end()) as usize),
                t.render(env),
            )
        })
        .collect();
    let our_binders: BTreeMap<(usize, usize), String> = inferred
        .def_types()
        .iter()
        .map(|(d, t)| {
            let r = resolved.def(*d).range;
            (
                (u32::from(r.start()) as usize, u32::from(r.end()) as usize),
                t.render(env),
            )
        })
        .collect();

    let mut entries = Vec::new();
    let mut unsound = Vec::new();
    let line_of = |offset: usize| src[..offset].matches('\n').count() as u32 + 1;
    for (k, ((name, _, _), &(start, end))) in CASES.iter().zip(&spans).enumerate() {
        let mut codes: Vec<u32> = dumps
            .errors
            .iter()
            .filter(|e| e.line == line_of(start))
            .map(|e| e.code)
            .collect();
        codes.sort();
        codes.dedup();
        let fcs = if codes.is_empty() {
            "clean".to_string()
        } else {
            let codes: Vec<String> = codes.iter().map(|c| format!("FS{c:04}")).collect();
            format!("errors {}", codes.join(" "))
        };
        entries.push((format!("{name} fcs"), fcs));
        entries.push((
            format!("{name} census"),
            format!("{:?}", census[header_bindings + k]),
        ));
        for (kind, mine, theirs) in [
            ("node", &ours, &dumps.types),
            ("binder", &our_binders, &dumps.binders),
        ] {
            let mut at: Vec<(usize, usize)> = mine
                .keys()
                .chain(theirs.keys())
                .filter(|&&(s, e)| s >= start && e <= end)
                .copied()
                .collect();
            at.sort();
            at.dedup();
            for (s, e) in at {
                let (m, t) = (mine.get(&(s, e)), theirs.get(&(s, e)));
                if let Some(m) = m
                    && t != Some(m)
                {
                    unsound.push(format!("{name}: `{}` ours {m}, FCS {t:?}", &src[s..e]));
                }
                entries.push((
                    format!("{name} {kind} {}-{} `{}`", s - start, e - start, &src[s..e]),
                    format!(
                        "ours {} fcs {}",
                        m.map_or("-", String::as_str),
                        t.map_or("-", String::as_str)
                    ),
                ));
            }
        }
    }
    assert!(
        unsound.is_empty(),
        "committed types FCS does not have:\n{}",
        unsound.join("\n")
    );
    let manifest = Manifest::from_keyed(entries).unwrap_or_else(|e| panic!("manifest entry: {e}"));
    check_manifest(
        "infer_check_order_pins",
        &manifest,
        &regenerate("infer_check_order_pins::"),
    );
}
