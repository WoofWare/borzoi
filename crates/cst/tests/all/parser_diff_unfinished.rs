//! Unfinished constructs FCS's grammar recovers in place, graded against FCS:
//! the recovered construct keeps its node (with an empty name, a
//! `FromParseError` type or an `ArbitraryAfterError` expression where the
//! source stops), and the declarations after it keep theirs.
//!
//! Each grid here generates the ways a construct can stop short, in each
//! place it can sit. Where the construct simply stops, the recovered trees
//! must be `exact` (the whole normalised trees equal, recovery placeholders
//! included). Where a stray token follows, FCS's error recovery discards
//! tokens as FsYacc's error states dictate, which this parser does not
//! reproduce token by token, so those cells must only agree outside the
//! damage, except the cells listed beside the grid with the reason.

use crate::common::recovery::Relation;

/// What a grid cell's recovered trees must be.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Want {
    /// The whole normalised trees are equal.
    Exact,
    /// The undamaged declarations agree ([`Relation::OutsideDamage`] or
    /// better).
    Agree,
}

/// Grade every cell, collecting the ones that miss what they want and are not
/// listed in `diverging` (cells whose trees are allowed to diverge), then fail
/// listing them all. Whatever a cell wants, it must also keep every unit FCS
/// keeps, under the same key: an error span of ours covering a declaration
/// would otherwise let the relation hold while we lose it. A listed cell that
/// no longer diverges fails too, so the list cannot go stale.
fn assert_cells(cells: impl IntoIterator<Item = (String, Want)>, diverging: &[&str]) {
    let failures = check_cells(cells, diverging);
    assert!(
        failures.is_empty(),
        "{} cells fail:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// [`assert_cells`]'s failures, one line each.
fn check_cells(cells: impl IntoIterator<Item = (String, Want)>, diverging: &[&str]) -> Vec<String> {
    use crate::common::recovery::{fcs_units, grade, our_units};
    let mut failures = Vec::new();
    let mut unused: Vec<&str> = diverging.to_vec();
    for (src, want) in cells {
        let json = {
            let mut tmp = tempfile::NamedTempFile::with_suffix(".fs").expect("create tempfile");
            std::io::Write::write_all(&mut tmp, src.as_bytes()).expect("write source");
            crate::common::fcs_ast_batch(tmp.path())
        };
        let parse = borzoi_cst::parser::parse(&src);
        let verdict = grade(&parse, &Default::default(), &json, &src);
        if let Some(i) = unused.iter().position(|a| *a == src) {
            unused.remove(i);
            if verdict.relation != Relation::Divergent {
                failures.push(format!(
                    "{src:?} no longer diverges ({}); take it off the list",
                    verdict.token()
                ));
            }
            continue;
        }
        let met = match want {
            Want::Exact => verdict.relation == Relation::Exact,
            Want::Agree => verdict.relation != Relation::Divergent,
        };
        if !met {
            failures.push(format!(
                "{src:?} wants {want:?}: {}{}",
                verdict.token(),
                verdict
                    .first_divergence
                    .map(|d| format!(" ({d})"))
                    .unwrap_or_default()
            ));
        }
        let ours = our_units(&parse);
        for unit in fcs_units(&json, &src) {
            if !ours.iter().any(|o| o.key == unit.key) {
                failures.push(format!("{src:?} loses {}", unit.key));
            }
        }
    }
    if !unused.is_empty() {
        failures.push(format!(
            "listed cells the grid no longer generates: {unused:?}"
        ));
    }
    failures
}

/// An abstract slot that stops after its keywords, its access or `inline`
/// modifiers, its name or its `:` (FCS's `classDefnMember` `recover` arms):
/// FCS keeps an `AbstractSlot`, named `""` when the name is missing, with a
/// `FromParseError` type, and discards the rest of the line. Each slot sits
/// alone in a type body, before another member, before another slot, and as a
/// type's whole representation inside a nested module (whose `let` after it
/// stays in that module), and is followed by nothing or by a stray token.
#[test]
fn recover_unfinished_abstract_slot_grid() {
    const FLAGS: &[&str] = &[
        "abstract",
        "abstract member",
        "static abstract",
        "static abstract member",
        "[<A>] abstract",
    ];
    const RESTS: &[(&str, Want)] = &[
        ("", Want::Exact),
        (" private", Want::Exact),
        (" inline", Want::Exact),
        (" private inline", Want::Exact),
        (" P", Want::Exact),
        (" P:", Want::Exact),
        (" P<'a>", Want::Exact),
        (" P<'a>:", Want::Exact),
        (" P: 1", Want::Exact),
        (" 1", Want::Agree),
        (" P 1", Want::Agree),
        // FCS reads `(x)` as an operator name that fails to parse (its
        // `opName` error arm), which names the slot differently.
        (" (x)", Want::Agree),
        // Junk that opens a context of its own, closed or not: the rest of the
        // member is discarded up to the member's own end, never the type's.
        (" P = match x with", Want::Agree),
        (" P = (x", Want::Agree),
        (" P = begin", Want::Agree),
        (" P with", Want::Agree),
        (" P: int with get", Want::Agree),
        (" { new I with member _.M = 1 }", Want::Agree),
    ];
    let mut cells = Vec::new();
    let mut diverging = Vec::new();
    let mut survivors = Vec::new();
    for flags in FLAGS {
        for &(rest, want) in RESTS {
            let slot = format!("{flags}{rest}");
            let alone = format!("module M\ntype T =\n    {slot}\n");
            let nested =
                format!("module M\nmodule A =\n    type T = {slot}\n    let x = 1\nlet z = 2\n");
            // A stray token after the slot on the type body's last line: FCS's
            // error recovery then discards the body's closing block end too,
            // which loses the module at the end of the file (`alone`) or,
            // inside a nested module, makes the `let` after the type one of its
            // members and the top-level `let z` one of `A`'s (`nested`).
            if matches!(rest, " 1" | " P 1" | " P = (x") {
                diverging.push(alone.clone());
            }
            if matches!(rest, " 1" | " P 1" | " P = match x with") {
                diverging.push(nested.clone());
            }
            cells.push((alone, want));
            cells.push((
                format!("module M\ntype T =\n    {slot}\n    member _.Q = 1\nlet x = 1\n"),
                want,
            ));
            cells.push((
                format!("module M\ntype T =\n    {slot}\n    abstract Q: int\nlet x = 1\n"),
                want,
            ));
            // The next member on the slot's own line: the discarded rest of
            // the slot ends where a member keyword begins, so the member
            // survives, unless the rest opened a bracket or a `with` (the lex
            // filter's contexts around the member are then the rest's, and the
            // member is discarded with it, as on `main`). (`abstract` before
            // `member` is one `abstract member` keyword run, whose junk `_.Q =
            // 1` is on the body's last line.)
            let flat = !rest.contains(['=', '(', '{']) && !rest.contains("with");
            for next in [
                "member _.Q = 1",
                "abstract Q: int",
                "val q: int",
                "new() = {}",
            ] {
                let src = format!("module M\ntype T() =\n    {slot} {next}\nlet x = 1\n");
                if matches!(*flags, "abstract" | "static abstract" | "[<A>] abstract")
                    && rest.is_empty()
                    && next.starts_with("member")
                {
                    diverging.push(src.clone());
                } else if flat {
                    survivors.push(src.clone());
                }
                cells.push((src, Want::Agree));
            }
            cells.push((nested, want));
        }
    }
    let diverging: Vec<&str> = diverging.iter().map(String::as_str).collect();
    assert_members_survive(&survivors);
    assert_cells(cells, &diverging);
}

/// Every source's first type definition keeps as many members as FCS's does:
/// members sit inside their type's unit, so [`assert_cells`]'s unit-level
/// loss check cannot see one discarded with an unfinished member's rest. A
/// tree the normaliser does not model counts no members.
fn assert_members_survive(sources: &[String]) {
    let lost = check_members_survive(sources);
    assert!(
        lost.is_empty(),
        "{} types lose members FCS keeps:\n{}",
        lost.len(),
        lost.join("\n")
    );
}

/// [`assert_members_survive`]'s failures, one line each.
fn check_members_survive(sources: &[String]) -> Vec<String> {
    use crate::common::normalised_ast::{
        NormalisedDecl, NormalisedRoot, NormalisedTypeRepr, normalise_fcs_dump, normalise_parse,
    };
    fn members(root: &NormalisedRoot) -> usize {
        let NormalisedRoot::Impl(file) = root else {
            return 0;
        };
        file.modules
            .iter()
            .flat_map(|m| &m.decls)
            .find_map(|d| match d {
                NormalisedDecl::Types(defs) => defs.first(),
                _ => None,
            })
            .map_or(0, |def| {
                let repr = match &def.repr {
                    NormalisedTypeRepr::ObjectModel { members, .. } => members.len(),
                    _ => 0,
                };
                repr + def.members.len()
            })
    }
    let mut lost = Vec::new();
    for src in sources {
        let json = {
            let mut tmp = tempfile::NamedTempFile::with_suffix(".fs").expect("create tempfile");
            std::io::Write::write_all(&mut tmp, src.as_bytes()).expect("write source");
            crate::common::fcs_ast_batch(tmp.path())
        };
        let parse = borzoi_cst::parser::parse(src);
        let count = |f: &dyn Fn() -> NormalisedRoot| {
            crate::common::catch_unwind_silent(std::panic::AssertUnwindSafe(f))
                .map_or(0, |root| members(&root))
        };
        let (fcs, ours) = (
            count(&|| normalise_fcs_dump(&json)),
            count(&|| normalise_parse(&parse)),
        );
        if ours < fcs {
            lost.push(format!("{src:?}: FCS keeps {fcs} members, ours {ours}"));
        }
    }
    lost
}

/// A `when` with no guard (FCS's `parenPattern WHEN` recovery arms): before
/// the clause's `->`, the clause has no guard and keeps its result; before
/// the next clause's `|`, or at the end of the list, it has no guard and an
/// `ArbitraryAfterError` result, and the clauses after it are kept. Each sits
/// first or after another clause, in a `match`, a `function` and a
/// `try … with`, at the top of a file and as a `let`'s body, with a `let`
/// after it.
///
/// FCS's arm for a guardless `when` before `->` ends the clause list, so it
/// discards the clauses after such a clause. This parser keeps them, so those
/// cells only agree outside the damage.
#[test]
fn recover_missing_when_guard_grid() {
    const CLAUSES: &[(&str, Want)] = &[
        ("| a when -> ()", Want::Exact),
        ("| a when", Want::Exact),
        ("| a when\n| b -> ()", Want::Exact),
        ("| a when | b -> ()", Want::Exact),
        ("| a when\n| [<A>] b -> ()", Want::Exact),
        ("| a when\n|", Want::Exact),
        ("| a when\n| b when\n| c -> ()", Want::Exact),
        ("| a when -> ()\n| b -> ()", Want::Agree),
    ];
    const HOSTS: &[&str] = &["match x with", "function", "try () with"];
    let mut cells = Vec::new();
    for &(clauses, want) in CLAUSES {
        for before in ["", "| z -> ()\n"] {
            for host in HOSTS {
                let body = format!("{host}\n{before}{clauses}");
                cells.push((format!("module M\n{body}\n"), want));
                let indented = body.replace('\n', "\n    ");
                cells.push((
                    format!("module M\nlet f x =\n    {indented}\nlet y = 1\n"),
                    want,
                ));
            }
        }
    }
    assert_cells(cells, &[]);
}

/// An infix operator with no right operand (FCS's `declExpr OP %prec
/// prec_recover` arms, and `ends_coming_soon_or_recover` for `@`/`^`): FCS
/// builds `mkSynInfix op lhs (ArbitraryAfterError)` and goes on, so the
/// operator ends its expression and the declarations after it are kept. Each
/// operator ends a `let`'s right-hand side at the top of a file and in a
/// nested module, ends a parenthesised expression, an argument and a named
/// argument, sits before `then`, and before another operator on the next line.
///
/// An operator that is also a prefix operator (`+`, `-`, `%`, `&&`) before a
/// closer or a `,` sends FCS into its parenthesis's error arm instead, which
/// discards the parenthesis's whole contents (`Paren(ArbitraryAfterError)`);
/// this parser keeps `a op ?` there, so those cells only agree outside the
/// damage.
#[test]
fn recover_unfinished_infix_operator_grid() {
    const OPS: &[&str] = &[
        "&&", "||", "|>", "&&&", "|||", "=", "==", "<>", "<", ">", "$", "%", "::", "+", "-", "*",
        "/", "**", "@", "^", "^^^", "<<<",
    ];
    const PREFIX_TOO: &[&str] = &["+", "-", "%", "&&"];
    let mut cells = Vec::new();
    for op in OPS {
        let in_paren = if PREFIX_TOO.contains(op) {
            Want::Agree
        } else {
            Want::Exact
        };
        cells.extend([
            (
                format!("module M\nlet x = a {op}\nlet y = 1\n"),
                Want::Exact,
            ),
            (
                format!("module M\nmodule A =\n    let x = a {op}\n    let y = 1\nlet z = 2\n"),
                Want::Exact,
            ),
            (format!("module M\nlet x = (a {op})\nlet y = 1\n"), in_paren),
            (
                format!("module M\nlet x = f (a {op}) b\nlet y = 1\n"),
                in_paren,
            ),
            (
                format!("module M\nlet x = M(a {op}, b = 2)\nlet y = 1\n"),
                in_paren,
            ),
            (
                format!("module M\nlet x = if a {op} then 1 else 2\nlet y = 1\n"),
                Want::Exact,
            ),
            (
                format!("module M\nlet x =\n    a {op}\n    |> f\nlet y = 1\n"),
                Want::Exact,
            ),
            (
                format!("module M\ndo\n    if true {op}\n\n    ()\n"),
                Want::Exact,
            ),
        ]);
    }
    // FCS starts the `let`'s range inside the module header here (at the
    // header's end, before its line break), so the units' keys differ.
    assert_cells(
        cells,
        &["module M\nlet x =\n    a &&&\n    |> f\nlet y = 1\n"],
    );
}

/// A pattern path that stops after a dot (FCS's `pathOp: ident DOT %prec
/// prec_recover` and `underscoreLongIdentPat: UNDERSCORE DOT %prec
/// prec_recover`): FCS keeps the path up to the dot, and a one-segment path
/// whose head is not uppercase reads as the variable it names (`e.` and `_.`
/// are `Named`). Each path heads a `match` clause with and without its `->`,
/// sits inside parentheses and as a constructor's argument, and heads a
/// member (with and without its `= body`).
#[test]
fn recover_trailing_dot_pattern_grid() {
    const PATHS: &[&str] = &["e.", "E.", "_.", "a.b.", "A.B.", "``e``."];
    let mut cells = Vec::new();
    for path in PATHS {
        for clause in [
            format!("| {path} -> ()"),
            format!("| {path}"),
            format!("| ({path}) -> ()"),
            format!("| Some {path} -> ()"),
            format!("| {path}\n    | b -> ()"),
        ] {
            cells.push((
                format!("module M\nlet f x =\n    match x with\n    {clause}\nlet y = 1\n"),
                Want::Exact,
            ));
        }
    }
    for head in ["this.", "_.", "x.P.", "``this``."] {
        for keyword in ["member", "override", "default"] {
            for body in ["", " = 2"] {
                cells.push((
                    format!(
                        "module M\ntype T() =\n    {keyword} {head}{body}\n    member _.Q = 1\nlet y = 1\n"
                    ),
                    Want::Exact,
                ));
            }
        }
    }
    assert_cells(cells, &[]);
}

/// An `if` with no `then` (FCS's `IF declExpr %prec prec_recover`, beside the
/// `IF declExpr ifExprCases` arms for a `then` with no branch): FCS keeps an
/// `IfThenElse` whose `then` branch is `ArbitraryAfterError`, and goes on.
/// Each stops after its condition, after an unfinished condition, after
/// `then` and after `else`, as a `let`'s right-hand side at the top of a file
/// and in a nested module, inside parentheses, in a `do` block and at the top
/// of a file before a later expression, and as a statement before another.
#[test]
fn recover_unfinished_if_grid() {
    const IFS: &[&str] = &["if a", "if a b", "if a *", "if a then", "if a then 1 else"];
    let mut cells = Vec::new();
    for unfinished in IFS {
        for src in [
            format!("module M\nlet x = {unfinished}\nlet y = 1\n"),
            format!("module M\nmodule A =\n    let x = {unfinished}\n    let y = 1\nlet z = 2\n"),
            format!("module M\nlet x = ({unfinished})\nlet y = 1\n"),
            format!("module M\nlet x = f ({unfinished}) b\nlet y = 1\n"),
            format!("module M\ndo\n    {unfinished}\n\n    ()\n"),
            format!("module M\n{unfinished}\n\n()\n"),
            format!("module M\nlet f () =\n    {unfinished}\n    b\nlet y = 1\n"),
        ] {
            cells.push((src, Want::Exact));
        }
    }
    assert_cells(cells, &[]);
}

/// An operator straight after an opener (`( >`) has no left operand: the
/// bracket's own recovery owns it, as FCS's `LPAREN recover` arm discards it
/// with the bracket's contents, so the climber does not take it as an
/// operator missing its right operand (`E_IncompleteParens01.fsx`'s shape).
#[test]
fn recover_operator_after_an_opener_is_the_brackets() {
    let verdict = crate::common::recovery::assert_recovered_trees_agree(
        "[<Measure>] type m\nlet velocity12 = 1.0<m / ( >  // Err\n",
        2,
    );
    assert_eq!(verdict.relation, Relation::Exact, "{}", verdict.token());
}

/// A binding whose right-hand side recovers in place, followed by a raw `let`
/// on a line indented past the binding's own: FCS reports the `let` (the
/// binding's terminator is missing), but its error recovery shifts it as the
/// start of a module-level declaration rather than discarding it, so the
/// declaration survives. Each right-hand side is clean, ends in an unfinished
/// operator, or holds one, at the top of a file and in a nested module.
#[test]
fn recover_raw_let_after_a_binding_grid() {
    const RHS: &[&str] = &[
        "a",
        "a *",
        "a +",
        "if a then 1 else 2",
        "if a * then 1 else 2",
        "f (a *) b",
        "match a with | b when -> ()",
    ];
    let mut cells = Vec::new();
    for rhs in RHS {
        for indent in ["  ", "    ", "        "] {
            cells.push((
                format!("module M\nlet x = {rhs}\n{indent}let y = 1\nlet z = 2\n"),
                Want::Agree,
            ));
            cells.push((
                format!(
                    "module M\nmodule A =\n    let x = {rhs}\n    {indent}let y = 1\n    let z = 2\n"
                ),
                Want::Agree,
            ));
        }
    }
    assert_cells(cells, &[]);
}

/// What follows an unfinished construct, systematically: each construct of
/// the grids above (an unfinished slot in a type body, a binding whose
/// right-hand side recovers in place) followed by each declaration or member
/// a buffer may hold next, on the same line or on the next at several
/// indents. Whatever the recovery, every unit FCS keeps should survive under
/// its key, and the type keep as many members as FCS's. Most of the cells
/// that do not are older than these ports: each is pinned in
/// `tests/manifests/unfinished_followers.txt`, and must be one where `main`'s
/// parser fails too (`unfinished_followers.base.txt`).
///
/// Each construct has a finished twin (`abstract P: int` for a slot, `a * b`
/// for `a *`, `when c ->` for a guardless `when`). A cell worse than `main`
/// is accepted when its twin, with the same follower, fails too: `main` then
/// kept the declaration only because its recovery failed earlier, and the
/// faithful recovery parses on into a gap the finished shape has on `main`
/// as well (a `type` after a member at the member column, a declaration
/// after a stray `then`, …), not one the ports opened.
#[test]
fn recover_followers_of_unfinished_constructs_grid() {
    use borzoi_oracle_harness::manifest::{Manifest, UPDATE_ENV};
    // Each construct beside its finished twin.
    const SLOTS: &[(&str, &str)] = &[
        ("abstract", "abstract P: int"),
        ("abstract P", "abstract P: int"),
        ("abstract P:", "abstract P: int"),
        ("abstract (x)", "abstract P: int"),
        ("abstract P 1", "abstract P: int"),
        ("abstract)", "abstract P: int"),
    ];
    const MEMBER_FOLLOWERS: &[&str] = &[
        "member _.Q = 1",
        "let q = 1",
        "do ()",
        "with get",
        "with get member _.Q = 1",
        "interface I",
        "inherit B()",
        "static member S = 1",
        "override _.O = 1",
        "[<A>] member _.Q = 1",
        "[<A(if true then 1 else 2)>] member _.Q = 1",
    ];
    const DECL_FOLLOWERS: &[&str] = &[
        "type S = int",
        "[<A>] type S = int",
        "module N = let n = 1",
        "open System",
        "exception E",
        "[<A>] let q = 1",
        "let y = 1",
        "do ()",
        "#nowarn \"1\"",
    ];
    const RHS: &[(&str, &str)] = &[
        ("a", "a"),
        ("a *", "a * b"),
        ("if a * then 1 else 2", "if a * b then 1 else 2"),
        (
            "match a with | b when -> ()",
            "match a with | b when c -> ()",
        ),
        ("f (a *) b", "f (a * b) b"),
        ("(a *)", "(a * b)"),
        ("(a *) in", "(a * b) in"),
        ("a * in", "a * b in"),
        ("if a * then", "if a * b then"),
        (
            "function | _ when | y -> ()",
            "function | _ when c -> () | y -> ()",
        ),
        (
            "function | _ when | y -> () then",
            "function | _ when c -> () | y -> () then",
        ),
        ("match a with | b. -> ()", "match a with | b.c -> ()"),
    ];
    // Each cell beside its twin.
    let mut cells: Vec<(String, String)> = Vec::new();
    let mut members = Vec::new();
    for &(slot, twin) in SLOTS {
        let host = |s: &str, sep: &str, next: &str| {
            format!("module M\ntype T() =\n    {s}{sep}{next}\nlet x = 1\n")
        };
        for next in MEMBER_FOLLOWERS {
            for sep in [" ", "\n    ", "\n        "] {
                members.push(host(slot, sep, next));
                cells.push((host(slot, sep, next), host(twin, sep, next)));
            }
        }
        for next in DECL_FOLLOWERS {
            for sep in [" ", "\n", "\n ", "\n    ", "\n        "] {
                cells.push((host(slot, sep, next), host(twin, sep, next)));
            }
            // The slot as the type's whole representation, on its line.
            let repr = |s: &str| format!("module M\ntype T() = {s}\n{next}\nlet x = 1\n");
            cells.push((repr(slot), repr(twin)));
        }
    }
    for &(rhs, twin) in RHS {
        for next in DECL_FOLLOWERS {
            for sep in [" ", "\n", "\n ", "\n  ", "\n    "] {
                let top = |r: &str| format!("module M\nlet x = {r}{sep}{next}\nlet z = 2\n");
                cells.push((top(rhs), top(twin)));
                let nested_sep = sep.replace('\n', "\n    ");
                let nested = |r: &str| {
                    format!(
                        "module M\nmodule A =\n    let x = {r}{nested_sep}{next}\n    let z = 2\nlet w = 3\n"
                    )
                };
                cells.push((nested(rhs), nested(twin)));
            }
        }
    }
    let keys = follower_keys(
        check_members_survive(&members)
            .into_iter()
            .chain(check_cells(
                cells.iter().map(|(src, _)| (src.clone(), Want::Agree)),
                &[],
            )),
    );
    let actual = Manifest::from_entries(keys.clone()).expect("one line per key");
    crate::common::corpus_manifest::check_manifest(
        "unfinished_followers",
        &actual,
        &format!(
            "{UPDATE_ENV}=1 nix develop -c cargo test -p borzoi-cst --test all parser_diff_unfinished::recover_followers"
        ),
    );
    // The twins of the failing cells, and which of them fail too.
    let failing: std::collections::BTreeSet<&str> = keys
        .iter()
        .filter_map(|k| k.rsplit_once(" | ").map(|(cell, _)| cell))
        .collect();
    let twin_of: std::collections::BTreeMap<String, &str> = cells
        .iter()
        .map(|(src, twin)| (format!("{src:?}"), twin.as_str()))
        .collect();
    let twins: Vec<String> = failing
        .iter()
        .filter_map(|cell| twin_of.get(*cell).map(|t| t.to_string()))
        .collect();
    let twin_members: Vec<String> = twins
        .iter()
        .filter(|t| {
            members
                .iter()
                .any(|m| twin_of.get(&format!("{m:?}")) == Some(&t.as_str()))
        })
        .cloned()
        .collect();
    let failing_twins: std::collections::BTreeSet<String> = follower_keys(
        check_members_survive(&twin_members)
            .into_iter()
            .chain(check_cells(
                twins.iter().map(|t| (t.clone(), Want::Agree)),
                &[],
            )),
    )
    .into_iter()
    .filter_map(|k| k.rsplit_once(" | ").map(|(cell, _)| cell.to_string()))
    .collect();
    let accepted: Vec<&str> = keys
        .iter()
        .filter(|k| {
            k.rsplit_once(" | ")
                .and_then(|(cell, _)| twin_of.get(cell))
                .is_some_and(|twin| failing_twins.contains(&format!("{twin:?}")))
        })
        .map(String::as_str)
        .collect();
    crate::common::corpus_manifest::check_no_worse_than_base(
        "unfinished_followers",
        &keys,
        &accepted,
    );
}

/// Each grid failure as a key spelled the same under any parser: the cell's
/// source, then what fails.
fn follower_keys(failures: impl IntoIterator<Item = String>) -> Vec<String> {
    failures
        .into_iter()
        .map(|f| {
            // `{src:?}: FCS keeps …` (a member), `{src:?} wants …` or
            // `{src:?} loses <unit>`.
            if let Some(end) = f.find("\": FCS keeps") {
                return format!("{} | loses a member", &f[..=end]);
            }
            let end = f.find("\" ").expect("a failure starts with its source");
            let what = &f[end + 2..];
            let what = if what.starts_with("loses ") {
                what.to_string()
            } else {
                "divergent".to_string()
            };
            format!("{} | {what}", &f[..=end])
        })
        .collect()
}
