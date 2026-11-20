//! Differential tests: our `Condition` evaluator (`condition.rs`) vs the real
//! MSBuild evaluator via `tools/msbuild-condition-oracle`.
//!
//! The asserted property is *certain-implies-exact*, not equality: our
//! [`Outcome::Unsupported`](borzoi_msbuild::test_support::Outcome) is a
//! deliberate fail-safe superset (it fires both when MSBuild would *reject* a
//! condition as illegal and when the condition is legal-but-uses-grammar we
//! don't model). So the sound contract is one-directional — whenever we commit
//! to a boolean, MSBuild must agree with that exact boolean; when we say
//! `Unsupported` we make no claim. See
//! [`check_certain_implies_exact`](common::check_certain_implies_exact).
//!
//! Inputs here are deterministic (fixed-seed SplitMix64 plus a hand-written
//! corner list) so a failure reproduces exactly and the oracle batch stays
//! stable run-to-run; the *random-input* exploration lives in
//! `condition_properties.rs`.
//!
//! Each case spawns nothing per-eval — the oracle evaluates conditions
//! in-process against the SDK's MSBuild — but the harness does `dotnet build`
//! the oracle once, so this runs under `nix develop` like the sibling
//! `dotnet`-driven differentials.

mod common;

use borzoi_msbuild::test_support::{PropertyMap, Throws, judge};
use common::case_axis::{CaseContext, gen_case_comparison, respell_case, respell_keys};
use common::{
    Oracle, SplitMix64, Verdict, breaks_inside_quote, check_certain_implies_exact, gen_bool_expr,
    gen_props, respell_whitespace, soak_parameters,
};

fn props(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
        .collect()
}

/// (condition, props, the outcome branch we must land in)
type Case = (&'static str, Vec<(String, String)>, Verdict);

/// Corners of [`Verdict::Illegal`]: what MSBuild rejects, where it does not
/// look, and the near misses it evaluates, which we must not call illegal.
fn illegal_corners() -> Vec<Case> {
    vec![
        // Syntax: MSBuild parses the whole condition before evaluating any of
        // it, so a syntax error rejects it whatever the values, and behind a
        // deciding `And`/`Or` operand too.
        ("tr ue", props(&[]), Verdict::Illegal),
        ("$(A) == ", props(&[("A", "a")]), Verdict::Illegal),
        ("(true", props(&[]), Verdict::Illegal),
        ("true)", props(&[]), Verdict::Illegal),
        ("()", props(&[]), Verdict::Illegal),
        ("'abc", props(&[]), Verdict::Illegal),
        ("'a' == 'b", props(&[]), Verdict::Illegal),
        ("false And (tr ue)", props(&[]), Verdict::Illegal),
        ("true Or 'abc", props(&[]), Verdict::Illegal),
        ("false And $(A) ==", props(&[]), Verdict::Illegal),
        ("false and 'x' = 'x'", props(&[]), Verdict::Illegal),
        ("true == true == true", props(&[]), Verdict::Illegal),
        ("a.b == 'a.b'", props(&[]), Verdict::Illegal),
        ("trueand true", props(&[]), Verdict::Illegal),
        ("'a' == 'b' 'c'", props(&[]), Verdict::Illegal),
        ("!", props(&[]), Verdict::Illegal),
        ("true And", props(&[]), Verdict::Illegal),
        ("Or true", props(&[]), Verdict::Illegal),
        ("true;", props(&[]), Verdict::Illegal),
        ("false and #", props(&[]), Verdict::Illegal),
        ("false and $", props(&[]), Verdict::Illegal),
        ("false and $x", props(&[]), Verdict::Illegal),
        ("false and @", props(&[]), Verdict::Illegal),
        ("false and %", props(&[]), Verdict::Illegal),
        ("true,true", props(&[]), Verdict::Illegal),
        ("false and $(A.B('x)", props(&[]), Verdict::Illegal),
        // The scan stops at the parse error, before the item list, whose
        // legality would depend on where the condition sits.
        ("tr ue @(I)", props(&[]), Verdict::Illegal),
        // An item list or metadata reference is legal on an item and illegal
        // on a property, so no claim either way.
        ("'@(I)' == ''", props(&[]), Verdict::Unsupported),
        ("false and '%(I.M)' == ''", props(&[]), Verdict::Unsupported),
        // Syntax MSBuild accepts and we do not model: evaluated, so no claim.
        ("(true) == true", props(&[]), Verdict::Unsupported),
        ("!true == false", props(&[]), Verdict::Unsupported),
        ("false and foo('x')", props(&[]), Verdict::Unsupported),
        ("false and f(,)", props(&[]), Verdict::Unsupported),
        // A relational comparison on an operand that is neither a number nor
        // a version (MSB4086), on the evaluated path only.
        ("1 < abc", props(&[]), Verdict::Illegal),
        ("abc < 1", props(&[]), Verdict::Illegal),
        ("1.2.3 < abc", props(&[]), Verdict::Illegal),
        ("true And 1 < abc", props(&[]), Verdict::Illegal),
        ("false And 1 < abc", props(&[]), Verdict::False),
        ("true Or 1 < abc", props(&[]), Verdict::True),
        ("'' < 1", props(&[]), Verdict::Illegal),
        ("$(Foo) < 1", props(&[]), Verdict::Illegal),
        ("$(Foo) < 1", props(&[("Foo", "Debug")]), Verdict::Illegal),
        ("' 1' < 2", props(&[]), Verdict::Illegal),
        ("'1.-1' < 2", props(&[]), Verdict::Illegal),
        ("'1.2.3.4.5' < 2", props(&[]), Verdict::Illegal),
        ("'1.2.2147483648' > 2", props(&[]), Verdict::Illegal),
        ("1 < 0xg", props(&[]), Verdict::Illegal),
        // …and the near misses .NET does read: `-0` is a version component,
        // whitespace pads one, and a dotted operand that is no version may
        // still be a number.
        ("'1.-0' < 2", props(&[]), Verdict::True),
        ("' 1 . 2 ' < 2", props(&[]), Verdict::True),
        ("'1.' < 2", props(&[]), Verdict::True),
        // `double.TryParse` takes the NaN symbol in any case (a number every
        // comparison is false on), a trailing NUL, and an infinity it then
        // refuses as a number: none of these is ours to call.
        ("nan < 1", props(&[]), Verdict::Unsupported),
        ("'NaN' > 1", props(&[]), Verdict::Unsupported),
        ("'1%00' < 2", props(&[]), Verdict::Unsupported),
        ("Infinity < 1", props(&[]), Verdict::Unsupported),
        // A scalar standing as a boolean outside the vocabulary, on the
        // evaluated path only.
        ("foo", props(&[]), Verdict::Illegal),
        ("1", props(&[]), Verdict::Illegal),
        ("'1'", props(&[]), Verdict::Illegal),
        ("$(Foo)", props(&[]), Verdict::Illegal),
        ("true and foo", props(&[]), Verdict::Illegal),
        ("'x'and'y'", props(&[]), Verdict::Illegal),
        ("foo or true", props(&[]), Verdict::Illegal),
        ("!foo or true", props(&[]), Verdict::Illegal),
        ("(foo) or true", props(&[]), Verdict::Illegal),
        ("false and foo", props(&[]), Verdict::False),
        ("true or foo", props(&[]), Verdict::True),
        ("false and $(Foo)", props(&[]), Verdict::False),
        ("'%74rue'", props(&[]), Verdict::True),
        // `OrdinalIgnoreCase` folds `ſ` to `S`, which ASCII folding does not.
        ("'yeſ'", props(&[]), Verdict::Unsupported),
        // `HasTrailingSlash` given more than one item.
        ("HasTrailingSlash('a;b')", props(&[]), Verdict::Illegal),
        ("HasTrailingSlash('a/; b/')", props(&[]), Verdict::Illegal),
        ("HasTrailingSlash('a/;%20')", props(&[]), Verdict::Illegal),
        ("HasTrailingSlash(';;a/;;')", props(&[]), Verdict::True),
        (
            "false and HasTrailingSlash('a;b')",
            props(&[]),
            Verdict::False,
        ),
        // A version function given no version (MSB4184), and a property
        // function out of range, on the evaluated path only (#1009).
        (
            "$([MSBuild]::VersionGreaterThan('abc', '1.0'))",
            props(&[]),
            Verdict::Illegal,
        ),
        (
            "$([MSBuild]::VersionLessThan('$(V)', '1.0'))",
            props(&[("V", "1.2.3.4.5")]),
            Verdict::Illegal,
        ),
        (
            "false and $([MSBuild]::VersionGreaterThan('abc', '1.0'))",
            props(&[]),
            Verdict::False,
        ),
        // .NET reads a trailing NUL as no part of the version: no claim.
        (
            "$([MSBuild]::VersionGreaterThan('1.2.3%00', '1.0'))",
            props(&[]),
            Verdict::Unsupported,
        ),
        (
            "'$(P.Split(`;`)[3])' == ''",
            props(&[("P", "a;b")]),
            Verdict::Illegal,
        ),
        ("'$(P[5])' == ''", props(&[("P", "abc")]), Verdict::Illegal),
        (
            "'a' == 'b' and '$(P[5])' == ''",
            props(&[("P", "abc")]),
            Verdict::False,
        ),
        (
            "'$([MSBuild]::VersionLessThan(\"x\", \"18.9\"))' == ''",
            props(&[]),
            Verdict::Illegal,
        ),
        ("'$(P[2])' == 'c'", props(&[("P", "abc")]), Verdict::True),
    ]
}

/// Hand-picked corners: each pins both our evaluator's committed outcome and
/// (via the internal oracle round-trip) MSBuild's agreement. Every shape the
/// `condition.rs` unit tests pin one-by-one gets a guaranteed seat here,
/// regardless of what the generator happens to produce.
#[test]
fn hand_picked_corners() {
    let mut oracle = Oracle::spawn();

    let cases: &[Case] = &[
        // Bare booleans and negation.
        ("true", props(&[]), Verdict::True),
        ("false", props(&[]), Verdict::False),
        ("!false", props(&[]), Verdict::True),
        ("!true", props(&[]), Verdict::False),
        // String equality (ordinal, case-insensitive).
        ("'a' == 'a'", props(&[]), Verdict::True),
        ("'a' == 'b'", props(&[]), Verdict::False),
        ("'ABC' == 'abc'", props(&[]), Verdict::True),
        ("'a' != 'b'", props(&[]), Verdict::True),
        // MSBuild boolean vocabulary: 'on'/'yes'/'true' are all mutually equal.
        ("'on' == 'yes'", props(&[]), Verdict::True),
        ("'off' == 'no'", props(&[]), Verdict::True),
        ("'on' == 'off'", props(&[]), Verdict::False),
        // Numeric (double) comparison.
        ("1 < 2", props(&[]), Verdict::True),
        ("2 <= 2", props(&[]), Verdict::True),
        ("3 > 10", props(&[]), Verdict::False),
        ("3.14 > 3", props(&[]), Verdict::True),
        // Hex is a 32-bit reinterpretation.
        ("0x10 == 16", props(&[]), Verdict::True),
        // Version vs number: major-only, version wins ties.
        ("6.0.0.0 > 6", props(&[]), Verdict::True),
        ("1.2.3 < 1.3", props(&[]), Verdict::True),
        // Exponent form is NOT a double, so this is string comparison.
        ("'1e2' == '100'", props(&[]), Verdict::False),
        // Property substitution.
        (
            "'$(Configuration)' == 'Debug'",
            props(&[("Configuration", "Debug")]),
            Verdict::True,
        ),
        (
            "'$(Configuration)' != 'Debug'",
            props(&[("Configuration", "Release")]),
            Verdict::True,
        ),
        // The is-it-set idiom: undefined property expands to empty.
        ("'$(Undefined)' == ''", props(&[]), Verdict::True),
        ("'$(Undefined)' != ''", props(&[]), Verdict::False),
        // The oracle's internal result lives in the item namespace, so a
        // condition referencing its name (or `R`, its former property name) as
        // a *property* sees nothing — these must match our empty expansion.
        ("'$(_ConditionResult)' == ''", props(&[]), Verdict::True),
        ("'$(R)' == ''", props(&[]), Verdict::True),
        ("'$(R)' == 'x'", props(&[("R", "x")]), Verdict::True),
        // Logical combinators and precedence.
        ("1 == 1 And 2 == 2", props(&[]), Verdict::True),
        ("1 == 1 And 2 == 3", props(&[]), Verdict::False),
        ("1 == 2 Or 3 == 3", props(&[]), Verdict::True),
        (
            "(1 == 2 Or 3 == 3) And 'a' == 'a'",
            props(&[]),
            Verdict::True,
        ),
        // Standalone scalar coerced to bool: a bare property reference,
        // bare boolean-vocabulary word, and quoted literal.
        ("$(Flag)", props(&[("Flag", "true")]), Verdict::True),
        ("$(Flag)", props(&[("Flag", "false")]), Verdict::False),
        // Whitespace around a *simple* reference is MSBuild-illegal (only the
        // function forms tolerate it), so we must not commit to Flag's value.
        ("$( Flag )", props(&[("Flag", "true")]), Verdict::Illegal),
        ("!$(Flag)", props(&[("Flag", "false")]), Verdict::True),
        ("on", props(&[]), Verdict::True),
        ("no", props(&[]), Verdict::False),
        ("!off", props(&[]), Verdict::True),
        ("'true'", props(&[]), Verdict::True),
        // Bare words are unquoted simple-string operands.
        ("Release == 'Release'", props(&[]), Verdict::True),
        ("on == 'x'", props(&[]), Verdict::False),
        ("$(P) == 'y'", props(&[("P", "y")]), Verdict::True),
        // true/false as unquoted comparison operands (SDK container shape).
        ("$(B) == false", props(&[("B", "False")]), Verdict::True),
        ("false == $(B)", props(&[("B", "False")]), Verdict::True),
        // String instance methods: capital True/False, ordinal & case-sensitive.
        (
            "$(V.Contains('{'))",
            props(&[("V", "8.0.0")]),
            Verdict::False,
        ),
        (
            "$(V.StartsWith('8'))",
            props(&[("V", "8.0.0")]),
            Verdict::True,
        ),
        // MSBuild's scanner counts a reference's parentheses without regard
        // to quotes, so a quoted `(` leaves this one unclosed.
        (
            "$(V.Contains('@('))",
            props(&[("V", "x")]),
            Verdict::Illegal,
        ),
        (
            "HasTrailingSlash('@(x)/')",
            props(&[]),
            Verdict::Unsupported,
        ),
        ("'%(Identity)' == 'x'", props(&[]), Verdict::Unsupported),
        // A `%XX` escape (percent + two hex digits) is *unescaped* by MSBuild at
        // the operand leaf — `'%74rue' == 'true'` is true — and we model that
        // now (stage E2 of `docs/completed/msbuild-escaped-value-plan.md`). These used to
        // degrade the whole condition: fail-safe, but it cost every gate an
        // escape appeared in. The oracle round-trip is what makes committing them
        // safe rather than brave.
        ("'%74rue' == 'true'", props(&[]), Verdict::True),
        ("'a%20b' == 'a b'", props(&[]), Verdict::True),
        // …including an escape reaching the operand through a property value.
        ("'$(P0)' == 'a b'", props(&[("P0", "a%20b")]), Verdict::True),
        // A `%` **outside** quotes is not an escape: MSBuild's scanner rejects it
        // outright (MSB4090). Committing a boolean for a condition MSBuild
        // refuses to evaluate would be a wrong gate.
        ("%74rue", props(&[]), Verdict::Illegal),
        ("1%2E0 > 0.5", props(&[]), Verdict::Illegal),
        // A bare `%` with any other suffix stays literal: committed as
        // ordinary string comparison, and MSBuild must agree.
        ("'100%' == '100%'", props(&[]), Verdict::True),
        ("'a%zz' == 'true'", props(&[]), Verdict::False),
        // But a marker delivered only via `$()` substitution is never
        // re-lexed by MSBuild, so it stays an ordinary substring and we must
        // still commit to the exact boolean MSBuild computes.
        (
            "$(V.Contains('$(N)'))",
            props(&[("V", "a@(b"), ("N", "@(")]),
            Verdict::True,
        ),
        (
            "$(V.Contains('-')) == false",
            props(&[("V", "8.0.100")]),
            Verdict::True,
        ),
        // HasTrailingSlash built-in (pure; trims the expanded argument).
        ("HasTrailingSlash('bin/Debug/')", props(&[]), Verdict::True),
        ("HasTrailingSlash('bin/Debug')", props(&[]), Verdict::False),
        (
            "!HasTrailingSlash('$(OutDir)')",
            props(&[("OutDir", "obj")]),
            Verdict::True,
        ),
        // The **unquoted** argument spelling. MSBuild accepts a bare property
        // expression where the built-ins take a string, and it is the only
        // spelling available to an argument that itself contains quotes — the
        // `Exists($([MSBuild]::GetPathOfFileAbove('x', '$(D)')))` idiom, which
        // has no way to nest a delimiter inside a literal.
        (
            "HasTrailingSlash($(OutDir))",
            props(&[("OutDir", "obj/")]),
            Verdict::True,
        ),
        (
            "HasTrailingSlash($(OutDir))",
            props(&[("OutDir", "obj")]),
            Verdict::False,
        ),
        // A nested function call as the unquoted argument — the shape that
        // cannot be written quoted at all.
        (
            "HasTrailingSlash($([MSBuild]::EnsureTrailingSlash('obj')))",
            props(&[]),
            Verdict::True,
        ),
        // Bare text *around* the reference is MSB4092 ("An unexpected token"),
        // so this must not read as `$(D)` plus a suffix.
        (
            "HasTrailingSlash($(OutDir)sub/)",
            props(&[("OutDir", "obj/")]),
            Verdict::Illegal,
        ),
        // The F# SDK's FSharpCoreMaximumMajorVersion gate, end-to-end.
        (
            "'$(S)' == 'true' and '$(V)' != '' and !$(V.Contains('{'))",
            props(&[("S", "true"), ("V", "8.0.0")]),
            Verdict::True,
        ),
        // MSBuild's scanner rejects an unquoted reference holding whitespace
        // but nothing outside an XML name, before `and` could short-circuit
        // past it; with punctuation beside the whitespace it is legal.
        ("false and $(A B)", props(&[]), Verdict::Illegal),
        ("false and $(A\nB)", props(&[]), Verdict::Illegal),
        (
            "false and $([System.String]::Concat($(A B)))",
            props(&[]),
            Verdict::Illegal,
        ),
        (
            "$(A.Contains('x y'))",
            props(&[("A", "x y")]),
            Verdict::True,
        ),
        // A line break or tab inside a quoted string is itself, not a space.
        ("'x\ny' == 'x y'", props(&[]), Verdict::False),
        ("'x\ty' == 'x\ty'", props(&[]), Verdict::True),
        // It scans parentheses without regard to quotes, so a quoted `)`
        // ends the reference early.
        ("false and $(A.Contains(')'))", props(&[]), Verdict::Illegal),
    ];
    let cases: Vec<Case> = cases.iter().cloned().chain(illegal_corners()).collect();

    let mut trues = 0;
    let mut falses = 0;
    let mut illegals = 0;
    for (condition, props, expected) in &cases {
        let got = check_certain_implies_exact(&mut oracle, condition, props);
        assert_eq!(
            got, *expected,
            "our evaluator landed in {got:?}, expected {expected:?} for {condition:?}"
        );
        match got {
            Verdict::True => trues += 1,
            Verdict::False => falses += 1,
            Verdict::Illegal => illegals += 1,
            Verdict::Unsupported => {}
        }
    }
    // Sanity: the corner list actually exercises every committed branch
    // (guards against the whole evaluator regressing to one constant, or the
    // rejection silently ceasing to fire).
    assert!(
        trues >= 5 && falses >= 5 && illegals >= 30,
        "corners: {trues} true, {falses} false, {illegals} illegal"
    );
}

/// Fixed-seed generative sweep. Every generated `(condition, props)` case must
/// satisfy certain-implies-exact; a coverage floor guards against the corpus
/// silently degrading to all-`Unsupported` (which would make the whole sweep
/// vacuously pass while testing nothing).
#[test]
fn fixed_seed_sweep() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x5eed_c0ffee);

    const CASES: usize = 4000;
    let mut trues = 0usize;
    let mut falses = 0usize;
    let mut illegal = 0usize;
    let mut unsupported = 0usize;

    for _ in 0..CASES {
        let depth = rng.below(3) as u32; // 0..=2 nesting levels.
        let condition = gen_bool_expr(&mut rng, depth);
        let props = gen_props(&mut rng);
        match check_certain_implies_exact(&mut oracle, &condition, &props) {
            Verdict::True => trues += 1,
            Verdict::False => falses += 1,
            Verdict::Illegal => illegal += 1,
            Verdict::Unsupported => unsupported += 1,
        }
    }

    eprintln!(
        "sweep: {trues} true, {falses} false, {illegal} illegal, {unsupported} unsupported / {CASES}"
    );
    // Anti-vacuity floors: a healthy corpus commits to *both* booleans a few
    // hundred times each (observed ~340/~390 at this seed). Far below the
    // split, so a generator tweak won't trip them, but a collapse of the
    // evaluator to a constant — or to all-`Unsupported` — would. The
    // relational operands include non-numbers, so it rejects too (471).
    assert!(trues >= 250, "too few committed-true cases: {trues}");
    assert!(falses >= 250, "too few committed-false cases: {falses}");
    assert!(illegal >= 230, "too few committed-illegal cases: {illegal}");
}

/// What one run of [`illegal_leaning_sweep`] saw: our verdicts on each of
/// [`gen_illegal_leaning`]'s families.
#[derive(Default, Debug)]
struct IllegalCensus {
    /// Our verdicts by family: `[true, false, illegal, unsupported]`.
    mutated: [usize; 4],
    ill_typed: [usize; 4],
    token_soup: [usize; 4],
}

impl IllegalCensus {
    fn illegal(&self) -> usize {
        self.mutated[2] + self.ill_typed[2] + self.token_soup[2]
    }
}

/// One of [`gen_bool_expr`]'s conditions with a character deleted or one
/// inserted, once or twice: mostly syntax errors, some still legal.
fn gen_mutated(rng: &mut SplitMix64) -> String {
    const INSERTS: &[char] = &[
        '\'', '(', ')', '=', '!', '<', '>', ' ', '\t', '$', '@', '%', ',', ';', '#', 'a', '1', '.',
        '-',
    ];
    let depth = rng.below(3) as u32;
    let mut chars: Vec<char> = gen_bool_expr(rng, depth).chars().collect();
    for _ in 0..1 + rng.below(2) {
        let at = rng.below(chars.len() + 1);
        if rng.below(2) == 0 && at < chars.len() {
            chars.remove(at);
        } else {
            chars.insert(at, *rng.pick(INSERTS));
        }
    }
    chars.into_iter().collect()
}

/// An operand MSBuild may not be able to type where it stands — a scalar as a
/// boolean, a relational comparison on a non-number, `HasTrailingSlash` over
/// a list — beside an ordinary condition on either side of `And`/`Or`, so
/// that the condition's verdict turns on whether MSBuild evaluates it. Some
/// are the near misses .NET does read.
fn gen_ill_typed(rng: &mut SplitMix64) -> String {
    const ATOMS: &[&str] = &[
        "foo",
        "1",
        "'1'",
        "''",
        "$(P0)",
        "$(Foo)",
        "$(Undefined)",
        "1 < abc",
        "abc >= 1",
        "'x' < $(P0)",
        "$(Foo) > 2",
        "$(Version) <= 6",
        "' 1' < 2",
        "'1.-1' < 2",
        "'1.-0' < 2",
        "'1.2.2147483648' > 1",
        "nan < 1",
        "HasTrailingSlash('a;b')",
        "HasTrailingSlash('$(P0);x/')",
        "HasTrailingSlash('$(P0)')",
    ];
    let depth = rng.below(2) as u32;
    let expr = gen_bool_expr(rng, depth);
    let atom = *rng.pick(ATOMS);
    let atom = if rng.below(4) == 0 {
        format!("!({atom})")
    } else {
        atom.to_string()
    };
    let connective = *rng.pick(&["And", "Or", "and", "or"]);
    if rng.below(2) == 0 {
        format!("{expr} {connective} {atom}")
    } else {
        format!("{atom} {connective} {expr}")
    }
}

/// One to six of MSBuild's condition tokens, near-tokens and stray
/// characters, in any order: mostly syntax errors, including the item-list
/// and metadata openers whose legality depends on the context.
fn gen_token_soup(rng: &mut SplitMix64) -> String {
    const TOKENS: &[&str] = &[
        "(",
        ")",
        "!",
        "==",
        "!=",
        "<",
        ">=",
        "=",
        "and",
        "Or",
        "'a'",
        "'",
        "1",
        "1.2",
        "0x1",
        "$(P0)",
        "$(P 0)",
        "$(",
        "$",
        "%",
        "@",
        ",",
        "f(",
        "foo",
        "true",
        "false",
        ";",
        "@(I)",
        "'%(M)'",
        "HasTrailingSlash",
        "'b/'",
    ];
    let mut soup = String::new();
    for _ in 0..1 + rng.below(6) {
        soup.push_str(rng.pick(TOKENS));
        soup.push_str(rng.pick(&["", " ", " ", "  "]));
    }
    soup
}

fn illegal_leaning_sweep(seed: u64, cases: usize) -> IllegalCensus {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut census = IllegalCensus::default();
    for _ in 0..cases {
        let family = rng.below(3);
        let condition = match family {
            0 => gen_mutated(&mut rng),
            1 => gen_ill_typed(&mut rng),
            _ => gen_token_soup(&mut rng),
        };
        let props = gen_props(&mut rng);
        let verdict = match check_certain_implies_exact(&mut oracle, &condition, &props) {
            Verdict::True => 0,
            Verdict::False => 1,
            Verdict::Illegal => 2,
            Verdict::Unsupported => 3,
        };
        let tally = match family {
            0 => &mut census.mutated,
            1 => &mut census.ill_typed,
            _ => &mut census.token_soup,
        };
        tally[verdict] += 1;
    }
    census
}

/// The illegal side of the contract, at a fixed seed: conditions leaning
/// towards MSBuild's errors, every `Illegal` verdict graded against MSBuild's
/// rejection, every boolean against its value.
#[test]
fn illegal_leaning_sweep_fixed_seed() {
    let census = illegal_leaning_sweep(0x111e_6a15_5eed, 4000);
    eprintln!("illegal-leaning sweep: {census:?}");
    // Liveness of each family's rejections (observed at this seed: 909
    // mutated, 601 ill-typed, 1150 token soup), so the classification cannot
    // silently stop firing, and of the ill-typed family's booleans (302),
    // which are where MSBuild's laziness is graded.
    assert!(census.mutated[2] >= 450, "{census:?}");
    assert!(census.ill_typed[2] >= 280, "{census:?}");
    assert!(census.token_soup[2] >= 550, "{census:?}");
    assert!(
        census.ill_typed[0] + census.ill_typed[1] >= 160,
        "{census:?}"
    );
}

/// Fresh-seed twin of [`illegal_leaning_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching condition.rs"]
fn illegal_leaning_sweep_soak() {
    let (seed, cases) = soak_parameters("condition illegal-leaning", 50_000);
    let census = illegal_leaning_sweep(seed, cases);
    eprintln!(
        "illegal-leaning soak: {census:?} ({} illegal)",
        census.illegal()
    );
}

/// What one run of [`case_variant_sweep`] saw.
#[derive(Default, Debug)]
struct CaseCensus {
    /// Cases whose original spelling we committed, and whose respelling differs
    /// from it — the points at which the metamorphic check has teeth.
    committed_respelt: usize,
    /// Committed `==` cases whose two operands are distinct but equal under
    /// ASCII case folding, and which came out `True` — so the case-insensitive
    /// branch of `==` is what decided them. Without these, a case-sensitive
    /// `==` agrees with MSBuild on every input.
    committed_case_equal_true: usize,
    /// Cases carrying a non-ASCII letter, by our verdict.
    non_ascii_committed: usize,
    non_ascii_declined: usize,
}

/// One case of the case-variant axis, three properties at once:
///
/// 1. **Certain-implies-exact** on the original *and* on the respelling, against
///    the oracle.
/// 2. **The respelling preserves MSBuild's answer.** This is the respeller's
///    claim, not ours, and it is checked rather than assumed — a scanning
///    mistake in [`respell_case`] would otherwise quietly widen what property 3
///    believes is equivalent.
/// 3. **The respelling preserves our verdict** — committed or declined, and
///    which boolean. This is the only one of the three that sees a
///    case-sensitivity bug which *declines*: `AND` falling through to a bare
///    word, a case-sensitive function-name match. Certain-implies-exact passes
///    every such bug, because a decline makes no claim.
fn respelled_condition_is_invariant(
    oracle: &mut Oracle,
    rng: &mut SplitMix64,
    condition: &str,
    props: &[(String, String)],
    census: &mut CaseCensus,
) {
    let respelt = respell_case(rng, condition, CaseContext::Condition);
    let respelt_props = respell_keys(rng, props);

    let ours = check_certain_implies_exact(oracle, condition, props);
    let ours_respelt = check_certain_implies_exact(oracle, &respelt, &respelt_props);

    let theirs = oracle.eval(condition, props);
    let theirs_respelt = oracle.eval(&respelt, &respelt_props);
    assert_eq!(
        theirs, theirs_respelt,
        "the respeller changed MSBuild's answer, so it flipped a letter MSBuild reads \
         case-sensitively:\n  original {condition:?} with {props:?}\n  respelt  \
         {respelt:?} with {respelt_props:?}"
    );

    // Exempt: a condition carrying a non-ASCII letter. String equality over
    // non-ASCII operands that are not byte-equal is a documented decline
    // (`compare_equality_values` carries no Unicode case table), so flipping an
    // ASCII letter beside a non-ASCII one legitimately turns a byte-equal,
    // committed pair into a declined one — and back.
    if condition.is_ascii() {
        assert_eq!(
            ours, ours_respelt,
            "a case respelling moved our verdict where MSBuild's stood still ({theirs:?}):\n  \
             original {condition:?} with {props:?} -> {ours:?}\n  respelt  {respelt:?} with \
             {respelt_props:?} -> {ours_respelt:?}"
        );
    }

    if ours != Verdict::Unsupported && respelt != condition {
        census.committed_respelt += 1;
    }
    if ours == Verdict::True && case_equal_operands(condition, "==") {
        census.committed_case_equal_true += 1;
    }
    if !condition.is_ascii() {
        match ours {
            Verdict::Unsupported => census.non_ascii_declined += 1,
            _ => census.non_ascii_committed += 1,
        }
    }
}

/// Whether `condition` is a single `lhs OP rhs` whose operands are distinct but
/// equal under ASCII case folding.
fn case_equal_operands(condition: &str, op: &str) -> bool {
    let Some((lhs, rhs)) = condition.split_once(&format!(" {op} ")) else {
        return false;
    };
    lhs != rhs && lhs.eq_ignore_ascii_case(rhs)
}

fn case_variant_sweep(oracle: &mut Oracle, rng: &mut SplitMix64, cases: usize) -> CaseCensus {
    let mut census = CaseCensus::default();
    for _ in 0..cases {
        let props = gen_props(rng);
        let condition = if rng.below(2) == 0 {
            let depth = rng.below(3) as u32;
            gen_bool_expr(rng, depth)
        } else {
            gen_case_comparison(rng, &props)
        };
        respelled_condition_is_invariant(oracle, rng, &condition, &props, &mut census);
    }
    census
}

/// The case-variant axis, at a fixed seed.
///
/// The generators above spell every keyword, function, property name and
/// operand one way, so a case-*sensitive* `==` — or property lookup, or keyword
/// match — agreed with MSBuild on every input they built. This sweep respells
/// them, and makes operands that differ only in case meet, including the
/// non-ASCII letters where `OrdinalIgnoreCase` is not what a Unicode-aware
/// reimplementation would guess.
#[test]
fn case_variant_sweep_fixed_seed() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0xca5e_f01d_5eed);
    let census = case_variant_sweep(&mut oracle, &mut rng, 3000);
    eprintln!("case-variant sweep: {census:?}");
    // Non-vacuity of the metamorphic check, and of the case-equal operand pairs
    // it exists for. Each is a floor on a *generated shape* reaching a commit,
    // not on the evaluator's commit rate overall. Observed at this seed: 1654
    // respelt, 104 case-equal `==` true, 620 non-ASCII.
    assert!(
        census.committed_respelt >= 500,
        "only {} committed cases were respelt — the metamorphic check is testing nothing",
        census.committed_respelt
    );
    assert!(
        census.committed_case_equal_true >= 60,
        "only {} committed `==` cases had operands equal only modulo case",
        census.committed_case_equal_true
    );
    assert!(
        census.non_ascii_declined + census.non_ascii_committed >= 200,
        "the non-ASCII case families stopped reaching the evaluator: {census:?}"
    );
}

/// Fresh-seed twin of [`case_variant_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching condition.rs"]
fn case_variant_sweep_soak() {
    let (seed, cases) = soak_parameters("condition case-variant", 50_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let census = case_variant_sweep(&mut oracle, &mut rng, cases);
    eprintln!("case-variant soak: {census:?}");
}

/// What one run of [`whitespace_variant_sweep`] saw.
#[derive(Default, Debug)]
struct WhitespaceCensus {
    /// Committed cases whose respelling put a tab or line feed somewhere.
    committed_respelt: usize,
    /// Of those, cases with one inside a quoted string, where MSBuild reads it
    /// as itself.
    committed_inside_quote: usize,
    /// Respelt cases we call illegal: whitespace inside a bare token splits it
    /// (`tr ue`, `= =`, `$(P 0)`).
    illegal_respelt: usize,
}

fn whitespace_variant_sweep(
    oracle: &mut Oracle,
    rng: &mut SplitMix64,
    cases: usize,
) -> WhitespaceCensus {
    let mut census = WhitespaceCensus::default();
    for _ in 0..cases {
        let props = gen_props(rng);
        let condition = if rng.below(2) == 0 {
            let depth = rng.below(3) as u32;
            gen_bool_expr(rng, depth)
        } else {
            gen_case_comparison(rng, &props)
        };
        let respelt = respell_whitespace(rng, &condition);
        let verdict = check_certain_implies_exact(oracle, &respelt, &props);
        if respelt != condition {
            match verdict {
                Verdict::True | Verdict::False => {
                    census.committed_respelt += 1;
                    census.committed_inside_quote += usize::from(breaks_inside_quote(&respelt));
                }
                Verdict::Illegal => census.illegal_respelt += 1,
                Verdict::Unsupported => {}
            }
        }
    }
    census
}

/// The whitespace axis, at a fixed seed: each generated condition with its
/// spaces respelt as tabs and line feeds, which MSBuild reads literally (it
/// does not normalise attribute values), held to certain-implies-exact. Between
/// tokens they are whitespace; inside a quoted string they are characters.
#[test]
fn whitespace_variant_sweep_fixed_seed() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x0007_ab1f_5eed);
    let census = whitespace_variant_sweep(&mut oracle, &mut rng, 3000);
    eprintln!("whitespace-variant sweep: {census:?}");
    // Observed at this seed: 932 respelt, 307 inside a quote.
    assert!(
        census.committed_respelt >= 500,
        "only {} committed cases were respelt — the check is testing nothing",
        census.committed_respelt
    );
    assert!(
        census.committed_inside_quote >= 100,
        "only {} committed cases broke a line inside a quote",
        census.committed_inside_quote
    );
}

/// Which of a document's conditions MSBuild evaluates, so an illegal one
/// rejects the project: the facts a consumer of `Outcome::Illegal` stands on,
/// pinned through the `project` op. A condition behind a false
/// `<PropertyGroup>`, `<ItemDefinitionGroup>` or `<ImportGroup>`, an unchosen
/// `<When>`, or a `<Target>` is never evaluated, syntax errors included, nor is
/// one on a write of a global property. In design-time evaluation (the
/// editable `Project`), an item's condition is evaluated under a false
/// `<ItemGroup>`, and an `Include` item's metadata's under a false item or
/// group, type errors included; a build (`ProjectInstance`) evaluates neither,
/// so it accepts every such project. An `Update` item's metadata's condition is
/// evaluated only where the update applies. `evaluator/rejection.rs` judges
/// conditions by design-time evaluation's facts, which reject every project a
/// build rejects.
#[test]
fn where_msbuild_evaluates_a_condition() {
    /// Whether MSBuild rejects a document, in each of its two evaluations.
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Rejects {
        /// Neither evaluation reads an illegal condition.
        Neither,
        /// Both do.
        Both,
        /// Only design-time evaluation does: it evaluates an `<ItemGroup>`'s
        /// items whatever their conditions hold, and a build does not.
        DesignTimeOnly,
    }
    fn rejects(oracle: &mut Oracle, xml: &str, globals: &[(String, String)]) -> Rejects {
        let both = oracle.project_both(xml, &["R".to_string()], None, globals);
        match (both.design_time.is_none(), both.build.is_none()) {
            (false, _) => Rejects::Neither,
            (true, true) => Rejects::Both,
            (true, false) => Rejects::DesignTimeOnly,
        }
    }
    let mut oracle = Oracle::spawn();
    for (body, rejected) in [
        (
            r#"<PropertyGroup><R Condition="tr ue">x</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<PropertyGroup><R Condition="1 &lt; abc">x</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<PropertyGroup><R Condition="false and 1 &lt; abc">x</R></PropertyGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<PropertyGroup><R Condition="false and (tr ue)">x</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<PropertyGroup><R Condition="false">x</R><R Condition="tr ue">y</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<PropertyGroup Condition="tr ue"><R>x</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<PropertyGroup Condition="false"><R Condition="tr ue">x</R></PropertyGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<PropertyGroup Condition="false"><R Condition="'abc">x</R></PropertyGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<PropertyGroup Condition="false"><R Condition="1 &lt; abc">x</R></PropertyGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemGroup><I Include="x" Condition="tr ue"/></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup Condition="false"><I Include="x" Condition="tr ue"/></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        (
            r#"<ItemGroup Condition="false"><I Include="x" Condition="1 &lt; abc"/></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        (
            r#"<ItemGroup Condition="false"><I Include="x" Condition="foo"/></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        (
            r#"<ItemGroup Condition="false and 1 &lt; abc"><I Include="x"/></ItemGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemGroup><I Include="x" Condition="false"><M Condition="1 &lt; abc">m</M></I></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        // Metadata that reads item metadata is evaluated item by item: not at
        // all for an `Include` that names no item.
        (
            r#"<ItemGroup><I Include="$(Missing)"><O>%(Filename)</O><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemGroup><I Include="x"><O>%(Filename)</O><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Include="x"/><I Remove="x" Condition="tr ue"/></ItemGroup>"#,
            Rejects::Both,
        ),
        (r#"<ItemDefinitionGroup Condition="tr ue"/>"#, Rejects::Both),
        (
            r#"<ItemDefinitionGroup Condition="false"><I><M Condition="tr ue">m</M></I></ItemDefinitionGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemDefinitionGroup><I Condition="false"><M Condition="tr ue">m</M></I></ItemDefinitionGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<Import Project="nope.props" Condition="tr ue"/>"#,
            Rejects::Both,
        ),
        (
            r#"<ImportGroup Condition="false"><Import Project="nope.props" Condition="tr ue"/></ImportGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<Choose><When Condition="tr ue"><PropertyGroup><R>x</R></PropertyGroup></When></Choose>"#,
            Rejects::Both,
        ),
        (
            r#"<Choose><When Condition="true"/><When Condition="tr ue"/></Choose>"#,
            Rejects::Neither,
        ),
        (
            r#"<Choose><When Condition="false"><ItemGroup><I Include="x" Condition="tr ue"/></ItemGroup></When></Choose>"#,
            Rejects::Neither,
        ),
        (
            r#"<Choose><When Condition="true"/><Otherwise><ItemGroup><I Include="x" Condition="tr ue"/></ItemGroup></Otherwise></Choose>"#,
            Rejects::Neither,
        ),
        (
            r#"<UsingTask TaskName="X" AssemblyFile="y.dll" Condition="tr ue"/>"#,
            Rejects::Both,
        ),
        (r#"<Target Name="T" Condition="tr ue"/>"#, Rejects::Neither),
        (
            r#"<Target Name="T"><PropertyGroup><R Condition="tr ue">x</R></PropertyGroup></Target>"#,
            Rejects::Neither,
        ),
        // An `Include` item's metadata, whatever its group or item holds, and
        // whether or not the include names anything; an `Update`'s only
        // where the update applies.
        (
            r#"<ItemGroup Condition="false"><I Include="x"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        (
            r#"<ItemGroup><I Include="nomatch/*.cs"><M Condition="1 &lt; abc">m</M></I></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Include="$(Nothing)"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Include="x" Exclude="x"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Update="nothere"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemGroup><I Include="x"/><I Update="x"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Include="x"/><I Update="x" Condition="false"><M Condition="tr ue">m</M></I></ItemGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<ItemGroup Condition="false"><I Update="x" Condition="1 &lt; abc"/></ItemGroup>"#,
            Rejects::DesignTimeOnly,
        ),
        (
            r#"<ItemDefinitionGroup><I><M Condition="1 &lt; abc">m</M></I></ItemDefinitionGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemDefinitionGroup><I Condition="tr ue"/></ItemDefinitionGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<UsingTask TaskName="X" AssemblyFile="y.dll" Condition="1 &lt; abc"/>"#,
            Rejects::Both,
        ),
        (
            r#"<Choose><When Condition="false"/><Otherwise><ItemGroup><I Include="x" Condition="tr ue"/></ItemGroup></Otherwise></Choose>"#,
            Rejects::Both,
        ),
        // An item list is illegal in a property's condition, even behind a
        // false `and`, and legal in an item's.
        (
            r#"<PropertyGroup><R Condition="false and '@(I)' == ''">x</R></PropertyGroup>"#,
            Rejects::Both,
        ),
        (
            r#"<ItemGroup><I Include="x" Condition="false and '@(I)' == ''"/></ItemGroup>"#,
            Rejects::Neither,
        ),
    ] {
        let xml = format!("<Project>{body}</Project>");
        assert_eq!(rejects(&mut oracle, &xml, &[]), rejected, "{xml}");
    }
    // A write of a global property is discarded with its condition
    // unevaluated; its group's condition is still evaluated.
    let globals = [("G".to_string(), "global".to_string())];
    for (body, rejected) in [
        (
            r#"<PropertyGroup><G Condition="tr ue">x</G></PropertyGroup>"#,
            Rejects::Neither,
        ),
        (
            r#"<PropertyGroup Condition="tr ue"><G>x</G></PropertyGroup>"#,
            Rejects::Both,
        ),
    ] {
        let xml = format!("<Project>{body}</Project>");
        assert_eq!(rejects(&mut oracle, &xml, &globals), rejected, "{xml}");
    }
}

/// Where MSBuild expands a text holding a property function it throws on
/// (`$(P.Split(';')[3])` with `P` holding `a;b`: MSB4184), each row pinned
/// against both evaluations (#1009). A property's body is expanded only under
/// true gates, in a build and design-time evaluation alike. In design-time
/// evaluation, an item's `Include`, `Exclude`, `Remove` and metadata (child or
/// attribute) are expanded whatever its group's or its own condition holds,
/// and a build expands none of them under a false gate; a metadatum under a
/// false condition of its own, and an `Update` that applies to nothing, are
/// expanded by neither. A `<UsingTask>`'s attributes are all expanded, and an
/// item definition's metadata under true gates. `evaluator/rejection.rs`
/// judges these texts by design-time evaluation's facts, as it does
/// conditions.
#[test]
fn where_msbuild_evaluates_a_text() {
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Rejects {
        Neither,
        Both,
        DesignTimeOnly,
    }
    let mut oracle = Oracle::spawn();
    const T: &str = "$(P.Split(';')[3])";
    for (body, rejected) in [
        ("<PropertyGroup><R>{t}</R></PropertyGroup>", Rejects::Both),
        (
            "<PropertyGroup><R Condition=\"false\">{t}</R></PropertyGroup>",
            Rejects::Neither,
        ),
        (
            "<PropertyGroup Condition=\"false\"><R>{t}</R></PropertyGroup>",
            Rejects::Neither,
        ),
        (
            "<Target Name=\"T\"><PropertyGroup><R>{t}</R></PropertyGroup></Target>",
            Rejects::Neither,
        ),
        (
            "<ItemGroup><I Include=\"{t}\" /></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Include=\"{t}\" Condition=\"false\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup Condition=\"false\"><I Include=\"{t}\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup><I Include=\"x\" Exclude=\"{t}\" /></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Include=\"x\" Condition=\"false\" Exclude=\"{t}\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup Condition=\"false\"><I Include=\"x\" Exclude=\"{t}\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup><I Include=\"x\"><M>{t}</M></I></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Include=\"x\" Condition=\"false\"><M>{t}</M></I></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup Condition=\"false\"><I Include=\"x\"><M>{t}</M></I></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup><I Include=\"x\"><M Condition=\"false\">{t}</M></I></ItemGroup>",
            Rejects::Neither,
        ),
        (
            "<ItemGroup><I Include=\"$(Missing)\"><M>{t}</M></I></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Include=\"x\" M=\"{t}\" /></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Include=\"x\" Condition=\"false\" M=\"{t}\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemGroup><I Include=\"x\" /><I Update=\"x\" M=\"{t}\" /></ItemGroup>",
            Rejects::Both,
        ),
        (
            "<ItemGroup><I Update=\"nothere\" M=\"{t}\" /></ItemGroup>",
            Rejects::Neither,
        ),
        ("<ItemGroup><I Remove=\"{t}\" /></ItemGroup>", Rejects::Both),
        (
            "<ItemGroup><I Include=\"x\" /><I Remove=\"{t}\" Condition=\"false\" /></ItemGroup>",
            Rejects::DesignTimeOnly,
        ),
        (
            "<ItemDefinitionGroup><I><M>{t}</M></I></ItemDefinitionGroup>",
            Rejects::Both,
        ),
        (
            "<ItemDefinitionGroup><I M=\"{t}\" /></ItemDefinitionGroup>",
            Rejects::Both,
        ),
        (
            "<ItemDefinitionGroup Condition=\"false\"><I><M>{t}</M></I></ItemDefinitionGroup>",
            Rejects::Neither,
        ),
        (
            "<ItemDefinitionGroup><I><M Condition=\"false\">{t}</M></I></ItemDefinitionGroup>",
            Rejects::Neither,
        ),
        (
            "<UsingTask TaskName=\"{t}\" AssemblyFile=\"y.dll\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"{t}\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyName=\"{t}\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" TaskFactory=\"{t}\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Runtime=\"{t}\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Architecture=\"{t}\" />",
            Rejects::Both,
        ),
        (
            "<UsingTask TaskName=\"X\" AssemblyFile=\"y.dll\" Condition=\"false\" Runtime=\"{t}\" />",
            Rejects::Neither,
        ),
    ] {
        let xml = format!(
            "<Project><PropertyGroup><P>a;b</P></PropertyGroup>{}</Project>",
            body.replace("{t}", T)
        );
        let both = oracle.project_both(&xml, &["P".to_string()], None, &[]);
        let got = match (both.design_time.is_none(), both.build.is_none()) {
            (false, _) => Rejects::Neither,
            (true, true) => Rejects::Both,
            (true, false) => Rejects::DesignTimeOnly,
        };
        assert_eq!(got, rejected, "{xml}");
    }
}

/// Every reserved attribute and a metadatum, on every item operation, holding
/// a property function MSBuild throws on: whether design-time evaluation
/// expands it is MSBuild's to say, and the walk's rejection judgement
/// (`evaluator/rejection.rs`) is held to it, certain-implies-exact. MSBuild
/// builds an `Include` (with its `Exclude` and metadata), else a `Remove`
/// (with its `MatchOnMetadata`), else an `Update` (with its metadata), each
/// expanding only its own attributes; the `MatchOnMetadata` options are
/// parsed as written. An attribute an item takes nowhere is the loader's.
#[test]
fn item_attributes_are_judged_by_their_operation() {
    const T: &str = "$(P.Split(';')[3])";
    const OPERATIONS: &[&str] = &[
        "Include=\"x\"",
        "Remove=\"@(J)\"",
        "Remove=\"@(J)\" MatchOnMetadata=\"M\"",
        "Update=\"x\"",
    ];
    const ATTRIBUTES: &[&str] = &[
        "Include",
        "Exclude",
        "Remove",
        "Update",
        "MatchOnMetadata",
        "MatchOnMetadataOptions",
        "Label",
        "KeepMetadata",
        "RemoveMetadata",
        "KeepDuplicates",
        "M",
    ];
    let mut oracle = Oracle::spawn();
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let project_path = dir.join("Demo.fsproj");
    let (mut rejects, mut evaluates) = (0, 0);
    for operation in OPERATIONS {
        for attribute in ATTRIBUTES {
            if operation.contains(&format!("{attribute}=")) {
                continue;
            }
            let xml = format!(
                "<Project><PropertyGroup><P>a;b</P></PropertyGroup><ItemGroup><J Include=\"x\" \
                 /><I Include=\"x\" /><I {operation} {attribute}=\"{T}\" /></ItemGroup>\
                 <PropertyGroup><After>ok</After></PropertyGroup></Project>"
            );
            std::fs::write(&project_path, &xml).unwrap();
            let parsed = common::parse_fsproj_with_imports(
                &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                    .expect("a project path spelt as its full path"),
                &std::collections::HashMap::new(),
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed");
            let msbuild_rejects = oracle
                .project_design_time(&xml, &["After".to_string()], Some(&project_path), &[])
                .is_none();
            let certainty = parsed.rejection.as_ref().map(|r| r.certainty);
            if msbuild_rejects {
                rejects += 1;
                assert!(
                    certainty.is_some(),
                    "MSBuild rejects, and the walk claims nothing: {xml}"
                );
            } else {
                evaluates += 1;
                assert_ne!(
                    certainty,
                    Some(borzoi_msbuild::RejectionCertainty::Certain),
                    "MSBuild evaluates, and the walk claims it rejects: {xml}"
                );
                assert_eq!(
                    parsed.property("After").value(),
                    Some("ok"),
                    "MSBuild evaluates, and the walk withdrew: {xml}\n{:#?}",
                    parsed.rejection
                );
            }
        }
    }
    assert!(rejects >= 10 && evaluates >= 10, "{rejects} {evaluates}");
}

/// Fresh-seed twin of [`whitespace_variant_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching condition.rs"]
fn whitespace_variant_sweep_soak() {
    let (seed, cases) = soak_parameters("condition whitespace-variant", 50_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let census = whitespace_variant_sweep(&mut oracle, &mut rng, cases);
    eprintln!("whitespace-variant soak: {census:?}");
}

// ---------------------------------------------------------------------------
// `judge`: a condition MSBuild evaluates with some values unknown.
// ---------------------------------------------------------------------------

/// The values an uncertain property is graded under: undefined, empty, a
/// number, a word, and a boolean, which between them take every branch of
/// MSBuild's comparison dispatch and boolean coercion.
const JUDGE_VALUES: &[Option<&str>] = &[None, Some(""), Some("1"), Some("abc"), Some("true")];
const JUDGE_CERTAIN: &[&str] = &["A", "B"];
const JUDGE_UNCERTAIN: &[&str] = &["U", "V"];

fn judge_operand(rng: &mut SplitMix64) -> String {
    let names: Vec<&str> = JUDGE_CERTAIN
        .iter()
        .chain(JUDGE_UNCERTAIN)
        .copied()
        .collect();
    let name = *rng.pick(&names);
    match rng.below(7) {
        0 => format!("'{}'", rng.pick(&["", "1", "2.0", "abc", "true", "x"])),
        1 => format!("'$({name})'"),
        2 => format!("$({name})"),
        3 => format!("'x$({name})'"),
        // Property functions, which may throw on their receiver.
        4 => format!("'$({name}.Substring(1))'"),
        5 => format!("'$({name}.Trim())'"),
        _ => format!("'$({name}.Length)'"),
    }
}

fn judge_condition(rng: &mut SplitMix64, depth: u32) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(6) {
            0 => rng.pick(&["true", "false"]).to_string(),
            1 => judge_operand(rng),
            _ => format!(
                "{} {} {}",
                judge_operand(rng),
                rng.pick(&["==", "!=", "<", ">=", ">"]),
                judge_operand(rng)
            ),
        };
    }
    match rng.below(3) {
        0 => format!("!({})", judge_condition(rng, depth - 1)),
        n => {
            let connective = if n == 1 { " And " } else { " Or " };
            let operands: Vec<String> = (0..2 + rng.below(2))
                .map(|_| judge_condition(rng, depth - 1))
                .collect();
            format!("({})", operands.join(connective))
        }
    }
}

fn property_map<'a>(pairs: impl IntoIterator<Item = &'a (String, String)>) -> PropertyMap {
    let mut map = PropertyMap::new();
    for (name, value) in pairs {
        map.insert(name.as_str(), value.as_str());
    }
    map
}

#[derive(Debug, Default)]
struct JudgeCensus {
    cases: usize,
    /// Conditions judged to have one value though they read an uncertain
    /// property, and MSBuild gave it somewhere.
    committed_despite_uncertain: usize,
    /// Conditions judged to throw on some values, where MSBuild threw on
    /// some and not others.
    maybe_both_ways: usize,
    /// Conditions that read an uncertain property and were judged unable to
    /// throw.
    never_despite_uncertain: usize,
    /// Conditions judged to throw whatever the uncertain values.
    certainly: usize,
}

/// [`judge`] graded against MSBuild under every assignment of the uncertain
/// pair from [`JUDGE_VALUES`]: its value is MSBuild's wherever MSBuild gives
/// one (certain-implies-exact); it never claims MSBuild cannot throw where an
/// assignment makes it throw, outside a part we do not model (which claims
/// nothing); and it claims MSBuild throws for certain only where every
/// assignment does.
fn judge_sweep(oracle: &mut Oracle, rng: &mut SplitMix64, cases: usize) -> JudgeCensus {
    let mut census = JudgeCensus::default();
    let uncertain = |name: &str| JUDGE_UNCERTAIN.iter().any(|u| u.eq_ignore_ascii_case(name));
    for _ in 0..cases {
        let condition = judge_condition(rng, 3);
        let certain: Vec<(String, String)> = JUDGE_CERTAIN
            .iter()
            .filter_map(|name| {
                rng.pick(JUDGE_VALUES)
                    .map(|v| (name.to_string(), v.to_string()))
            })
            .collect();
        // The values the walk holds for the uncertain names, which a sound
        // judgement never reads.
        let held: Vec<(String, String)> = JUDGE_UNCERTAIN
            .iter()
            .filter_map(|name| {
                rng.pick(JUDGE_VALUES)
                    .map(|v| (name.to_string(), v.to_string()))
            })
            .collect();
        let held_map = property_map(certain.iter().chain(&held));
        // Whether the judgement asked about an uncertain name it reached: an
        // operand it never reached does not count.
        let reached_uncertain = std::cell::Cell::new(false);
        let judged = judge(&condition, &held_map, &|name: &str| {
            let is = uncertain(name);
            reached_uncertain.set(reached_uncertain.get() || is);
            is
        });
        census.cases += 1;
        let reads_uncertain = reached_uncertain.get();
        let (mut threw, mut held_value) = (false, false);
        for u in JUDGE_VALUES {
            for v in JUDGE_VALUES {
                let mut props = certain.clone();
                props.extend(u.map(|u| ("U".to_string(), u.to_string())));
                props.extend(v.map(|v| ("V".to_string(), v.to_string())));
                match oracle.eval(&condition, &props) {
                    Some(value) => {
                        held_value = true;
                        assert!(
                            judged.value.is_none_or(|judged| judged == value),
                            "{condition}: judged {judged:?}, MSBuild gives {value} under {props:?}"
                        );
                        assert_ne!(
                            judged.throws,
                            Throws::Certainly,
                            "{condition}: MSBuild gives {value} under {props:?}"
                        );
                    }
                    None => {
                        threw = true;
                        // A part we cannot evaluate on certain values claims
                        // nothing; every other verdict is a claim.
                        if !judged.unevaluated {
                            assert_ne!(
                                judged.throws,
                                Throws::Never,
                                "{condition}: MSBuild throws under {props:?}"
                            );
                        }
                    }
                }
            }
        }
        census.committed_despite_uncertain +=
            usize::from(reads_uncertain && judged.value.is_some() && held_value);
        census.maybe_both_ways +=
            usize::from(judged.throws == Throws::Maybe && threw && held_value);
        census.never_despite_uncertain += usize::from(
            reads_uncertain && judged.throws == Throws::Never && !judged.unevaluated && held_value,
        );
        census.certainly += usize::from(judged.throws == Throws::Certainly);
    }
    census
}

/// [`judge_sweep`] at a fixed seed.
#[test]
fn judge_sweep_fixed_seed() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x0009_0d0e_5eed);
    let census = judge_sweep(&mut oracle, &mut rng, 400);
    eprintln!("judge sweep: {census:?}");
    // Anti-vacuity: each verdict meets conditions that read an uncertain
    // property, MSBuild both throwing and not.
    assert!(census.committed_despite_uncertain >= 10, "{census:?}");
    assert!(census.maybe_both_ways >= 20, "{census:?}");
    assert!(census.never_despite_uncertain >= 10, "{census:?}");
    assert!(census.certainly >= 5, "{census:?}");
}

/// Fresh-seed twin of [`judge_sweep_fixed_seed`].
#[test]
#[ignore = "fresh-seed soak; run it when touching condition.rs"]
fn judge_sweep_soak() {
    let (seed, cases) = soak_parameters("condition judge", 5_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let census = judge_sweep(&mut oracle, &mut rng, cases);
    eprintln!("judge soak: {census:?}");
}

/// Equality and order over every pair of an alphabet of spellings at the edge
/// of what .NET's number, version and boolean parsing accept (NaN, infinity,
/// signs, padding, a trailing NUL, exponents, hex, fullwidth digits, versions,
/// booleans, the empty string), held to certain-implies-exact. The rejection
/// judgement certifies reach through such comparisons, so a committed boolean
/// here must be MSBuild's.
#[test]
fn comparisons_of_edge_spellings_are_certain_implies_exact() {
    const SPELLINGS: &[&str] = &[
        "",
        "1",
        "01",
        "1.0",
        "1.",
        ".5",
        "+1",
        "-1",
        "-0",
        "0",
        " 1",
        "1 ",
        "1%00",
        "%001",
        "1e3",
        "1E3",
        "0x1",
        "0X1",
        "0x",
        "0xFFFFFFFF",
        "\u{ff11}",
        "NaN",
        "nan",
        "-NaN",
        "Infinity",
        "-Infinity",
        "\u{221e}",
        "1.2.3",
        "1.2.3.4",
        "1.2.3.4.5",
        "v1.2",
        "true",
        "on",
        "!false",
        "yes",
        "abc",
        "1,000",
        "1_000",
        "-0.1",
        "+0.1",
        "-0.0",
        "0.0.0",
        "1.-0",
        "1.-1",
        " 1.2",
        "1.2 ",
        "1. 2",
        "01.2",
        "2147483648.0",
        "1.2%00",
        "+-1",
        "- NaN",
        "NaN%00",
        "Current",
        "18",
        "18.0",
    ];
    let mut oracle = Oracle::spawn();
    let mut committed = 0usize;
    for lhs in SPELLINGS {
        for rhs in SPELLINGS {
            for op in ["==", "!=", "<", ">="] {
                let condition = format!("'{lhs}' {op} '{rhs}'");
                if matches!(
                    check_certain_implies_exact(&mut oracle, &condition, &[]),
                    Verdict::True | Verdict::False
                ) {
                    committed += 1;
                }
            }
        }
    }
    assert!(committed >= 2000, "only {committed} committed");
}

/// MSBuild reads a NaN spelling as a number, and NaN equals nothing, itself
/// included; it orders against nothing either, without throwing. Each
/// spelling, beside itself, another NaN, a number and a word, held to
/// certain-implies-exact.
#[test]
fn nan_operands_are_never_committed_wrongly() {
    let mut oracle = Oracle::spawn();
    for spelling in [
        "NaN",
        "nan",
        "NAN",
        "-NaN",
        "+NaN",
        " NaN",
        "NaN ",
        "\u{a0}NaN",
    ] {
        for other in [spelling, "NaN", "1", "abc", ""] {
            for op in ["==", "!=", "<", ">="] {
                let condition = format!("'{spelling}' {op} '{other}'");
                check_certain_implies_exact(&mut oracle, &condition, &[]);
            }
        }
    }
    // A throw past a NaN comparison is reached only if that comparison is
    // true, which MSBuild never makes it.
    let uncertain = |name: &str| name == "U";
    let judged = judge(
        "'NaN' == 'NaN' And 1 < abc And '$(U)' == ''",
        &PropertyMap::new(),
        &uncertain,
    );
    assert_ne!(judged.throws, Throws::Certainly, "{judged:?}");
}

// ---------------------------------------------------------------------------
// `Exists()` against the file system.
// ---------------------------------------------------------------------------

/// `Exists()` over a real tree. Unix-only: the tree is made of symlinks, a
/// socket and a FIFO.
#[cfg(unix)]
mod exists_on_disk {
    use super::*;
    use borzoi_msbuild::test_support::{Outcome, PropertyMap, evaluate_with_exists};
    use std::path::PathBuf;

    /// A tree of every kind of entry `Exists()` can meet, under a fresh directory:
    /// files, directories, symlinks to each, a dangling symlink and a chain ending
    /// in one, a symlink loop, a link to `..`, a socket, a FIFO (which neither side
    /// opens to probe), and a directory link out
    /// of the project directory (`d/up`), whose `..` the OS and .NET resolve
    /// differently. `proj` is the project directory every relative path resolves
    /// against.
    ///
    /// The tree lives under the system temporary directory, whose path is short:
    /// a socket's path must fit in `sun_path` (107 bytes on Linux, 103 on macOS).
    /// Where it still does not, the tree has no socket and `sock` is a missing
    /// name to both sides.
    struct ExistsTree {
        _dir: tempfile::TempDir,
        root: PathBuf,
        socket: Option<std::os::unix::net::UnixListener>,
    }

    impl ExistsTree {
        fn new() -> Self {
            use std::os::unix::fs::symlink;
            let dir = tempfile::tempdir().expect("tempdir");
            let root = dir.path().to_path_buf();
            let proj = root.join("proj");
            for sub in ["proj/d", "other"] {
                std::fs::create_dir_all(root.join(sub)).expect("mkdir");
            }
            for file in ["proj/f", "proj/d/g", "other/o"] {
                std::fs::write(root.join(file), "").expect("write");
            }
            for (target, link) in [
                ("f", "flink"),
                ("d", "dlink"),
                ("missing", "dangling"),
                ("dangling", "chain"),
                ("loop", "loop"),
                ("..", "dirup"),
                ("../../other", "d/up"),
            ] {
                symlink(target, proj.join(link)).expect("symlink");
            }
            let socket = std::os::unix::net::UnixListener::bind(proj.join("sock")).ok();
            common::odd_entry::place(
                common::odd_entry::Odd::Fifo,
                &proj.join("pipe"),
                "",
                &root.join("aside"),
            );
            ExistsTree {
                _dir: dir,
                root,
                socket,
            }
        }

        fn proj(&self) -> PathBuf {
            self.root.join("proj")
        }
    }

    /// The names a generated path is spelt from: every entry of [`ExistsTree`],
    /// a case respelling, names that are not there, and the relative segments.
    const EXISTS_SEGMENTS: &[&str] = &[
        "f", "F", "d", "g", "up", "flink", "dlink", "dangling", "chain", "loop", "dirup", "sock",
        "pipe", "o", "other", "proj", "missing", "x%00", "..", "..", ".", "",
    ];

    /// One `Exists()` argument: a `;` list of one to three generated paths, each
    /// relative or rooted in the tree, `/` or `\` separated, with or without a
    /// trailing separator, padded or not, and sometimes routed through a property
    /// or spelt with an escape. `props` collects the properties it references.
    fn gen_exists_argument(
        rng: &mut SplitMix64,
        tree: &ExistsTree,
        props: &mut Vec<(String, String)>,
    ) -> String {
        let entries = 1 + rng.below(3) * rng.below(2);
        let mut list = Vec::new();
        for _ in 0..entries {
            let mut path = String::new();
            if rng.below(5) == 0 {
                path.push_str(&tree.root.to_string_lossy());
                path.push('/');
                path.push_str(rng.pick(&["proj/", "other/", ""]));
            }
            let segments = 1 + rng.below(2) + rng.below(2);
            for i in 0..segments {
                if i > 0 {
                    path.push_str(rng.pick(&["/", "/", "\\"]));
                }
                path.push_str(rng.pick(EXISTS_SEGMENTS));
            }
            if rng.below(5) == 0 {
                path.push_str(rng.pick(&["/", "\\", "/."]));
            }
            if rng.below(8) == 0 {
                // An escape decodes to the character it spells: a `.`, a
                // separator, or a `;` that is filename data rather than a split.
                if let Some(at) = path.find(['.', '/', 'f']) {
                    let escape = match path.as_bytes()[at] {
                        b'.' => "%2e",
                        b'/' => *rng.pick(&["%2f", "%5c"]),
                        _ => "%66",
                    };
                    path.replace_range(at..at + 1, escape);
                }
            }
            if rng.below(6) == 0 {
                let name = format!("ExistsP{}", props.len());
                props.push((name.clone(), path));
                path = format!("$({name})");
            }
            if rng.below(6) == 0 {
                path = format!(" {path} ");
            }
            list.push(path);
        }
        let mut argument = list.join(";");
        if rng.below(10) == 0 {
            argument.push(';');
        }
        argument
    }

    fn xml_escape(text: &str) -> String {
        text.replace('&', "&amp;")
            .replace('<', "&lt;")
            .replace('>', "&gt;")
            .replace('"', "&quot;")
    }

    /// What one batch of `Exists()` conditions came to, both sides.
    #[derive(Default, Debug)]
    struct ExistsCensus {
        committed_true: usize,
        committed_false: usize,
        declined: usize,
    }

    /// Grade `conditions` (with `props`) against MSBuild, certain-implies-exact:
    /// each is a property element's condition in a project in `tree`'s project
    /// directory, so its relative `Exists()` paths resolve there, as ours do.
    fn grade_exists_batch(
        oracle: &mut Oracle,
        tree: &ExistsTree,
        conditions: &[String],
        props: &[(String, String)],
        census: &mut ExistsCensus,
    ) {
        let mut xml = String::from("<Project><PropertyGroup>");
        for (name, value) in props {
            xml.push_str(&format!("<{name}>{}</{name}>", xml_escape(value)));
        }
        xml.push_str("</PropertyGroup><PropertyGroup>");
        let names: Vec<String> = (0..conditions.len()).map(|i| format!("R{i}")).collect();
        for (name, condition) in names.iter().zip(conditions) {
            xml.push_str(&format!(
                "<{name} Condition=\"{}\">T</{name}>",
                xml_escape(condition)
            ));
        }
        xml.push_str("</PropertyGroup></Project>");
        let project = tree.proj().join("p.proj");
        let theirs = oracle
            .project(&xml, &names, Some(&project), &[])
            .unwrap_or_else(|| panic!("MSBuild rejects the batch:\n{xml}"));
        let mut map = PropertyMap::new();
        for (name, value) in props {
            map.insert(name.clone(), value.clone());
        }
        for (name, condition) in names.iter().zip(conditions) {
            let ours = evaluate_with_exists(condition, &map, &tree.proj());
            let theirs = theirs[name] == "T";
            match ours {
                Outcome::Unsupported => census.declined += 1,
                // MSBuild evaluated the batch, so it rejects none of them.
                Outcome::Illegal => panic!(
                    "certain-implies-exact violated: we say Illegal for {condition:?} with \
                     {props:?}, but MSBuild evaluates it"
                ),
                Outcome::True | Outcome::False => {
                    let ours = ours == Outcome::True;
                    assert_eq!(
                        ours,
                        theirs,
                        "certain-implies-exact violated for {condition:?} with {props:?} \
                     (project directory {})",
                        tree.proj().display()
                    );
                    if ours {
                        census.committed_true += 1;
                    } else {
                        census.committed_false += 1;
                    }
                }
            }
        }
    }

    /// Hand-picked `Exists()` corners, each pinned to MSBuild's answer here and
    /// round-tripped through the oracle: a dangling symlink exists, `..` collapses
    /// as text before the file system sees it, a trailing separator asks for a
    /// directory, and the argument is a `;` list every entry of which must exist.
    #[test]
    fn exists_corners() {
        let tree = ExistsTree::new();
        let mut oracle = Oracle::spawn();
        let dangling = tree.proj().join("dangling").to_string_lossy().into_owned();
        let mut cases: Vec<(&str, bool)> = vec![
            ("f", true),
            ("dangling", true),
            ("chain", true),
            ("loop", true),
            ("dangling/", false),
            ("dangling/.", true),
            ("dlink/", true),
            ("f/", false),
            // `d/up` is `other`; lexically `d/up/..` is `d`.
            ("d/up/o", true),
            ("d/up/../g", true),
            ("d/up/../../other/o", false),
            ("dirup/proj/f", true),
            ("missing/../f", true),
            ("f;flink", true),
            ("f;missing", false),
            ("f%3bflink", false),
            (";", false),
            // .NET rejects a NUL before a `..` can erase it.
            ("bad%00/../f", false),
            ("d\\g", true),
        ];
        // A socket is no directory, so a file to `File.Exists`.
        cases.push(("sock", tree.socket.is_some()));
        // So is a FIFO, which `File.Exists` does not open.
        cases.extend([("pipe", true), ("pipe/", false)]);
        let conditions: Vec<String> = cases
            .iter()
            .map(|(path, _)| format!("Exists('{path}')"))
            .chain([format!("Exists('{dangling}')")])
            .collect();
        let mut census = ExistsCensus::default();
        grade_exists_batch(&mut oracle, &tree, &conditions, &[], &mut census);
        for ((path, expected), condition) in cases.iter().zip(&conditions) {
            let ours = evaluate_with_exists(condition, &PropertyMap::new(), &tree.proj());
            let ours = match ours {
                Outcome::True => true,
                Outcome::False => false,
                Outcome::Illegal | Outcome::Unsupported => panic!("{path}: declined"),
            };
            assert_eq!(ours, *expected, "Exists('{path}')");
        }
        assert_eq!(census.declined, 0, "{census:?}");
        // An escaped `\` decides rootedness apart from its role as a separator.
        let root = tree.root.to_string_lossy();
        for declined in ["d%5cg".to_owned(), format!("%5c{}/proj/f", &root[1..])] {
            let condition = format!("Exists('{declined}')");
            assert_eq!(
                evaluate_with_exists(&condition, &PropertyMap::new(), &tree.proj()),
                Outcome::Unsupported,
                "{condition}"
            );
        }
    }

    /// Generated `Exists()` arguments over [`ExistsTree`], certain-implies-exact.
    fn exists_sweep(seed: u64, cases: usize) -> ExistsCensus {
        let tree = ExistsTree::new();
        let mut oracle = Oracle::spawn();
        let mut rng = SplitMix64(seed);
        let mut census = ExistsCensus::default();
        const BATCH: usize = 100;
        let mut done = 0;
        while done < cases {
            let mut props = Vec::new();
            let conditions: Vec<String> = (0..BATCH.min(cases - done))
                .map(|_| {
                    format!(
                        "Exists('{}')",
                        gen_exists_argument(&mut rng, &tree, &mut props)
                    )
                })
                .collect();
            grade_exists_batch(&mut oracle, &tree, &conditions, &props, &mut census);
            done += conditions.len();
        }
        census
    }

    #[test]
    fn exists_matches_msbuild_over_a_generated_tree() {
        let census = exists_sweep(0xe815_75ee_d000, 4000);
        eprintln!("exists sweep: {census:?}");
        assert!(
            census.committed_true >= 500 && census.committed_false >= 500,
            "{census:?}"
        );
    }

    /// Fresh-seed twin of [`exists_matches_msbuild_over_a_generated_tree`].
    #[test]
    #[ignore = "fresh-seed soak; run it when touching Exists()"]
    fn exists_soak() {
        let (seed, cases) = soak_parameters("condition exists", 20_000);
        eprintln!("exists soak: {:?}", exists_sweep(seed, cases));
    }
}
