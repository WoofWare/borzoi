//! Evaluator for MSBuild `Condition` attributes.
//!
//! Phase 3 implements the subset described in plan D5: single-quoted
//! string literals (with `$(Name)` substitution inside), `==` / `!=`
//! equality mirroring MSBuild's `MultipleComparisonNode` dispatch (empty
//! short-circuit, then double-numeric — decimal or hex — then MSBuild
//! boolean vocabulary, then case-insensitive string equality), relational
//! comparisons mirroring `NumericComparisonExpressionNode` (doubles,
//! `System.Version`-style dotted versions, and MSBuild's mixed
//! number-vs-version major-only rule), MSBuild version comparison
//! functions, the `System.Version.Parse(...).Build/Revision` comparisons the
//! SDK uses, the pure `HasTrailingSlash('...')` built-in, `And` / `Or`
//! boolean connectives, unary `!`, parentheses, bare `true` / `false`
//! literals, and a standalone scalar coerced to bool through MSBuild's
//! boolean vocabulary (`Condition="$(SomeBool)"`, `!$(V.Contains('{'))`).
//! Fixed names (keywords, property-function type/member names) match
//! case-insensitively throughout, as MSBuild's do. The filesystem-touching
//! entry point additionally gives `Exists('...')` a filesystem callback;
//! pure evaluation treats a reached `Exists` call as [`Outcome::Unsupported`].
//! Anything outside that grammar — arithmetic, `@(...)` item references,
//! unmodelled property functions — produces [`Outcome::Unsupported`], at which
//! point the caller treats the containing construct as **excluded** (plan D5).
//! A condition MSBuild itself throws on is [`Outcome::Illegal`] where we can
//! show it does: a syntax error MSBuild's parser reports (the [`syntax`]
//! port), and the evaluation errors whose every input we compute exactly. Any
//! other failure stays `Unsupported`, which makes no claim either way.
//!
//! The comparison semantics were derived from MSBuild's own evaluator
//! (`src/Build/Evaluation/Conditionals/*.cs` — `MultipleComparisonNode`,
//! `NumericComparisonExpressionNode`, `ConversionUtilities`) and pinned by
//! unit tests verified against `dotnet msbuild` 10.0.300; tests below cite
//! that oracle.
//!
//! We deliberately fail safe: when we can't tell whether a condition is
//! true or false, we MUST NOT proceed as if it were true. Otherwise a
//! `<Compile Include="DebugOnly.fs" Condition="$([System.String]::IsNullOrEmpty('$(Foo)'))" />`
//! (an unmodelled property function) would silently leak into Release
//! builds. Excluding (and surfacing a diagnostic) preserves the "never
//! produce wrong output" promise.
//!
//! Property substitution inside condition strings reuses the main
//! [`crate::properties::substitute_in_world`] function. Undefined references become
//! `""` (matching MSBuild's "unset property → empty string" rule) so
//! we can still compute a truth value, but the names of every
//! undefined reference are returned alongside the outcome so the
//! walker can emit [`UndefinedProperty`](super::diagnostic::DiagnosticKind::UndefinedProperty)
//! diagnostics. Without that, a condition like
//! `'$(TargetFramework)' == '$(FcsTargetNetFxFramework)'` (both sides
//! undefined here) silently expands to `'' == ''` = true, picking a
//! branch MSBuild might not — see plan D5's fail-loud stance.
//!
//! The standard protected-write idiom
//! (`<Configuration Condition="'$(Configuration)' == ''">Debug</…>`)
//! is unaffected: the walker short-circuits protected writes *before*
//! evaluating the condition, so the diagnostic never fires for that
//! pattern. Unsupported expressions (unknown property functions, item
//! references inside the substitution) still poison the whole condition.

mod syntax;

use std::ops::Range;

use super::observed::Observer;
use super::properties::escaping::Escaped;
use super::properties::worlds::{self, Start, World, Worlds};
use super::properties::{
    Issue, MAX_EXPRESSION_NESTING, PropertyMap, Provenanced, path_fixup, substitute_in_world,
};

/// The file-system queries a condition may make: `exists` answers
/// `Exists('…')` for one decoded, trimmed entry of its argument's list,
/// and the property functions that probe the file system
/// (`GetDirectoryNameOfFileAbove`) query through `observer`. A condition
/// evaluated without them treats both as unsupported.
///
/// `start` is what the evaluation knows about MSBuild's startup directory,
/// under which the Unix path adjustment probes a relative segment
/// ([`worlds`]). A condition is evaluated in every world it allows, and
/// decided only where every world decides it the same way; a condition
/// evaluated without `Probes` knows no startup directory.
#[derive(Clone, Copy)]
pub(crate) struct Probes<'a> {
    pub exists: &'a dyn Fn(&str) -> bool,
    pub observer: &'a Observer,
    pub start: Start<'a>,
}

/// Where MSBuild evaluates a condition, which decides two things about it.
///
/// Design-time evaluation of a condition of the property pass (a property, a
/// property group, a `When`, an import or import group) records the
/// conditioned properties, and so expands both sides of an equality in full
/// even where one side's emptiness decides it
/// (`MultipleComparisonExpressionNode.UpdateConditionedProperties`;
/// `Evaluator`'s `EvaluateConditionCollectingConditionedProperties`); a
/// condition of the item pass records none.
///
/// A condition of the item pass (an item, a metadatum, an item group, a
/// `<UsingTask>`) expands an item list or metadatum its properties' values
/// form (`@(I)` from `$(A)$(B)`), and may throw on it; one of the property
/// pass reads it as text (`'$(A)$(B)' != ''` is true there; probed,
/// `msbuild-condition-oracle`, SDK 10.0.401), and so does one of an item
/// definition, which expands properties and metadata alone and records no
/// conditioned properties. The oracle's `eval` op, which `evaluate` is held
/// to, evaluates as the item pass does. `tests/condition_diff.rs`'s
/// `condition_sites_expand_as_msbuild_does` pins each construct's site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Site {
    /// A condition of the property pass, in design-time evaluation.
    PropertyPass,
    /// A condition of the item pass but an item definition's.
    ItemPass,
    /// A condition of an item definition group, a definition in it, or one of
    /// its metadata.
    ItemDefinition,
}

/// What an evaluation reaches beyond the property table: the file system,
/// where the caller gives one, the condition's [`Site`], and the world of
/// MSBuild's startup directory it reads the table in ([`worlds::World`]):
/// `None` outside an enumeration of them, where a read takes the value where
/// no segment is a directory.
#[derive(Clone, Copy)]
struct Ctx<'a> {
    probes: Option<Probes<'a>>,
    site: Site,
    world: Option<&'a World<'a>>,
}

impl<'a> Ctx<'a> {
    fn new(probes: Option<Probes<'a>>, site: Site) -> Self {
        Ctx {
            probes,
            site,
            world: None,
        }
    }

    fn observer(&self) -> Option<&Observer> {
        self.probes.map(|probes| probes.observer)
    }

    /// What MSBuild's startup directory may be.
    fn start(&self) -> Start<'a> {
        self.probes.map_or(Start::Unknown, |probes| probes.start)
    }

    /// `self` in `world`.
    fn in_world<'b>(&self, world: &'b World<'b>) -> Ctx<'b>
    where
        'a: 'b,
    {
        Ctx {
            probes: self.probes,
            site: self.site,
            world: Some(world),
        }
    }

    /// `text` substituted in this context's world.
    fn substitute(&self, text: &str, props: &PropertyMap) -> (Provenanced<Escaped>, Vec<Issue>) {
        match self.world {
            Some(world) => substitute_in_world(text, props, self.observer(), world),
            None => substitute_in_world(text, props, self.observer(), &World::absent_everywhere()),
        }
    }

    /// The value `name` holds in this context's world.
    fn value<'m>(&self, props: &'m PropertyMap, name: &str) -> Option<&'m Escaped> {
        let worlds = props.get_ignoring_trust(name)?;
        Some(match self.world {
            Some(world) => world.read(worlds),
            None => worlds.absent_everywhere(),
        })
    }
}

/// A condition's value in each world: a boolean, or a rejection within that
/// world. `Err(TooManySegments)` when the condition asks about more of
/// MSBuild's startup directory than the walk enumerates.
type InEveryWorld = Result<Worlds<Result<bool, Reject>>, worlds::TooManySegments>;

/// `expr` evaluated in every world `fs` allows, with the undefined names the
/// evaluations read: the first world's in order, then any other world's it
/// lacks.
fn eval_in_every_world(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
) -> (InEveryWorld, Vec<String>) {
    let mut undefined: Vec<String> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut first = true;
    let value = worlds::in_every_world(fs.start(), |world| {
        let mut read = Vec::new();
        let value = eval_bool(expr, props, fs.in_world(world), &mut read);
        if first {
            seen.extend(read.iter().cloned());
            undefined = read;
            first = false;
        } else {
            for name in read {
                if seen.insert(name.clone()) {
                    undefined.push(name);
                }
            }
        }
        value
    });
    (value, undefined)
}

/// Result of evaluating a condition string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    True,
    False,
    /// MSBuild throws evaluating this condition against exactly these
    /// property values (`InvalidProjectFileException`), which rejects the
    /// whole project. Either its syntax is illegal, which MSBuild reports
    /// whatever the values and however `And`/`Or` short-circuit, or the part
    /// of it MSBuild evaluates is ill typed: a relational comparison on an
    /// operand that is neither a number nor a version (`1 < abc`), a scalar
    /// standing as a boolean outside the boolean vocabulary (`foo`,
    /// `$(Unset)`), `HasTrailingSlash` given more than one item, a property
    /// function that fails on its input (an indexer out of range, a version
    /// function given no version: MSB4184). An ill-typed operand behind a
    /// deciding `And`/`Or` operand is never evaluated, by MSBuild or by us.
    ///
    /// A claim about the values given, not about the build: a consumer that
    /// concludes MSBuild rejects the project must hold every property the
    /// condition reads to the same trust a committed boolean needs. As for
    /// `Unsupported`, the [`Eval`] carries no undefined names. Nor is every
    /// condition MSBuild meets in a document evaluated: those under a false
    /// `<PropertyGroup>`, `<ItemDefinitionGroup>` or unchosen `<When>`, and
    /// those under a `<Target>`, are not, while an item's condition under a
    /// false `<ItemGroup>`, or its metadata's under a false item, are
    /// (`tests/condition_diff.rs`'s `where_msbuild_evaluates_a_condition`).
    Illegal,
    /// The condition contains syntax or operators outside the
    /// grammar we model, or asks about more of MSBuild's startup directory
    /// than the walk enumerates. Treat the containing construct as
    /// excluded; do NOT proceed as if it were true. MSBuild may evaluate it to
    /// either boolean, or reject it.
    Unsupported,
    /// MSBuild evaluates the condition to a boolean wherever it starts, and
    /// to different booleans by what its startup directory holds
    /// (`super::properties::worlds`). Treat the containing construct as
    /// excluded, as for [`Outcome::Unsupported`]; but MSBuild does not reject
    /// the project over it.
    StartupDirectory,
}

/// Why a condition, or a part of it, has no boolean: what MSBuild does there,
/// classified three ways.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Reject {
    /// MSBuild returns a boolean we cannot compute, and does not throw: a
    /// string equality whose case folding we do not model, an `Exists` we
    /// cannot ask, an operand whose value turns on the Unix path adjustment
    /// read where no value throws ([`Outcome::Unsupported`]).
    Undecided,
    /// Outside what we model: MSBuild may return either boolean, or throw
    /// ([`Outcome::Unsupported`]).
    Unmodelled,
    /// MSBuild throws on it, in a function the operand calls on these values:
    /// a property function (an indexer out of range), or a version function
    /// given no version ([`Outcome::Illegal`]).
    Throws,
    /// MSBuild throws on it: a syntax error, or an operand of a type the
    /// leaf does not take, a relational comparison's non-number, a coerced
    /// non-boolean ([`Outcome::Illegal`]).
    Illegal,
}

impl Reject {
    /// This rejection of an operand, read by a leaf that throws on some value
    /// of it (a relational comparison, a boolean coercion, `HasTrailingSlash`,
    /// a version function): an operand whose value we do not know may be one
    /// it throws on.
    fn read_by_throwing_leaf(self) -> Self {
        match self {
            Reject::Undecided => Reject::Unmodelled,
            other => other,
        }
    }

    /// What `judge` makes of a leaf that has no boolean on certain values.
    fn judged(self) -> Judgement {
        let throws = match self {
            Reject::Undecided => Throws::Never,
            Reject::Unmodelled => Throws::Maybe,
            Reject::Throws | Reject::Illegal => Throws::Certainly,
        };
        Judgement::of(None, throws, true)
    }

    /// What the walk's rejection judgement ([`may_throw_on_held`]) makes of a
    /// leaf that fails on a value the walk holds and MSBuild need not hold
    /// (`""` for a write the walk refused to compute, or a reserved name it
    /// does not seed). A leaf of a type that rejects that value (a relational
    /// comparison, a coerced scalar) is still a site: an unset name is `""`,
    /// and MSBuild may leave it unset. Whether a function the leaf calls
    /// throws on MSBuild's value, or one we do not model does, is the
    /// judgement over the values a name may hold (#1009's second stage), not
    /// made here.
    fn judged_on_doubted_values(self) -> Judgement {
        let throws = match self {
            Reject::Illegal => Throws::Certainly,
            Reject::Undecided | Reject::Unmodelled | Reject::Throws => Throws::Never,
        };
        Judgement::of(None, throws, true)
    }
}

/// A helper's `Err(())` claims nothing about MSBuild: it may throw there.
impl From<()> for Reject {
    fn from((): ()) -> Self {
        Reject::Unmodelled
    }
}

/// Outcome plus the names of any `$(...)` references encountered
/// during evaluation that weren't defined in the supplied
/// [`PropertyMap`]. Each was substituted to `""`, so the outcome is
/// still meaningful (and matches what MSBuild would compute given the
/// same property map), but callers should emit an
/// [`UndefinedProperty`](super::diagnostic::DiagnosticKind::UndefinedProperty)
/// diagnostic per name and mark the project partial — our map may be
/// missing values MSBuild itself would have seen (imported targets,
/// environment, etc.), making our truth value potentially divergent.
/// Names are returned in encounter order with duplicates preserved,
/// matching how `properties::substitute` reports issues for
/// non-condition substitution sites elsewhere in the parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Eval {
    pub outcome: Outcome,
    pub undefined_properties: Vec<String>,
    /// The subset of [`Self::undefined_properties`] with at least one
    /// occurrence *outside* a comparison against the empty literal
    /// (`'$(X)' == ''` / `'$(X)' != ''`). The empty-comparison shape is
    /// the MSBuild default-fill / is-it-set idiom, which the evaluator's
    /// self-default exemption may treat as deterministic; any other
    /// context (`'$(X)' != 'bar'`, `Exists('$(X)')`, …) is a genuine
    /// branch decision on the unknown value and must never be exempt.
    pub undefined_outside_empty_comparison: Vec<String>,
}

/// Evaluate a `Condition` attribute against the current property map.
///
/// Returns [`Outcome::True`] / [`Outcome::False`] when the entire
/// expression reduces to a boolean within our grammar, and
/// [`Outcome::Unsupported`] when any part of the parse or any
/// `$(...)` expansion strays outside it. Whitespace around tokens is
/// insignificant; an entirely-blank condition string evaluates as
/// [`Outcome::True`] (matching MSBuild, which omits the attribute and
/// the attribute-with-only-whitespace-content identically).
///
/// When the outcome is `Unsupported` or `Illegal`, the
/// `undefined_properties` list is empty: the `UnsupportedCondition`
/// diagnostic the caller will emit subsumes any per-property concerns, and
/// reporting both would double up. For `True` / `False`, the list is
/// populated.
#[cfg(any(test, feature = "test-support"))]
pub fn evaluate(source: &str, props: &PropertyMap) -> Eval {
    evaluate_inner(source, props, Ctx::new(None, Site::ItemPass))
}

/// Evaluate a condition with support for MSBuild's filesystem-backed
/// `Exists('...')` predicate and the property functions that probe the file
/// system (see [`Probes`]).
#[cfg(any(test, feature = "test-support"))]
pub fn evaluate_with_exists(source: &str, props: &PropertyMap, probes: Probes<'_>) -> Eval {
    evaluate_inner(source, props, Ctx::new(Some(probes), Site::ItemPass))
}

/// A condition evaluated at `site`, with the file system where
/// `probes` gives one.
pub(crate) fn evaluate_at(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
) -> Eval {
    evaluate_inner(source, props, Ctx::new(probes, site))
}

/// Whether `source` evaluates differently by MSBuild's startup directory, or
/// asks about more of it than the walk enumerates: why an evaluation of it at
/// `site` is undecided when its grammar is not to blame.
pub(crate) fn depends_on_startup_directory(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
) -> bool {
    let Ok(Some(expr)) = parse_condition(source) else {
        return false;
    };
    !matches!(
        eval_in_every_world(&expr, props, Ctx::new(probes, site)).0,
        Ok(Worlds::Same(_))
    )
}

fn evaluate_inner(source: &str, props: &PropertyMap, fs: Ctx<'_>) -> Eval {
    let expr = match parse_condition(source) {
        Ok(Some(expr)) => expr,
        Ok(None) => {
            return Eval {
                outcome: Outcome::True,
                undefined_properties: Vec::new(),
                undefined_outside_empty_comparison: Vec::new(),
            };
        }
        Err(reject) => return rejected(reject),
    };
    // A condition whose value turns on MSBuild's startup directory has none
    // the walk can commit to, as one outside the grammar has none. Where every
    // world returns a boolean, no world throws.
    let (value, undefined) = match eval_in_every_world(&expr, props, fs) {
        (Ok(Worlds::Same(value)), undefined) => (value, undefined),
        (Ok(split), _) if split.values().iter().all(|value| value.is_ok()) => {
            return Eval {
                outcome: Outcome::StartupDirectory,
                undefined_properties: Vec::new(),
                undefined_outside_empty_comparison: Vec::new(),
            };
        }
        // A world that returns a boolean, or may, is one MSBuild may start in
        // without throwing: no claim of a rejection. Only where every world
        // throws, or every one rejects alike, does the worst stand for them.
        (Ok(split), _) => {
            let values = split.values();
            if values.iter().any(|value| value.is_ok()) {
                return rejected(Reject::Unmodelled);
            }
            let rejects: Vec<Reject> = values.into_iter().filter_map(|value| value.err()).collect();
            let worst = *rejects
                .iter()
                .max()
                .expect("a split with a non-boolean world");
            let least = *rejects
                .iter()
                .min()
                .expect("a split with a non-boolean world");
            if least >= Reject::Throws || least == worst {
                return rejected(worst);
            }
            return rejected(Reject::Unmodelled);
        }
        (Err(worlds::TooManySegments), _) => return rejected(Reject::Unmodelled),
    };
    let outcome = match value {
        Ok(true) => Outcome::True,
        Ok(false) => Outcome::False,
        Err(reject) => {
            // Discard any undefined names we may have collected: the
            // UnsupportedCondition diagnostic the caller raises is
            // the authoritative description of the failure, and a
            // separate UndefinedProperty for some property mentioned
            // in the same condition would be redundant noise.
            return rejected(reject);
        }
    };
    // Scan the *whole parsed tree* for reference contexts — evaluation
    // above short-circuits (`'$(X)' == '' Or '$(X)' == 'x'` never expands
    // the second arm when the first is true), so evaluation-order records
    // would under-report non-default uses.
    let mut outside = Vec::new();
    refs_outside_empty_comparison(&expr, &mut outside);
    let undefined_outside_empty_comparison = undefined
        .iter()
        .filter(|name| outside.iter().any(|o| o.eq_ignore_ascii_case(name)))
        .cloned()
        .collect();
    Eval {
        outcome,
        undefined_properties: undefined,
        undefined_outside_empty_comparison,
    }
}

/// Parse a condition into its tree: `Ok(None)` for an empty condition (which
/// MSBuild treats as true), `Err` for anything outside the grammar, which is
/// [`Reject::Illegal`] when MSBuild's own parser rejects it too, as it does a
/// condition of whitespace alone (MSB4092; probed, `dotnet msbuild` 10.0).
fn parse_condition(source: &str) -> Result<Option<BoolExpr>, Reject> {
    parse_modelled(source).map_err(|()| match syntax::msbuild_parse(source) {
        syntax::Syntax::Rejects => Reject::Illegal,
        syntax::Syntax::Parses | syntax::Syntax::Unknown => Reject::Unmodelled,
    })
}

/// [`parse_condition`] within the grammar we model.
fn parse_modelled(source: &str) -> Result<Option<BoolExpr>, ()> {
    if source.is_empty() {
        return Ok(None);
    }
    if source.trim().is_empty() {
        return Err(());
    }
    // MSBuild's condition scanner lexes item-list (`@(`) and metadata (`%(`)
    // references directly from the *raw* condition text, before any property
    // expansion; we model neither, and MSBuild treats a bare marker in a
    // condition as a hard lex error. A single scan of the raw source closes
    // that whole class up front: some of our reductions (string instance
    // methods, `System.Version` parts, version functions) collapse a `$(…)`
    // subexpression to a value *before* the operand-level `@(`/`%(` check in
    // `expand_for_condition` can see it, which would otherwise let a raw
    // marker in the source slip through and commit us to a boolean MSBuild
    // never reaches. Rejecting here is uniform and structural — no individual
    // reducer needs its own marker guard.
    //
    // Markers arriving *only* via `$()` substitution are not in the raw
    // source and are unaffected, matching MSBuild (it never re-lexes
    // substituted text). This is deliberately conservative: it also rejects
    // the rare balanced `@(x)` forms MSBuild happens to accept, but only ever
    // toward `Unsupported`, never a wrong committed gate.
    if source.contains("@(") || source.contains("%(") {
        return Err(());
    }
    // NB: escape-bearing conditions are **modelled**, not degraded (stage E2 of
    // `docs/completed/msbuild-escaped-value-plan.md`). MSBuild unescapes `%XX` at the
    // operand leaf, so `'%74rue' == 'true'` is *true* — and `expand_for_condition`
    // decodes each operand there, exactly once, having scanned it escaped.
    //
    // A `%` **outside** quotes needs no guard here: it is not an escape at all,
    // because MSBuild's scanner rejects it (`MSB4090: Found an unexpected
    // character '7' … in condition "%74rue"`). Our tokeniser reaches the same
    // verdict structurally — `%` matches no token start, so it lexes to
    // `Token::Unknown`, which the parser surfaces as `Unsupported`. That is the
    // right mapping for an MSBuild error, and it is why deleting the wholesale
    // degrade does not open a hole.
    let tokens = tokenise(source)?;
    let mut parser = Parser {
        tokens: &tokens,
        pos: 0,
        depth: 0,
    };
    let expr = parser.parse_or()?;
    if parser.pos != parser.tokens.len() {
        // Trailing tokens — something we don't model came after a
        // well-formed prefix (`'a' == 'b' garbage`). Don't pretend
        // the prefix's truth value is the whole condition's.
        return Err(());
    }
    Ok(Some(expr))
}

/// Whether MSBuild may throw evaluating a condition ([`Judgement::throws`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Throws {
    /// It throws on no value of the properties the caller is not certain of
    /// (in an item's condition, on none whose substitution forms no item or
    /// metadata expression; see `leaf_may_throw_on_some_value`). An operand
    /// reached on certain values whose boolean we cannot compute
    /// ([`Judgement::unevaluated`]) is no exception: one we do not model is
    /// [`Throws::Maybe`], and only one MSBuild evaluates without throwing (a
    /// string equality whose case folding we do not model, an `Exists` we
    /// cannot ask) leaves this.
    Never,
    /// A throw cannot be ruled out: it may throw on some value of those
    /// properties, though leaves judged one at a time (contradictory guards,
    /// say) may make the throwing operand unreachable on every one.
    Maybe,
    /// It throws whatever they hold.
    Certainly,
}

/// What MSBuild makes of a condition when some of the properties it reads are
/// not certain (`judge`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Judgement {
    /// The condition's value wherever MSBuild does not throw, if one value
    /// holds for every value of the uncertain properties.
    pub value: Option<bool>,
    /// Whether MSBuild may throw evaluating it.
    pub throws: Throws,
    /// Whether an operand MSBuild may reach, on certain values, is one we
    /// cannot evaluate: outside the grammar we model (which MSBuild may
    /// throw on), one MSBuild throws on, or one it returns a boolean we
    /// cannot compute for. A value beside it holds only where that operand
    /// returns.
    pub unevaluated: bool,
}

impl Judgement {
    const fn of(value: Option<bool>, throws: Throws, unevaluated: bool) -> Self {
        Judgement {
            value,
            throws,
            unevaluated,
        }
    }
}

/// Judge a condition as MSBuild evaluates it, without the values of the
/// properties `uncertain` names.
///
/// MSBuild evaluates a condition left to right, and an `And` (`Or`) stops at
/// the first operand that is false (true); `!` evaluates its operand. A leaf (a
/// comparison, a coerced scalar, a function call) that mentions an uncertain
/// property anywhere in its operands has no known value, and may throw when its
/// kind can throw on some value ([`leaf_may_throw_on_some_value`]); every other
/// leaf evaluates exactly as [`evaluate`] does against `props`. One with no
/// boolean there is classified by what MSBuild does instead: it throws
/// ([`Throws::Certainly`]: an ill-typed operand, a property function out of
/// range), it may throw because we do not model it, a property function
/// included ([`Throws::Maybe`]), or it returns a boolean we cannot compute
/// ([`Throws::Never`]). Evaluation goes on past a leaf of unknown value, which may have stopped it, so what comes
/// after one is reached only perhaps: a throw there is [`Throws::Maybe`]. An
/// operand MSBuild never reaches, after one that decides the chain, is not
/// judged at all.
///
/// The value is Kleene's, as MSBuild's short-circuit gives it: an unknown
/// operand before a false one is false (MSBuild stops there), true (it goes
/// on to the false one) or a throw, and none of those disagrees with `false`.
/// Leaves are judged one at a time, so a contradiction spread across leaves
/// (`'$(U)' == 'a' And '$(U)' != 'a'`) is unknown. That only ever declines.
///
/// The walk calls [`decide_without`], [`throws_whatever`] and
/// [`may_throw_on_held`], which answer one question each and walk no further
/// than it needs; this, the whole judgement the first two and `may_throw`
/// are held to, is for tests.
#[cfg(any(test, feature = "test-support"))]
pub fn judge(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    uncertain: &dyn Fn(&str) -> bool,
) -> Judgement {
    let fs = Ctx::new(probes, site);
    match parse_condition(source) {
        Ok(Some(expr)) => judge_expr(&expr, props, fs, uncertain, Walk::Judge),
        Ok(None) => Judgement::of(Some(true), Throws::Never, false),
        Err(reject) => reject.judged(),
    }
}

/// How far [`judge_expr`] walks a condition.
#[derive(Clone, Copy)]
enum Walk<'a> {
    /// To the operand that ends each chain, judging whether MSBuild throws.
    #[cfg(any(test, feature = "test-support"))]
    Judge,
    /// To the first operand we cannot evaluate, past which nothing is
    /// decided ([`Judgement::unevaluated`]): a caller that only decides need
    /// not evaluate, nor probe the file system for, the operands after it.
    Decide,
    /// To the first operand of unknown value: a caller that only asks whether
    /// MSBuild throws whatever the uncertain values hold
    /// ([`throws_whatever`]) settles for no further.
    Certainty,
    /// To the first operand MSBuild may throw on: a caller that only asks
    /// whether it may throw (`may_throw`, [`may_throw_on_held`]) need go no
    /// further. Nor need it evaluate an operand that cannot throw and gates no
    /// later one that can (`later` says whether any operand after this
    /// subtree, in the chains around it, can throw). `on_held`, the names
    /// whose value held MSBuild need not hold at all: a leaf that reads a name
    /// the caller is not certain of is evaluated on the values held, its
    /// failure judged as [`Reject::judged_on_doubted_values`] says where it
    /// rests on such a name, rather than by its kind, and its boolean is none
    /// of MSBuild's.
    Possibility {
        later: bool,
        on_held: Option<&'a dyn Fn(&str) -> bool>,
    },
}

/// Whether MSBuild throws evaluating `source` whatever the properties
/// `uncertain` names hold: a [`Throws::Certainly`] of `judge`'s, found
/// without evaluating (or probing the file system for) any operand past the
/// first of unknown value. It may miss one `judge` finds past such an
/// operand whose chain a later operand decides anyway; it never claims one
/// `judge` does not.
pub fn throws_whatever(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    uncertain: &dyn Fn(&str) -> bool,
) -> bool {
    let fs = Ctx::new(probes, site);
    match parse_condition(source) {
        Ok(Some(expr)) => {
            judge_expr(&expr, props, fs, uncertain, Walk::Certainty).throws == Throws::Certainly
        }
        Ok(None) | Err(Reject::Unmodelled | Reject::Undecided) => false,
        Err(Reject::Throws | Reject::Illegal) => true,
    }
}

/// Whether MSBuild may throw evaluating `source`, the properties `uncertain`
/// names unknown: `judge`'s throw verdict other than [`Throws::Never`],
/// found without evaluating (or probing the file system for) any operand past
/// the first that may throw.
pub fn may_throw(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    uncertain: &dyn Fn(&str) -> bool,
) -> bool {
    let fs = Ctx::new(probes, site);
    may_throw_walked(source, props, fs, uncertain, None)
}

/// Whether MSBuild may throw evaluating `source` on the values `props`
/// holds, where `doubted` names the names whose value held MSBuild need not
/// hold at all: the rejection judgement's Possible site. MSBuild may hold
/// every other value held, so a leaf that throws on those, or that calls what
/// we do not model on them, may throw. A leaf whose failing operand reads a
/// doubted name throws on what it holds only by type
/// ([`Reject::judged_on_doubted_values`], `failing_operand_is_doubted`):
/// whether a function it calls throws on MSBuild's value is the judgement
/// over the values a name may hold (#1009's second stage). A condition wholly
/// outside the grammar we parse claims nothing (#1095).
pub fn may_throw_on_held(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    unsure: &dyn Fn(&str) -> bool,
    doubted: &dyn Fn(&str) -> bool,
) -> bool {
    let fs = Ctx::new(probes, site);
    may_throw_walked(source, props, fs, unsure, Some(doubted))
}

/// `may_throw` or [`may_throw_on_held`], as `on_held` says.
fn may_throw_walked(
    source: &str,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
    on_held: Option<&dyn Fn(&str) -> bool>,
) -> bool {
    match parse_condition(source) {
        Ok(Some(expr)) => {
            judge_expr(
                &expr,
                props,
                fs,
                uncertain,
                Walk::Possibility {
                    later: false,
                    on_held,
                },
            )
            .throws
                != Throws::Never
        }
        Ok(None) | Err(Reject::Undecided) => false,
        // A condition outside the grammar we parse, whole: an item list or
        // metadata reference, an item function, syntax MSBuild takes that we
        // do not. The rejection judgement claims nothing of it, as of a
        // condition legal on the values held: the SDK's own item-pass
        // conditions are of it (`Regex::IsMatch(%(Identity), …)` on a
        // metadatum, `'@(…)' == ''` on a group), MSBuild evaluates them
        // without throwing, and a model of what they expand to is what tells
        // the two apart (#1095).
        Err(Reject::Unmodelled) => on_held.is_none(),
        Err(Reject::Throws | Reject::Illegal) => true,
    }
}

/// `judge` of a parsed condition, walked as `walk` says.
fn judge_expr(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
    walk: Walk<'_>,
) -> Judgement {
    match expr {
        BoolExpr::Not(inner) => {
            let judged = judge_expr(inner, props, fs, uncertain, walk);
            Judgement {
                value: judged.value.map(|value| !value),
                ..judged
            }
        }
        BoolExpr::And(operands) => judge_chain(operands, false, props, fs, uncertain, walk),
        BoolExpr::Or(operands) => judge_chain(operands, true, props, fs, uncertain, walk),
        BoolExpr::True
        | BoolExpr::False
        | BoolExpr::Exists(_)
        | BoolExpr::HasTrailingSlash(_)
        | BoolExpr::MsbuildVersionFunction(_)
        | BoolExpr::CoerceBool(_)
        | BoolExpr::Compare { .. } => judge_leaf_in_every_world(expr, props, fs, uncertain, walk),
    }
}

/// [`judge_leaf`] in every world of MSBuild's startup directory: a leaf whose
/// judgement turns on it has no value, and throws certainly only where it
/// does in every world, perhaps where it may in some. One that asks about
/// more of the startup directory than the walk enumerates is unevaluated, and
/// may throw as its kind can.
fn judge_leaf_in_every_world(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
    walk: Walk<'_>,
) -> Judgement {
    let judged = worlds::in_every_world(fs.start(), |world| {
        judge_leaf(expr, props, fs.in_world(world), uncertain, walk)
    });
    match judged {
        Ok(Worlds::Same(judged)) => judged,
        Ok(split) => {
            let values = split.values();
            let throws = if values.iter().all(|j| j.throws == Throws::Certainly) {
                Throws::Certainly
            } else if values.iter().all(|j| j.throws == Throws::Never) {
                Throws::Never
            } else {
                Throws::Maybe
            };
            Judgement::of(None, throws, values.iter().any(|j| j.unevaluated))
        }
        Err(worlds::TooManySegments) => {
            let throws = if leaf_may_throw_on_some_value(expr) {
                Throws::Maybe
            } else {
                Throws::Never
            };
            Judgement::of(None, throws, true)
        }
    }
}

/// `judge_expr` of the leaf `expr`, in `fs`'s world.
fn judge_leaf(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
    walk: Walk<'_>,
) -> Judgement {
    {
        {
            let mut references = Vec::new();
            leaf_references(expr, &mut references);
            let mut implicit = Vec::new();
            leaf_implicit_references(expr, &mut implicit);
            let explicit_doubt = references.iter().any(|name| uncertain(name));
            let implicit_doubt = implicit.iter().any(|name| uncertain(name));
            let doubted = match walk {
                Walk::Possibility {
                    on_held: Some(doubted),
                    ..
                } => Some(doubted),
                _ => None,
            };
            if doubted.is_none() {
                if explicit_doubt {
                    // A certain value that may complete an item or metadata
                    // expression beside an uncertain one (`$(U)$(V)` with
                    // `V` holding `@(I)`) may make a leaf of any kind throw
                    // in an item's condition. Whether the value is certain
                    // is `uncertain`'s to say, asked first.
                    let completes = references.iter().any(|name| {
                        !uncertain(name)
                            && fs
                                .value(props, name)
                                .is_some_and(|value| value.as_escaped().contains(['@', '%']))
                    });
                    let throws = if leaf_may_throw_on_some_value(expr) || completes {
                        Throws::Maybe
                    } else {
                        Throws::Never
                    };
                    return Judgement::of(None, throws, false);
                }
                // One that reads an uncertain name it does not name, we
                // neither evaluate nor decide past: it may throw, as the walk
                // would have found had the name been named.
                if implicit_doubt {
                    return Judgement::of(None, Throws::Maybe, true);
                }
            }
            // The undefined names are the caller's to report from its own
            // `evaluate`; this evaluation only judges.
            let mut undefined = Vec::new();
            // On held values, the names whose value held MSBuild need not
            // hold at all; a failure resting on one is judged apart.
            let doubted: &dyn Fn(&str) -> bool = doubted.unwrap_or(uncertain);
            let reads_doubted = references.iter().chain(&implicit).any(|name| doubted(name));
            match eval_bool(expr, props, fs, &mut undefined) {
                // On a value held of a name the caller is not certain of, the
                // boolean is none of MSBuild's: what comes after the leaf is
                // reached perhaps, whichever way it went here.
                // And an operand the evaluation skipped on that value (the
                // other side of an equality one side's emptiness decided)
                // MSBuild reaches perhaps: one that fails on what it reads of
                // values MSBuild holds as held may throw.
                Ok(_) if explicit_doubt || implicit_doubt => {
                    let skipped_may_fail = leaf_texts(expr)
                        .is_some_and(|texts| fails_on_held(&texts, props, fs, doubted));
                    let throws = if skipped_may_fail {
                        Throws::Maybe
                    } else {
                        Throws::Never
                    };
                    Judgement::of(None, throws, false)
                }
                Ok(value) => Judgement::of(Some(value), Throws::Never, false),
                Err(reject) if reads_doubted => match doubted_failures(expr, props, fs, doubted) {
                    None => reject.judged(),
                    Some(_) if throws_whatever_they_return(expr, props, fs, doubted) => {
                        Judgement::of(None, Throws::Maybe, true)
                    }
                    Some(_) => reject.judged_on_doubted_values(),
                },
                Err(reject) => reject.judged(),
            }
        }
    }
}

/// What made the leaf `expr` fail on the values `props` holds, where it reads
/// a name `uncertain` names: the property functions that throw or that we do
/// not model, in any operand, each failing on what its own expression reads
/// whatever the rest of the operand reads. `None` where one of them reads no
/// uncertain name (the failure is on values MSBuild may hold); otherwise those
/// that do, none where the leaf failed on its operands' values together (a
/// comparison of their types, an item expression their substitution forms),
/// which rests on every name they read.
fn doubted_failures(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
) -> Option<Vec<String>> {
    let reads_doubted = |raw: &str| {
        let mut names = Vec::new();
        explicit_references(raw, &mut names);
        implicit_references(raw, &mut names);
        names.iter().any(|name| uncertain(name))
    };
    let texts = leaf_texts(expr)?;
    // Each failing expression, and whether its failure reads a doubted name:
    // a throw rests on what it read before it threw, a shape we do not model
    // on everything it names.
    let mut failing: Vec<(String, bool)> = Vec::new();
    for text in &texts {
        let (_, issues) = fs.substitute(text, props);
        failing.extend(issues.into_iter().filter_map(|issue| match issue {
            Issue::Throws {
                expression, reads, ..
            } => {
                let doubted = reads.iter().any(|name| uncertain(name));
                Some((expression, doubted))
            }
            Issue::Unsupported { expression } => {
                let doubted = reads_doubted(&expression);
                Some((expression, doubted))
            }
            _ => None,
        }));
    }
    if failing.is_empty() {
        return texts.iter().any(|text| reads_doubted(text)).then(Vec::new);
    }
    failing.iter().all(|(_, doubted)| *doubted).then(|| {
        failing
            .into_iter()
            .map(|(expression, _)| expression)
            .collect()
    })
}

/// Whether one of `texts`, expanded in full on the values `props` holds,
/// fails on what it reads of no name `doubted` names: a property function
/// that throws, or that we do not model, on values MSBuild may hold as held.
fn fails_on_held(
    texts: &[String],
    props: &PropertyMap,
    fs: Ctx<'_>,
    doubted: &dyn Fn(&str) -> bool,
) -> bool {
    texts.iter().any(|text| {
        let (_, issues) = fs.substitute(text, props);
        issues.into_iter().any(|issue| match issue {
            Issue::Throws { reads, .. } => !reads.iter().any(|name| doubted(name)),
            Issue::Unsupported { expression } => {
                let mut names = Vec::new();
                explicit_references(&expression, &mut names);
                implicit_references(&expression, &mut names);
                !names.iter().any(|name| doubted(name))
            }
            _ => false,
        })
    })
}

/// The texts the leaf `expr` expands, in MSBuild's order; `None` for a leaf
/// that expands none (`true`, `false`).
fn leaf_texts(expr: &BoolExpr) -> Option<Vec<String>> {
    let raw = |scalar: &ScalarExpr| -> String {
        match scalar {
            ScalarExpr::Bare(text) | ScalarExpr::String(text) | ScalarExpr::Property(text) => {
                text.clone()
            }
            ScalarExpr::SystemVersionPart { arg, .. } => arg.clone(),
        }
    };
    match expr {
        BoolExpr::Compare { lhs, rhs, .. } => Some(vec![raw(lhs), raw(rhs)]),
        BoolExpr::CoerceBool(scalar) => Some(vec![raw(scalar)]),
        BoolExpr::Exists(text) | BoolExpr::HasTrailingSlash(text) => Some(vec![text.clone()]),
        BoolExpr::MsbuildVersionFunction(inner) => Some(vec![format!("$({inner})")]),
        BoolExpr::True | BoolExpr::False => None,
        BoolExpr::Not(_) | BoolExpr::And(_) | BoolExpr::Or(_) => Some(Vec::new()),
    }
}

/// The values an expression on an uncertain name is tried as returning, in
/// [`throws_whatever_they_return`]: empty, a word, a number, a version, a
/// boolean either way, a list, and the hyphen a prerelease version joins
/// with (`1$(X)preview`). A sample, not a proof: a throw it shows is a
/// Possible site, never a certain one.
const RETURNED: &[&str] = &["", "x", "1", "1.2", "true", "false", "a;b", "-"];

/// The innermost `$(…)` expressions of `text` that read a name `uncertain`
/// names, by the scanner's extents: those holding no other such expression,
/// so that one in a function's argument leaves the function, and the type it
/// returns, standing. The search descends no deeper than the evaluator does
/// ([`MAX_EXPRESSION_NESTING`]): an expression at that depth is taken whole,
/// which the evaluator declines anyway, so each level costs one scan of the
/// text and the whole search is linear in it.
fn uncertain_spans(text: &str, uncertain: &dyn Fn(&str) -> bool) -> Vec<Range<usize>> {
    let reads = |expression: &str| {
        let mut names = Vec::new();
        explicit_references(expression, &mut names);
        implicit_references(expression, &mut names);
        names.iter().any(|name| uncertain(name))
    };
    // The outermost expressions of `text[span]`, as spans of `text`.
    let outermost = |span: Range<usize>| {
        let mut found = Vec::new();
        let mut at = span.start;
        while let Some(open) = text[at..span.end].find("$(") {
            let start = at + open;
            let Some(close) = find_balanced_property_expression_close(&text[start + 2..span.end])
            else {
                break;
            };
            let end = start + 2 + close + 1;
            found.push(start..end);
            at = end;
        }
        found
    };
    let mut found = Vec::new();
    let mut pending = vec![(0..text.len(), 0)];
    while let Some((span, depth)) = pending.pop() {
        for expression in outermost(span) {
            if !reads(&text[expression.clone()]) {
                continue;
            }
            let inner = expression.start + 2..expression.end - 1;
            if depth + 1 < MAX_EXPRESSION_NESTING
                && outermost(inner.clone())
                    .into_iter()
                    .any(|nested| reads(&text[nested]))
            {
                pending.push((inner, depth + 1));
            } else {
                found.push(expression);
            }
        }
    }
    found.sort_by_key(|span| span.start);
    found
}

/// `text` with each of `spans` (disjoint, in order: those
/// [`uncertain_spans`] finds) replaced by `value`, in one pass.
fn strike(text: &str, spans: &[Range<usize>], value: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut from = 0;
    for span in spans {
        out.push_str(&text[from..span.start]);
        out.push_str(value);
        from = span.end;
    }
    out.push_str(&text[from..]);
    out
}

/// Whether MSBuild throws evaluating `expression`, one `$(…)` of a text that
/// throws on the values `props` holds, whatever the expressions in it that
/// read a name `unheld` names return: with each of them in turn returning each
/// value of [`RETURNED`], it still throws, on what it read of the other names
/// (`VersionLessThan($(A), $(X))` with `A` holding `true`, whatever `X` is).
/// The text's counterpart of [`throws_whatever_they_return`].
pub(crate) fn expression_throws_whatever_they_return(
    expression: &str,
    props: &PropertyMap,
    observer: Option<&Observer>,
    unheld: &dyn Fn(&str) -> bool,
) -> bool {
    let inner = uncertain_spans(expression, unheld);
    if inner.is_empty() {
        return false;
    }
    // It throws whatever they return only where it throws in every world of
    // MSBuild's startup directory.
    RETURNED.iter().all(|value| {
        let struck = strike(expression, &inner, value);
        let thrown = worlds::in_every_world(Start::Unknown, |world| {
            let (_, issues) = substitute_in_world(&struck, props, observer, world);
            issues.iter().any(|issue| {
                matches!(issue, Issue::Throws { reads, .. } if !reads.iter().any(|name| unheld(name)))
            })
        });
        matches!(thrown, Ok(Worlds::Same(true)))
    })
}

/// Whether MSBuild throws evaluating the leaf `expr`, or may, whatever the
/// expressions in it that read a name `uncertain` names return: with each of
/// them in turn returning each value of [`RETURNED`], the leaf has no boolean
/// that MSBuild evaluates to without throwing (`'t$(U[9])'` coerces none,
/// whatever `U[9]` is; `'É' < '$(U.Length)'` orders a word). MSBuild then
/// throws there, or may, or at one of those expressions itself.
fn throws_whatever_they_return(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
) -> bool {
    let Some(texts) = leaf_texts(expr) else {
        return false;
    };
    if texts
        .iter()
        .all(|text| uncertain_spans(text, uncertain).is_empty())
    {
        return false;
    }
    let strike = |raw: &str, value: &str| strike(raw, &uncertain_spans(raw, uncertain), value);
    let scalar = |scalar: &ScalarExpr, value: &str| match scalar {
        ScalarExpr::String(raw) | ScalarExpr::Property(raw) => {
            Some(ScalarExpr::String(strike(raw, value)))
        }
        ScalarExpr::Bare(text) => Some(ScalarExpr::Bare(text.clone())),
        ScalarExpr::SystemVersionPart { .. } => None,
    };
    RETURNED.iter().all(|value| {
        let tried = match expr {
            BoolExpr::Compare { op, lhs, rhs } => match (scalar(lhs, value), scalar(rhs, value)) {
                (Some(lhs), Some(rhs)) => BoolExpr::Compare { op: *op, lhs, rhs },
                _ => return false,
            },
            BoolExpr::CoerceBool(operand) => match scalar(operand, value) {
                Some(operand) => BoolExpr::CoerceBool(operand),
                None => return false,
            },
            BoolExpr::HasTrailingSlash(raw) => BoolExpr::HasTrailingSlash(strike(raw, value)),
            BoolExpr::Exists(raw) => BoolExpr::Exists(strike(raw, value)),
            BoolExpr::MsbuildVersionFunction(inner) => {
                BoolExpr::MsbuildVersionFunction(strike(inner, value))
            }
            _ => return false,
        };
        matches!(
            eval_bool(&tried, props, fs, &mut Vec::new()),
            Err(Reject::Illegal | Reject::Throws | Reject::Unmodelled)
        )
    })
}

/// `judge` of an `And` chain (`absorbing` false) or an `Or` chain
/// (`absorbing` true), operand by operand in MSBuild's order. An operand of
/// unknown value may stop the chain, so every later one is reached only
/// perhaps; one that may throw does not make a later one less certain, since a
/// throw at either rejects the project. An operand holding the absorbing value
/// ends the chain, and so does one that throws whatever the uncertain values
/// hold: past an operand of unknown value, the chain then either stopped with
/// the absorbing value or throws. No operand after the one that ends it is
/// judged, so none is evaluated (an `Exists` probes the file system).
fn judge_chain(
    operands: &[BoolExpr],
    absorbing: bool,
    props: &PropertyMap,
    fs: Ctx<'_>,
    uncertain: &dyn Fn(&str) -> bool,
    walk: Walk<'_>,
) -> Judgement {
    let mut throws = Throws::Never;
    let mut reached_for_certain = true;
    let mut unknown = false;
    let mut unevaluated = false;
    // For the possible-throw walk: the last operand of this chain that can
    // throw, found once.
    let last_throwing = match walk {
        Walk::Possibility { .. } => operands.iter().rposition(may_throw_somewhere),
        _ => None,
    };
    for (index, operand) in operands.iter().enumerate() {
        let walk = match walk {
            Walk::Possibility { later, on_held } => {
                let later = later || last_throwing.is_some_and(|last| last > index);
                if !later && last_throwing != Some(index) {
                    // Nothing from here on can throw, nor be reached by
                    // anything that can.
                    return Judgement::of(None, throws, unevaluated);
                }
                Walk::Possibility { later, on_held }
            }
            other => other,
        };
        let judged = judge_expr(operand, props, fs, uncertain, walk);
        unevaluated |= judged.unevaluated;
        if matches!(walk, Walk::Decide) && unevaluated {
            return Judgement::of(None, throws.max(judged.throws), true);
        }
        if judged.throws == Throws::Certainly {
            return if reached_for_certain {
                Judgement::of(None, Throws::Certainly, unevaluated)
            } else {
                Judgement::of(Some(absorbing), Throws::Maybe, unevaluated)
            };
        }
        throws = throws.max(judged.throws);
        if matches!(walk, Walk::Possibility { .. }) && throws != Throws::Never {
            return Judgement::of(None, throws, unevaluated);
        }
        match judged.value {
            Some(value) if value == absorbing => {
                return Judgement::of(Some(absorbing), throws, unevaluated);
            }
            Some(_) => {}
            None if matches!(walk, Walk::Certainty) => {
                return Judgement::of(None, throws.max(Throws::Maybe), unevaluated);
            }
            None => {
                unknown = true;
                reached_for_certain = false;
            }
        }
    }
    Judgement::of((!unknown).then_some(!absorbing), throws, unevaluated)
}

/// Whether the leaf `expr` may throw on some value of a property it mentions:
/// a relational comparison (on an operand that is neither a number nor a
/// version), a scalar standing as a boolean (outside the boolean vocabulary),
/// `HasTrailingSlash` (on more than one item), a version function (on a value
/// that is no version), and any operand that calls a property function, which
/// may throw on its receiver or arguments. A string comparison of plain
/// references, and `Exists` of them, throw on no value whose substitution
/// forms no item or metadata expression (`@(`, `%(`). In an item's condition
/// MSBuild expands one the substituted text forms, from one value or across
/// adjacent references (`$(U)$(V)` with `@` and `(I)x`), and may throw on it,
/// so there the claim holds only of values that form none.
/// Whether any leaf of `expr` may throw on certain values: one of a kind that
/// can throw on some value ([`leaf_may_throw_on_some_value`]), or one that
/// substitutes a property, whose text may form an item or metadata
/// expression MSBuild expands in an item's condition, and which we do not
/// model ([`Reject::Unmodelled`]).
fn may_throw_somewhere(expr: &BoolExpr) -> bool {
    match expr {
        BoolExpr::Not(inner) => may_throw_somewhere(inner),
        BoolExpr::And(operands) | BoolExpr::Or(operands) => {
            operands.iter().any(may_throw_somewhere)
        }
        // By its kind alone: a relational comparison of literals is counted as
        // one that can throw, though it may not, since some (a path the Unix
        // adjustment rewrites) need the file system to tell. That only costs
        // a probe the verdict might not need.
        leaf => leaf_may_throw_on_some_value(leaf) || leaf_substitutes(leaf),
    }
}

/// Whether an operand of the leaf `expr` substitutes a property (`$(`).
fn leaf_substitutes(expr: &BoolExpr) -> bool {
    let raw = |raw: &str| raw.contains("$(");
    let scalar = |scalar: &ScalarExpr| match scalar {
        ScalarExpr::Bare(_) => false,
        ScalarExpr::String(text)
        | ScalarExpr::Property(text)
        | ScalarExpr::SystemVersionPart { arg: text, .. } => raw(text),
    };
    match expr {
        BoolExpr::True | BoolExpr::False => false,
        BoolExpr::Exists(text)
        | BoolExpr::HasTrailingSlash(text)
        | BoolExpr::MsbuildVersionFunction(text) => raw(text),
        BoolExpr::CoerceBool(value) => scalar(value),
        BoolExpr::Compare { lhs, rhs, .. } => scalar(lhs) || scalar(rhs),
        BoolExpr::Not(_) | BoolExpr::And(_) | BoolExpr::Or(_) => true,
    }
}

fn leaf_may_throw_on_some_value(expr: &BoolExpr) -> bool {
    let scalar = |scalar: &ScalarExpr| match scalar {
        ScalarExpr::Bare(_) => false,
        ScalarExpr::String(raw) | ScalarExpr::Property(raw) => !plain_references_only(raw),
        ScalarExpr::SystemVersionPart { .. } => true,
    };
    match expr {
        BoolExpr::True | BoolExpr::False => false,
        BoolExpr::Compare {
            op: CompareOp::Eq | CompareOp::Neq,
            lhs,
            rhs,
        } => scalar(lhs) || scalar(rhs),
        BoolExpr::Exists(raw) => !plain_references_only(raw),
        // A boolean literal standing alone (`true`, `'on'`) coerces.
        BoolExpr::CoerceBool(ScalarExpr::Bare(word) | ScalarExpr::String(word))
            if !word.contains(['$', '%']) && parse_msbuild_bool(word).is_some() =>
        {
            false
        }
        BoolExpr::Compare { .. }
        | BoolExpr::CoerceBool(_)
        | BoolExpr::HasTrailingSlash(_)
        | BoolExpr::MsbuildVersionFunction(_)
        | BoolExpr::Not(_)
        | BoolExpr::And(_)
        | BoolExpr::Or(_) => true,
    }
}

/// Whether every `$(` in `raw` opens a plain reference, `$(Name)`, whose
/// expansion is the property's value and cannot throw.
pub(crate) fn plain_references_only(raw: &str) -> bool {
    let mut rest = raw;
    while let Some(at) = rest.find("$(") {
        let after = &rest[at + 2..];
        let name_len = after
            .bytes()
            .take_while(|&b| super::properties::is_name_byte(b))
            .count();
        if name_len == 0 || after.as_bytes().get(name_len) != Some(&b')') {
            return false;
        }
        rest = &after[name_len + 1..];
    }
    true
}

/// Whether a condition's outcome depends on properties whose values cannot be
/// trusted. See [`decide_without`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    /// Every value the untrusted properties could hold gives this outcome, or
    /// makes MSBuild reject the condition (a project error, after which the
    /// real evaluation has no value to disagree with).
    Decided(bool),
    /// Some value of an untrusted property may change the outcome.
    Depends,
    /// The condition is outside the grammar, or a part of it the untrusted
    /// properties do not reach is (see [`Outcome::Unsupported`]).
    Unsupported,
}

/// Decide a condition without trusting the properties `untrusted` names: the
/// value of `judge`, which holds wherever MSBuild does not throw. A throw on
/// an untrusted value is a project error, after which the real evaluation has
/// no value to disagree with, so a committed value need not ask whether one is
/// possible; the rejection judgement does ([`Judgement::throws`]). An operand
/// on trusted values we cannot evaluate, which MSBuild may reach, decides
/// nothing ([`Judgement::unevaluated`]): what it does, MSBuild may do instead
/// of returning the value.
pub fn decide_without(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    untrusted: &dyn Fn(&str) -> bool,
) -> Decision {
    let fs = Ctx::new(probes, site);
    let expr = match parse_condition(source) {
        Ok(Some(expr)) => expr,
        Ok(None) => return Decision::Decided(true),
        Err(_) => return Decision::Unsupported,
    };
    match judge_decide(&expr, props, fs, untrusted) {
        Judgement {
            unevaluated: true, ..
        } => Decision::Unsupported,
        Judgement {
            value: Some(value), ..
        } => Decision::Decided(value),
        Judgement { value: None, .. } => Decision::Depends,
    }
}

/// `judge_expr` walked to decide, but where `expr` reads no name `untrusted`
/// names, the whole of it evaluated in every world of MSBuild's startup
/// directory first: a leaf judged alone forgets that another leaf read the
/// same value in the same world (`'$(S)' == 'seg/a' And '$(S)' != 'seg/a'`
/// is false in every world, though each leaf turns on it).
fn judge_decide(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    untrusted: &dyn Fn(&str) -> bool,
) -> Judgement {
    let mut names = Vec::new();
    leaf_references(expr, &mut names);
    leaf_implicit_references(expr, &mut names);
    if !names.iter().any(|name| untrusted(name))
        && let (Ok(Worlds::Same(Ok(value))), _) = eval_in_every_world(expr, props, fs)
    {
        return Judgement::of(Some(value), Throws::Never, false);
    }
    judge_expr(expr, props, fs, untrusted, Walk::Decide)
}

/// Whether `source` is a conjunction (nested conjunctions flattened) each of
/// whose conjuncts is either an `Exists` whose raw argument `is_the_exists`
/// accepts, with `fs` there to answer it, or decided by [`decide_without`]'s
/// evaluation on its own. Stricter than deciding the whole condition: an
/// undecidable conjunct beside a false one is not accepted, though the
/// condition is false whatever the conjunct holds.
pub fn decided_conjunctwise(
    source: &str,
    props: &PropertyMap,
    probes: Option<Probes<'_>>,
    site: Site,
    untrusted: &dyn Fn(&str) -> bool,
    is_the_exists: &dyn Fn(&str) -> bool,
) -> bool {
    let fs = Ctx::new(probes, site);
    let expr = match parse_condition(source) {
        Ok(Some(expr)) => expr,
        Ok(None) => return true,
        Err(_) => return false,
    };
    let mut pending = vec![&expr];
    while let Some(conjunct) = pending.pop() {
        match conjunct {
            BoolExpr::And(operands) => pending.extend(operands),
            BoolExpr::Exists(arg) if fs.probes.is_some() && is_the_exists(arg) => {}
            other => {
                let judged = judge_decide(other, props, fs, untrusted);
                if judged.value.is_none() || judged.unevaluated {
                    return false;
                }
            }
        }
    }
    true
}

/// Whether `source` is a conjunction (nested conjunctions flattened) one of
/// whose conjuncts is an `Exists` whose raw argument `is_the_exists` accepts:
/// the condition is false whenever that `Exists` is.
pub fn requires_exists(source: &str, is_the_exists: &dyn Fn(&str) -> bool) -> bool {
    let Ok(Some(expr)) = parse_condition(source) else {
        return false;
    };
    let mut pending = vec![&expr];
    while let Some(conjunct) = pending.pop() {
        match conjunct {
            BoolExpr::And(operands) => pending.extend(operands),
            BoolExpr::Exists(arg) if is_the_exists(arg) => return true,
            _ => {}
        }
    }
    false
}

/// Whether `scalar` is exactly a `$(MSBuildToolsVersion)` reference, which
/// MSBuild may compare otherwise than its text says. A string that only
/// contains one compares as a string.
fn scalar_reads_toolset_version(scalar: &ScalarExpr) -> bool {
    match scalar {
        ScalarExpr::String(raw) | ScalarExpr::Property(raw) => {
            raw.eq_ignore_ascii_case("$(MSBuildToolsVersion)")
        }
        ScalarExpr::Bare(_) | ScalarExpr::SystemVersionPart { .. } => false,
    }
}

/// The properties `raw` names in `$(…)` references.
fn explicit_references(raw: &str, out: &mut Vec<String>) {
    out.extend(super::properties::property_references(raw).map(str::to_string));
}

/// The property an intrinsic `raw` calls reads with no reference to it: a
/// property expression whose root is `[MSBuild]::AreFeaturesEnabled`, however
/// it is spaced (the property-expression parser allows whitespace within
/// `$( … )` and before the arguments), reads
/// `MSBuildDisableFeaturesFromVersion`.
fn implicit_references(raw: &str, out: &mut Vec<String>) {
    const CALL: &str = "[msbuild]::arefeaturesenabled(";
    // Compared lazily, so a reference that is no such call costs a character.
    let calls = raw.match_indices("$(").any(|(at, _)| {
        let mut squeezed = raw[at + 2..]
            .chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| c.to_ascii_lowercase());
        CALL.chars()
            .all(|expected| squeezed.next() == Some(expected))
    });
    if calls {
        out.push("MSBuildDisableFeaturesFromVersion".to_owned());
    }
}

/// Every property a leaf of the condition tree mentions, in any operand.
fn leaf_references(expr: &BoolExpr, out: &mut Vec<String>) {
    leaf_names(expr, out, explicit_references);
}

/// Every property a leaf of the condition tree reads without naming it
/// ([`implicit_references`]).
fn leaf_implicit_references(expr: &BoolExpr, out: &mut Vec<String>) {
    leaf_names(expr, out, implicit_references);
}

/// The names `read` finds in each operand of a leaf of the condition tree.
fn leaf_names(expr: &BoolExpr, out: &mut Vec<String>, read: fn(&str, &mut Vec<String>)) {
    let scalar = |scalar: &ScalarExpr, out: &mut Vec<String>| match scalar {
        ScalarExpr::Bare(_) => {}
        ScalarExpr::String(raw)
        | ScalarExpr::Property(raw)
        | ScalarExpr::SystemVersionPart { arg: raw, .. } => read(raw, out),
    };
    match expr {
        BoolExpr::True | BoolExpr::False => {}
        BoolExpr::Not(inner) => leaf_names(inner, out, read),
        BoolExpr::And(operands) | BoolExpr::Or(operands) => {
            for operand in operands {
                leaf_names(operand, out, read);
            }
        }
        BoolExpr::Exists(raw)
        | BoolExpr::HasTrailingSlash(raw)
        | BoolExpr::MsbuildVersionFunction(raw) => read(raw, out),
        BoolExpr::CoerceBool(value) => scalar(value, out),
        BoolExpr::Compare { lhs, rhs, .. } => {
            scalar(lhs, out);
            scalar(rhs, out);
        }
    }
}

/// Collect every property reference with at least one *syntactic*
/// occurrence outside a comparison against the empty literal. An
/// operand's references count as empty-compared exactly when the other
/// operand is the (quote-stripped, exactly) empty literal; `Exists(…)`
/// and every other context is non-default. Purely syntactic on purpose —
/// see the call site.
fn refs_outside_empty_comparison(expr: &BoolExpr, out: &mut Vec<String>) {
    match expr {
        BoolExpr::True | BoolExpr::False => {}
        BoolExpr::Not(inner) => refs_outside_empty_comparison(inner, out),
        BoolExpr::And(operands) | BoolExpr::Or(operands) => {
            for operand in operands {
                refs_outside_empty_comparison(operand, out);
            }
        }
        BoolExpr::Exists(raw) | BoolExpr::HasTrailingSlash(raw) => {
            out.extend(super::properties::property_references(raw).map(str::to_string))
        }
        BoolExpr::MsbuildVersionFunction(inner) => {
            out.extend(super::properties::property_references(inner).map(str::to_string))
        }
        // A standalone scalar coerced to bool is a genuine branch decision
        // on its value, never the is-it-set idiom.
        BoolExpr::CoerceBool(scalar) => scalar_refs_outside_empty_comparison(scalar, out),
        BoolExpr::Compare { op, lhs, rhs } => {
            // Only the equality shape (`'$(X)' == ''` / `'$(X)' != ''`) is the
            // is-it-set idiom; a relational comparison against any operand is a
            // genuine branch decision on the value.
            let exempting = matches!(op, CompareOp::Eq | CompareOp::Neq);
            if !(exempting && rhs.is_empty_string_literal()) {
                scalar_refs_outside_empty_comparison(lhs, out);
            }
            if !(exempting && lhs.is_empty_string_literal()) {
                scalar_refs_outside_empty_comparison(rhs, out);
            }
        }
    }
}

fn scalar_refs_outside_empty_comparison(scalar: &ScalarExpr, out: &mut Vec<String>) {
    match scalar {
        ScalarExpr::Bare(_) => {}
        ScalarExpr::String(raw) | ScalarExpr::Property(raw) => {
            out.extend(super::properties::property_references(raw).map(str::to_string))
        }
        // The raw `Parse(...)` argument may hold `$(X)` — including under
        // the `.Split('-')[0]` idiom, whose base property
        // `property_references` extracts like every other
        // taint/reference scan.
        ScalarExpr::SystemVersionPart { arg, .. } => {
            out.extend(super::properties::property_references(arg).map(str::to_string))
        }
    }
}

impl ScalarExpr {
    fn is_empty_string_literal(&self) -> bool {
        matches!(self, ScalarExpr::String(s) if s.is_empty())
    }
}

fn rejected(reject: Reject) -> Eval {
    Eval {
        outcome: match reject {
            Reject::Throws | Reject::Illegal => Outcome::Illegal,
            Reject::Unmodelled | Reject::Undecided => Outcome::Unsupported,
        },
        undefined_properties: Vec::new(),
        undefined_outside_empty_comparison: Vec::new(),
    }
}

// -- Tokeniser --------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum VersionPart {
    Build,
    Revision,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    /// Raw string-literal text (the content between the single quotes,
    /// pre-substitution). We hold the raw form until evaluation so the
    /// PropertyMap available at evaluation time — not tokenisation —
    /// is the one used for `$(...)` expansion.
    String(String),
    Bare(String),
    SystemVersionPart {
        arg: String,
        part: VersionPart,
    },
    /// A bare (unquoted) `$(…)` property expression that isn't one of the
    /// specially-recognised version functions below — a plain reference
    /// (`$(SomeBool)`) or an instance-method call (`$(V.Contains('{'))`).
    /// The raw `$(…)` text is kept until evaluation, when it is expanded
    /// via [`super::properties::substitute_in_world`] and used either as a
    /// comparison operand or coerced to bool (`Condition="$(SomeBool)"`).
    /// An expression the substituter can't evaluate poisons the condition
    /// to [`Outcome::Unsupported`], exactly as it did when this arrived as
    /// [`Token::Unknown`].
    Property(String),
    True,
    False,
    Exists,
    /// MSBuild's `HasTrailingSlash('…')` built-in condition function.
    HasTrailingSlash,
    MsbuildVersionFunction(String),
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    Bang,
    LParen,
    RParen,
    /// An identifier or stray character we don't recognise. Carrying
    /// the literal text would just bloat the token type — the parser
    /// rejects this on sight and returns Unsupported.
    Unknown,
}

/// Returns `Err(())` only for genuinely malformed input — an
/// unterminated string literal, since that's the one case we can't
/// recover from without inventing characters. Every other surprising
/// byte becomes [`Token::Unknown`], which the parser will reject when
/// it can't fit one into the grammar.
fn tokenise(source: &str) -> Result<Vec<Token>, ()> {
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut tokens = Vec::new();
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        match b {
            b'(' => {
                tokens.push(Token::LParen);
                i += 1;
            }
            b')' => {
                tokens.push(Token::RParen);
                i += 1;
            }
            b'=' if bytes.get(i + 1) == Some(&b'=') => {
                tokens.push(Token::Eq);
                i += 2;
            }
            b'!' if bytes.get(i + 1) == Some(&b'=') => {
                tokens.push(Token::Neq);
                i += 2;
            }
            b'<' if bytes.get(i + 1) == Some(&b'=') => {
                tokens.push(Token::Lte);
                i += 2;
            }
            b'>' if bytes.get(i + 1) == Some(&b'=') => {
                tokens.push(Token::Gte);
                i += 2;
            }
            b'<' => {
                tokens.push(Token::Lt);
                i += 1;
            }
            b'>' => {
                tokens.push(Token::Gt);
                i += 1;
            }
            b'!' => {
                tokens.push(Token::Bang);
                i += 1;
            }
            b'\'' => {
                // Walk until the next unescaped quote. MSBuild
                // condition strings have no `\`-escape syntax — the
                // grammar simply doesn't admit a literal `'` inside a
                // string. An unterminated literal is a hard parse
                // error: treating it as Unsupported would silently
                // accept truncated input that happens to look closer
                // to true than to false.
                let start = i + 1;
                let mut j = start;
                while j < bytes.len() && bytes[j] != b'\'' {
                    j += 1;
                }
                if j == bytes.len() {
                    return Err(());
                }
                // Safety: the slice is bounded by the original
                // string's byte indices, and we only advanced through
                // ASCII single quotes (which are full code points by
                // themselves), so `start..j` is on UTF-8 boundaries.
                tokens.push(Token::String(source[start..j].to_string()));
                i = j + 1;
            }
            b'$' if bytes.get(i + 1) == Some(&b'(') => {
                let after = &source[i + 2..];
                let Some(close) = find_balanced_property_expression_close(after) else {
                    tokens.push(Token::Unknown);
                    i += 1;
                    continue;
                };
                if scanner_may_reject_property_expression(after, close) {
                    tokens.push(Token::Unknown);
                    i += 2 + close + 1;
                    continue;
                }
                // MSBuild tolerates whitespace inside `$( … )` for
                // *property-function* forms, but NOT for a simple property
                // reference: `$( Foo )` (and `$(Foo )` / `$( Foo)`) is
                // illegal, where `$(Foo)` is fine (verified against the
                // oracle). Trim for classifying the function forms, but keep
                // the raw spelling to gate the simple-reference case.
                let raw_inner = &after[..close];
                let inner = raw_inner.trim_matches(|c: char| c.is_ascii_whitespace());
                if parse_msbuild_version_function_call(inner).is_some() {
                    tokens.push(Token::MsbuildVersionFunction(inner.to_string()));
                } else if let Some((arg, part)) = parse_system_version_part_token(inner) {
                    tokens.push(Token::SystemVersionPart {
                        arg: arg.to_string(),
                        part,
                    });
                } else if inner.contains('(') || inner.contains('[') {
                    // A property-function form (an instance-method call like
                    // `$(V.Contains('x'))` or a `[Type]::` static call).
                    // Whitespace around it is MSBuild-legal, so classify from
                    // the trimmed text.
                    tokens.push(Token::Property(format!("$({inner})")));
                } else if raw_inner == inner {
                    // A simple property reference with no surrounding
                    // whitespace — the only spelling MSBuild accepts.
                    tokens.push(Token::Property(format!("$({inner})")));
                } else {
                    // A whitespace-padded simple reference (`$( Foo )`):
                    // MSBuild rejects it, so we must not evaluate it as
                    // `$(Foo)` — surface it as unmodelled instead.
                    tokens.push(Token::Unknown);
                }
                i += 2 + close + 1;
            }
            // Bare numerics, mirroring MSBuild's `Scanner.ParseNumeric`
            // greedy lexing: `0x` + hex digits, or optional sign then digits
            // and dots interleaved (so a bare `1.2.3` version is one token).
            // Validity is the comparison layer's problem, exactly as
            // MSBuild leaves it to conversion.
            b if b.is_ascii_digit() || b == b'.' || b == b'+' || b == b'-' => {
                let start = i;
                if b == b'0' && matches!(bytes.get(i + 1), Some(b'x' | b'X')) && i + 2 < bytes.len()
                {
                    i += 2;
                    while i < bytes.len() && bytes[i].is_ascii_hexdigit() {
                        i += 1;
                    }
                } else {
                    if b == b'+' || b == b'-' {
                        i += 1;
                    }
                    while i < bytes.len() && (bytes[i].is_ascii_digit() || bytes[i] == b'.') {
                        i += 1;
                    }
                }
                tokens.push(Token::Bare(source[start..i].to_string()));
            }
            b if is_ident_start(b) => {
                let start = i;
                while i < bytes.len() && is_ident_continue(bytes[i]) {
                    i += 1;
                }
                let word = &source[start..i];
                tokens.push(match_keyword(word));
            }
            _ => {
                // Stray punctuation we don't understand (`<`, `>`,
                // `+`, etc. — operators MSBuild supports but we
                // don't). Emit Unknown so the parser surfaces the
                // condition as Unsupported.
                tokens.push(Token::Unknown);
                i += 1;
            }
        }
    }
    Ok(tokens)
}

/// Most `$(` a reference may nest before [`scanner_may_reject_property_expression`]
/// declines rather than check each (a check per nested reference, each over
/// the rest of the text).
const MAX_NESTED_PROPERTY_EXPRESSIONS: usize = 32;

/// Whether MSBuild's condition scanner may reject the unquoted `$(…)` whose
/// text after the `$(` is `after`, closing at `close`
/// (`Scanner.ScanForPropertyExpressionEnd`). It counts parentheses without
/// regard to quotes, so it must close where we do; and it rejects an
/// expression, or one nested in it, holding whitespace but no character
/// outside an XML name (parentheses aside): `$(A B)` as much as `$( A)`.
///
/// Where unsure, this says it may: a non-ASCII character counts as possible
/// whitespace and a possible name character, and `.` as a name character.
fn scanner_may_reject_property_expression(after: &str, close: usize) -> bool {
    let mut depth = 0usize;
    let raw_close = after.char_indices().find_map(|(idx, ch)| match ch {
        '(' => {
            depth += 1;
            None
        }
        ')' if depth == 0 => Some(idx),
        ')' => {
            depth -= 1;
            None
        }
        _ => None,
    });
    if raw_close != Some(close) {
        return true;
    }
    let ill_formed = |inner: &str| {
        let mut whitespace = false;
        let mut punctuation = false;
        for c in inner.chars() {
            match c {
                '(' | ')' => {}
                c if c.is_whitespace() || !c.is_ascii() => whitespace = true,
                c if c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.') => {}
                _ => punctuation = true,
            }
        }
        whitespace && !punctuation
    };
    let inner = &after[..close];
    if ill_formed(inner) {
        return true;
    }
    // A nested reference holds a `$`, which is punctuation to every reference
    // around it, so each is judged by its own text alone.
    let nested: Vec<usize> = inner.match_indices("$(").map(|(at, _)| at + 2).collect();
    if nested.len() > MAX_NESTED_PROPERTY_EXPRESSIONS {
        return true;
    }
    nested.into_iter().any(|start| {
        let rest = &inner[start..];
        let mut depth = 0usize;
        let end = rest.char_indices().find_map(|(idx, ch)| match ch {
            '(' => {
                depth += 1;
                None
            }
            ')' if depth == 0 => Some(idx),
            ')' => {
                depth -= 1;
                None
            }
            _ => None,
        });
        end.is_none_or(|end| ill_formed(&rest[..end]))
    })
}

fn find_balanced_property_expression_close(input: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut in_string = false;
    for (idx, ch) in input.char_indices() {
        if in_string {
            if ch == '\'' {
                in_string = false;
            }
            continue;
        }
        match ch {
            '\'' => in_string = true,
            '(' => depth += 1,
            ')' => {
                if depth == 0 {
                    return Some(idx);
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

/// MSBuild resolves property-function type and member names
/// case-insensitively (`$([msbuild]::versiongreaterthan(…))` is as valid as
/// the canonical spelling), so every fixed-name match in this module goes
/// through these ASCII-case-folding strip helpers. The needles are all pure
/// ASCII; a non-char-boundary split can therefore only mean "no match".
fn strip_prefix_ignore_ascii_case<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    let (head, tail) = s.split_at_checked(prefix.len())?;
    head.eq_ignore_ascii_case(prefix).then_some(tail)
}

fn strip_suffix_ignore_ascii_case<'a>(s: &'a str, suffix: &str) -> Option<&'a str> {
    let (head, tail) = s.split_at_checked(s.len().checked_sub(suffix.len())?)?;
    tail.eq_ignore_ascii_case(suffix).then_some(head)
}

/// Match a (whitespace-trimmed) `$( … )` interior against the supported
/// `[MSBuild]::Version*` comparison functions, returning the operator and
/// the raw argument list. Whitespace between the member name and its `(`
/// is MSBuild-legal and tolerated. Shared by the tokeniser (support gate)
/// and the evaluator so the two can't drift.
fn parse_msbuild_version_function_call(inner: &str) -> Option<(CompareOp, &str)> {
    let (op, rest) = [
        ("[MSBuild]::VersionGreaterThanOrEquals", CompareOp::Gte),
        ("[MSBuild]::VersionGreaterThan", CompareOp::Gt),
        ("[MSBuild]::VersionLessThanOrEquals", CompareOp::Lte),
        ("[MSBuild]::VersionLessThan", CompareOp::Lt),
        ("[MSBuild]::VersionEquals", CompareOp::Eq),
        ("[MSBuild]::VersionNotEquals", CompareOp::Neq),
    ]
    .into_iter()
    .find_map(|(name, op)| strip_prefix_ignore_ascii_case(inner, name).map(|rest| (op, rest)))?;
    let rest = rest.trim_start_matches(|c: char| c.is_ascii_whitespace());
    let args = rest.strip_prefix('(')?.strip_suffix(')')?;
    Some((op, args))
}

/// Match `[System.Version]::Parse( … ).Build` / `.Revision`, tolerating
/// whitespace at each joint of the call syntax. The stripped-from-the-end
/// `)` is the `Parse` call's own close — parentheses inside the argument
/// (e.g. the `.Split('-')[0]` idiom) sit safely to its left.
fn parse_system_version_part_token(inner: &str) -> Option<(&str, VersionPart)> {
    let rest = strip_prefix_ignore_ascii_case(inner, "[System.Version]::Parse")?;
    let rest = rest.trim_start_matches(|c: char| c.is_ascii_whitespace());
    let rest = rest.strip_prefix('(')?;
    let rest = rest.trim_end_matches(|c: char| c.is_ascii_whitespace());
    let (rest, part) = if let Some(rest) = strip_suffix_ignore_ascii_case(rest, ".Build") {
        (rest, VersionPart::Build)
    } else {
        (
            strip_suffix_ignore_ascii_case(rest, ".Revision")?,
            VersionPart::Revision,
        )
    };
    let rest = rest.trim_end_matches(|c: char| c.is_ascii_whitespace());
    let arg = rest.strip_suffix(')')?;
    Some((arg, part))
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn match_keyword(word: &str) -> Token {
    // MSBuild treats these keywords as case-insensitive: `And` /
    // `AND` / `and` all parse the same. The condition language is
    // OrdinalIgnoreCase end-to-end (mirroring the rest of MSBuild's
    // property-name semantics), so we match here without preserving
    // the input casing.
    if word.eq_ignore_ascii_case("true") {
        Token::True
    } else if word.eq_ignore_ascii_case("false") {
        Token::False
    } else if word.eq_ignore_ascii_case("and") {
        Token::And
    } else if word.eq_ignore_ascii_case("or") {
        Token::Or
    } else if word.eq_ignore_ascii_case("exists") {
        Token::Exists
    } else if word.eq_ignore_ascii_case("hastrailingslash") {
        Token::HasTrailingSlash
    } else {
        // Any other bare word is an unquoted simple-string operand, exactly
        // as MSBuild's scanner treats it: `Release == 'Release'` is true,
        // and a standalone `on` / `yes` / `off` / `no` coerces through the
        // boolean vocabulary (a non-boolean bare word like `maybe` is then a
        // project error → Unsupported). Carrying the text lets the scalar
        // machinery expand/compare it like any other operand. (An unmodelled
        // *function* name still fails: the trailing `(...)` can't fit the
        // grammar after the bare word, so the condition stays Unsupported.)
        Token::Bare(word.to_string())
    }
}

// -- Parser -----------------------------------------------------------

/// Boolean expression AST. We don't store string AST nodes separately
/// — string literals only appear inside [`BoolExpr::Compare`], so
/// embedding the raw text directly keeps the type small and matches
/// the actual grammar.
#[derive(Debug, Clone)]
enum BoolExpr {
    True,
    False,
    Not(Box<BoolExpr>),
    /// A chain `a And b And …`, held flat: MSBuild's connectives are
    /// left-associative and short-circuit left to right, so the chain's value
    /// is its operands' in order. Flat, a chain of any length costs no
    /// recursion to parse, evaluate, scan or drop; only parentheses and `!`
    /// nest (see [`MAX_CONDITION_NESTING`]). Always two operands or more.
    And(Vec<BoolExpr>),
    /// A chain `a Or b Or …`, held flat like [`BoolExpr::And`].
    Or(Vec<BoolExpr>),
    Exists(String),
    /// `HasTrailingSlash('…')`: the raw (quote-stripped, pre-substitution)
    /// argument text.
    HasTrailingSlash(String),
    MsbuildVersionFunction(String),
    /// A scalar standing alone as a boolean, coerced through MSBuild's
    /// boolean vocabulary (`Condition="$(SomeBool)"`, `!$(V.Contains('x'))`,
    /// `Condition="'true'"`).
    CoerceBool(ScalarExpr),
    /// `lhs <op> rhs`. String and version-function operands keep their
    /// pre-substitution raw text; expansion runs at evaluation time so the
    /// latest [`PropertyMap`] is used.
    Compare {
        op: CompareOp,
        lhs: ScalarExpr,
        rhs: ScalarExpr,
    },
}

#[derive(Debug, Clone)]
enum ScalarExpr {
    String(String),
    Bare(String),
    SystemVersionPart {
        arg: String,
        part: VersionPart,
    },
    /// A bare `$(…)` property expression (reference or instance-method
    /// call), expanded via [`super::properties::substitute_in_world`] at evaluation.
    Property(String),
}

#[derive(Debug, Clone, Copy)]
enum CompareOp {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

/// How deeply parentheses and `!` may nest in one condition before it is
/// [`Outcome::Unsupported`].
///
/// Parsing and evaluation recurse once per level, so an unbounded depth
/// overflows the stack, which aborts the process: a project file on disk could
/// take the LSP down. MSBuild's own parser recurses the same way with no limit;
/// it evaluates 10,000 nested parentheses or `!`s and dies of a stack overflow
/// at 100,000 (`msbuild-condition-oracle`, SDK 10.0.401). A decline makes no
/// claim, so any bound is sound. This one is far beyond what a project writes,
/// and an eighth of the depth at which a debug build overflows a 2 MiB thread
/// (about 500 levels, at some 4 KiB of frames each). `tests/deep_nesting.rs`
/// holds the bound to MSBuild on both sides and drives far deeper input on that
/// thread. `And`/`Or` chains do not nest (`BoolExpr::And`), so their length
/// is unbounded.
pub const MAX_CONDITION_NESTING: usize = 64;

struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    /// Parentheses and `!`s enclosing the factor being parsed.
    depth: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&'a Token> {
        self.tokens.get(self.pos)
    }

    fn bump(&mut self) -> Option<&'a Token> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn parse_or(&mut self) -> Result<BoolExpr, ()> {
        let mut operands = vec![self.parse_and()?];
        while matches!(self.peek(), Some(Token::Or)) {
            self.bump();
            operands.push(self.parse_and()?);
        }
        Ok(chain(operands, BoolExpr::Or))
    }

    fn parse_and(&mut self) -> Result<BoolExpr, ()> {
        let mut operands = vec![self.parse_primary_bool()?];
        while matches!(self.peek(), Some(Token::And)) {
            self.bump();
            operands.push(self.parse_primary_bool()?);
        }
        Ok(chain(operands, BoolExpr::And))
    }

    /// Run `parse` one nesting level down, declining at
    /// [`MAX_CONDITION_NESTING`].
    fn nested(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<BoolExpr, ()>,
    ) -> Result<BoolExpr, ()> {
        if self.depth >= MAX_CONDITION_NESTING {
            return Err(());
        }
        self.depth += 1;
        let parsed = parse(self);
        self.depth -= 1;
        parsed
    }

    /// A boolean-typed primary at comparison level: a bool factor
    /// (parenthesised sub-expression, `true`/`false`, a function, or a
    /// scalar coerced to bool) optionally followed by a comparison operator
    /// and a right-hand scalar (`'a' == 'b'`, `1 < 2`,
    /// `System.Version.Parse(...).Build >= 0`, `$(P) == 'x'`). A leading
    /// scalar with no operator is coerced to bool (`Condition="$(SomeBool)"`).
    fn parse_primary_bool(&mut self) -> Result<BoolExpr, ()> {
        // A leading scalar may be the left of a comparison OR stand alone
        // as a coerced boolean. Only scalars can be a comparison LHS, so
        // handle them here; every other factor delegates below.
        if self.peek().is_some_and(Token::is_scalar_start) {
            let lhs = self.parse_scalar()?;
            return match self.peek_compare_op() {
                Some(op) => {
                    self.bump();
                    let rhs = self.parse_scalar()?;
                    Ok(BoolExpr::Compare { op, lhs, rhs })
                }
                None => Ok(BoolExpr::CoerceBool(lhs)),
            };
        }
        self.parse_bool_factor()
    }

    /// A boolean *factor*: everything a comparison operand cannot follow.
    /// Crucially, a leading scalar here is coerced to bool WITHOUT
    /// consuming a trailing comparison operator — so `!` (which parses a
    /// factor) binds tighter than comparison, matching MSBuild: `!'a' == 'b'`
    /// is `(!'a') == 'b'` (a project error → any trailing operator is left
    /// unconsumed and the top level reports Unsupported), never
    /// `!('a' == 'b')`.
    fn parse_bool_factor(&mut self) -> Result<BoolExpr, ()> {
        match self.peek() {
            Some(Token::Bang) => {
                self.bump();
                let operand = self.nested(Self::parse_bool_factor)?;
                Ok(BoolExpr::Not(Box::new(operand)))
            }
            Some(Token::LParen) => {
                self.bump();
                let inner = self.nested(Self::parse_or)?;
                match self.bump() {
                    Some(Token::RParen) => Ok(inner),
                    _ => Err(()),
                }
            }
            Some(Token::True) => {
                self.bump();
                Ok(BoolExpr::True)
            }
            Some(Token::False) => {
                self.bump();
                Ok(BoolExpr::False)
            }
            Some(Token::Exists) => {
                self.bump();
                Ok(BoolExpr::Exists(self.parse_single_string_argument()?))
            }
            Some(Token::HasTrailingSlash) => {
                self.bump();
                Ok(BoolExpr::HasTrailingSlash(
                    self.parse_single_string_argument()?,
                ))
            }
            Some(Token::MsbuildVersionFunction(inner)) => {
                let inner = inner.clone();
                self.bump();
                Ok(BoolExpr::MsbuildVersionFunction(inner))
            }
            Some(token) if token.is_scalar_start() => {
                Ok(BoolExpr::CoerceBool(self.parse_scalar()?))
            }
            _ => Err(()),
        }
    }

    /// Parse the single argument shared by `Exists` and `HasTrailingSlash`:
    /// either a quoted literal `( '…' )` or a bare property expression
    /// `( $(…) )`. Returns the raw (quote-stripped) text for the caller to
    /// expand.
    ///
    /// The unquoted spelling is the only one available to an argument that
    /// itself contains quotes — `Exists($([MSBuild]::GetPathOfFileAbove('x',
    /// '$(D)')))`, the `Directory.Build.props` chaining idiom — since the
    /// literal form has no escape for a nested delimiter. MSBuild accepts both
    /// (oracle-pinned 2026-08-04: `Exists($(F))`, `HasTrailingSlash($(D))` and
    /// the nested-function form all evaluate).
    ///
    /// Anything *around* the reference is still rejected, matching MSBuild:
    /// `Exists($(D)../x.props)` is MSB4092 ("An unexpected token `..`"), and the
    /// trailing text tokenises past the closing paren this expects.
    fn parse_single_string_argument(&mut self) -> Result<String, ()> {
        match self.bump() {
            Some(Token::LParen) => {}
            _ => return Err(()),
        }
        let arg = match self.bump() {
            Some(Token::String(s)) => s.clone(),
            Some(Token::Property(raw)) => raw.clone(),
            _ => return Err(()),
        };
        match self.bump() {
            Some(Token::RParen) => Ok(arg),
            _ => Err(()),
        }
    }

    fn peek_compare_op(&self) -> Option<CompareOp> {
        match self.peek()? {
            Token::Eq => Some(CompareOp::Eq),
            Token::Neq => Some(CompareOp::Neq),
            Token::Lt => Some(CompareOp::Lt),
            Token::Lte => Some(CompareOp::Lte),
            Token::Gt => Some(CompareOp::Gt),
            Token::Gte => Some(CompareOp::Gte),
            _ => None,
        }
    }

    fn parse_scalar(&mut self) -> Result<ScalarExpr, ()> {
        match self.bump() {
            Some(Token::String(s)) => Ok(ScalarExpr::String(s.clone())),
            Some(Token::Bare(s)) => Ok(ScalarExpr::Bare(s.clone())),
            Some(Token::SystemVersionPart { arg, part }) => Ok(ScalarExpr::SystemVersionPart {
                arg: arg.clone(),
                part: part.clone(),
            }),
            Some(Token::Property(raw)) => Ok(ScalarExpr::Property(raw.clone())),
            // `true`/`false` double as unquoted string operands in a
            // comparison (`$(X) == false`), where MSBuild compares them
            // through the boolean vocabulary. We normalise to the canonical
            // lowercase spelling since the token discards the input casing.
            Some(Token::True) => Ok(ScalarExpr::Bare("true".to_string())),
            Some(Token::False) => Ok(ScalarExpr::Bare("false".to_string())),
            _ => Err(()),
        }
    }
}

/// One operand stands alone; two or more form a flat chain.
fn chain(mut operands: Vec<BoolExpr>, connective: fn(Vec<BoolExpr>) -> BoolExpr) -> BoolExpr {
    if operands.len() == 1 {
        operands.pop().expect("one operand")
    } else {
        connective(operands)
    }
}

impl Token {
    fn is_scalar_start(&self) -> bool {
        matches!(
            self,
            Token::String(_)
                | Token::Bare(_)
                | Token::SystemVersionPart { .. }
                | Token::Property(_)
                // `true`/`false` can begin a comparison (`false == $(X)`) as
                // well as stand alone; the standalone case coerces the same
                // way `BoolExpr::True`/`False` would.
                | Token::True
                | Token::False
        )
    }
}

// -- Evaluator --------------------------------------------------------

fn eval_bool(
    expr: &BoolExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<bool, Reject> {
    match expr {
        BoolExpr::True => Ok(true),
        BoolExpr::False => Ok(false),
        BoolExpr::Not(expr) => Ok(!eval_bool(expr, props, fs, undefined)?),
        // Short-circuit on the resolved truth value, matching MSBuild's
        // left-to-right evaluation order. This is only observable when
        // the right-hand side encounters an Unsupported expression
        // inside a string literal — the *parser* already rejected
        // anything else (a bare `HasTrailingSlash(...)` token sequence
        // doesn't fit the grammar and short-circuits the whole
        // condition to Unsupported well before evaluation). Where it
        // does fire, propagating Err only when the resolving side
        // can't be computed preserves the "never produce wrong output"
        // promise without overly-aggressive Unsupported reporting.
        //
        // The short-circuit also means we don't collect undefined-property
        // names from the skipped side. MSBuild itself never sees those
        // refs when the result is decided by the first side, so reporting
        // them as "we couldn't resolve" would be over-eager.
        BoolExpr::And(operands) => {
            for operand in operands {
                if !eval_bool(operand, props, fs, undefined)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        BoolExpr::Or(operands) => {
            for operand in operands {
                if eval_bool(operand, props, fs, undefined)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        BoolExpr::Exists(raw) => {
            // MSBuild expands the argument, which may throw, and then asks
            // the file system, which does not (`FileOrDirectoryExistsNoThrow`).
            let Some(probes) = fs.probes else {
                expand_for_condition(raw, props, fs, undefined)?;
                return Err(Reject::Undecided);
            };
            // A `\` written in the argument is a `/` before it is expanded.
            let raw = &path_fixup::fix_file_path(raw);
            let value = expand_for_condition(raw, props, fs, undefined)?;
            // MSBuild expands the argument into an item list and asks about
            // every entry: true when each exists, false for an empty list
            // (`ExpandArgumentAsFileList`). The split and the trim happen in
            // the escaped domain, as for `HasTrailingSlash` below: an escaped
            // `%3b` is filename data, not a separator, and an escaped `%20` is
            // data, not padding. Oracle-pinned: `Exists('a;b')` is true with
            // files `a` and `b` and none named `a;b`, `Exists('a%3bb')` asks
            // about `a;b`, and `Exists('path%20')` about `path `.
            let entries: Vec<Escaped> = value.split_list().collect();
            // A `\` written as `%5c` decodes after MSBuild has asked whether
            // the entry is rooted, and acts as a separator only after that.
            // Oracle-pinned: `Exists('%5c<an existing absolute path>')` is
            // false, while `Exists('d%5cg')` is true with `d/g` and
            // `Exists('d/up%5c..%5cg')` collapses the `..` as text. Decline
            // rather than model that order.
            if entries
                .iter()
                .any(|entry| entry.as_escaped().to_ascii_lowercase().contains("%5c"))
            {
                return Err(Reject::Undecided);
            }
            Ok(!entries.is_empty()
                && entries
                    .iter()
                    .all(|entry| (probes.exists)(&entry.unescape())))
        }
        BoolExpr::HasTrailingSlash(raw) => {
            let raw = &path_fixup::fix_file_path(raw);
            let value = expand_for_condition(raw, props, fs, undefined)
                .map_err(Reject::read_by_throwing_leaf)?;
            // MSBuild expands the argument into an item list: each entry is
            // whitespace-trimmed and empty entries are dropped
            // (`'a/;'` and `';/'` are the single item `a/` / `/`). A single
            // remaining item is checked for a trailing `/` or `\`; more than
            // one is a project error (`HasTrailingSlash('a;b')`); none (an
            // empty or all-separator argument) has no trailing slash. The trim
            // is .NET's `Trim`, which outside ASCII we do not claim to match.
            //
            // The split and the trim happen **in the escaped domain**, and each
            // entry decodes at the leaf — the same order the item pass uses, and
            // for the same reason: an escaped `%3b` is data, not a separator, and
            // an escaped `%20` is data, not padding. Both pinned against
            // `dotnet msbuild`: `HasTrailingSlash('foo%2f')` is true (it decodes
            // to `foo/`), while `HasTrailingSlash('foo/%20')` is **false** — the
            // decoded value is `foo/ `, whose last character is a space. Decoding
            // first and trimming after would commit `true` there.
            let mut items = value.split_list().map(|entry| entry.unescape());
            let item = items.next();
            if items.next().is_some() {
                return Err(if value.as_escaped().is_ascii() {
                    Reject::Illegal
                } else {
                    Reject::Unmodelled
                });
            }
            Ok(item.is_some_and(|s: String| s.ends_with('/') || s.ends_with('\\')))
        }
        BoolExpr::MsbuildVersionFunction(inner) => {
            eval_msbuild_version_function(inner, props, fs, undefined)
                .map_err(Reject::read_by_throwing_leaf)
        }
        BoolExpr::CoerceBool(scalar) => {
            let value = match expand_scalar_for_condition(scalar, props, fs, undefined) {
                // A boolean we do not compute coerces without throwing.
                Err(Reject::Undecided) if lone_boolean(scalar, props, fs) => {
                    return Err(Reject::Undecided);
                }
                other => other.map_err(Reject::read_by_throwing_leaf)?,
            };
            // A standalone scalar is coerced through MSBuild's boolean
            // vocabulary; a value outside it (`1`, `foo`, an unset
            // property's "") is a project error. The vocabulary matches
            // ignoring case ordinally, which outside ASCII folds letters
            // `eq_ignore_ascii_case` does not (`ſ` is an `s`).
            parse_msbuild_bool(&value).ok_or(if value.is_ascii() {
                Reject::Illegal
            } else {
                Reject::Unmodelled
            })
        }
        BoolExpr::Compare { op, lhs, rhs } => {
            // MSBuild compares a `$(MSBuildToolsVersion)` reference, which
            // expands to `Current`, as Visual Studio's version beside a number
            // or version (`'$(MSBuildToolsVersion)' != '18'` is false on SDK
            // 10.0.401), though a literal `Current` compares as a string. Not
            // modelled for equality; the relational operators decline any
            // `Current` (`certainly_neither_number_nor_version`).
            let (lhs_toolset, rhs_toolset) = (
                scalar_reads_toolset_version(lhs),
                scalar_reads_toolset_version(rhs),
            );
            // Equality throws on no value; an order on many.
            let relational = !matches!(op, CompareOp::Eq | CompareOp::Neq);
            let operand = |reject: Reject, scalar: &ScalarExpr| {
                if !relational {
                    reject
                } else if reject == Reject::Undecided && lone_boolean(scalar, props, fs) {
                    // A boolean we do not compute is still no number nor
                    // version: an order on it throws.
                    Reject::Illegal
                } else {
                    reject.read_by_throwing_leaf()
                }
            };
            let (lhs_scalar, rhs_scalar) = (lhs, rhs);
            // Equality asks each side, left then right, whether it is empty
            // first, expanding only a side that is one reference whole
            // (`MultipleComparisonExpressionNode`, `EvaluatesToEmpty`); where
            // one is, emptiness decides it and nothing more is expanded,
            // unless the condition is the property pass's, whose design-time
            // evaluation then expands both sides in full all the same for its
            // table of conditioned properties ([`Site`]). An item's condition
            // whose side's emptiness is unknown may be one where that side is
            // empty, and a throw expanding the other one MSBuild never reaches.
            let (lhs_probe, rhs_probe, emptiness_unknown) = if relational {
                (None, None, false)
            } else {
                let lhs_probe = probe_emptiness(lhs_scalar, props, fs, undefined);
                if let Probed::Expanded(Err(reject @ (Reject::Throws | Reject::Illegal))) =
                    lhs_probe
                {
                    return Err(reject);
                }
                let rhs_probe = probe_emptiness(rhs_scalar, props, fs, undefined);
                let mut emptiness_unknown = false;
                match (lhs_probe.emptiness(), rhs_probe.emptiness()) {
                    (Ok(lhs_empty), Ok(rhs_empty)) if lhs_empty || rhs_empty => {
                        let decided = matches!(op, CompareOp::Eq) == (lhs_empty == rhs_empty);
                        if fs.site != Site::PropertyPass {
                            return Ok(decided);
                        }
                        // Right, then left, as `UpdateConditionedProperties`
                        // expands them; each side expanded once.
                        let worst = [(rhs_scalar, &rhs_probe), (lhs_scalar, &lhs_probe)]
                            .into_iter()
                            .filter_map(|(scalar, probe)| match probe {
                                Probed::Expanded(result) => result.as_ref().err().copied(),
                                Probed::NotExpanded => {
                                    expand_scalar_for_condition(scalar, props, fs, undefined).err()
                                }
                            })
                            .max();
                        return match worst {
                            Some(
                                reject @ (Reject::Throws | Reject::Illegal | Reject::Unmodelled),
                            ) => Err(reject),
                            _ => Ok(decided),
                        };
                    }
                    (Ok(true), Err(reject)) | (Err(reject), Ok(true)) => return Err(reject),
                    (_, Err(reject @ (Reject::Throws | Reject::Illegal))) => return Err(reject),
                    (Err(_), _) | (_, Err(_)) => {
                        emptiness_unknown = fs.site != Site::PropertyPass;
                    }
                    _ => {}
                }
                (Some(lhs_probe), Some(rhs_probe), emptiness_unknown)
            };
            let reached_perhaps = |reject: Reject| match reject {
                Reject::Throws | Reject::Illegal if emptiness_unknown => Reject::Unmodelled,
                other => other,
            };
            // MSBuild expands both operands before it compares them, so an
            // operand whose value we do not know does not keep it from the
            // other, which may throw: the worse of the two stands. One that
            // throws ends it. A side the emptiness question expanded is not
            // expanded again.
            let mut expand = |scalar: &ScalarExpr, probe: Option<Probed>| match probe {
                Some(Probed::Expanded(result)) => result,
                _ => expand_scalar_for_condition(scalar, props, fs, undefined),
            };
            let lhs = expand(lhs_scalar, lhs_probe)
                .map_err(|reject| reached_perhaps(operand(reject, lhs_scalar)));
            let lhs = match lhs {
                Err(reject @ (Reject::Throws | Reject::Illegal)) => return Err(reject),
                other => other,
            };
            let rhs = expand(rhs_scalar, rhs_probe)
                .map_err(|reject| reached_perhaps(operand(reject, rhs_scalar)));
            let (lhs, rhs) = match (lhs, rhs) {
                (Ok(lhs), Ok(rhs)) => (lhs, rhs),
                (Err(lhs), Err(rhs)) => return Err(lhs.max(rhs)),
                (Err(reject), Ok(_)) | (Ok(_), Err(reject)) => return Err(reject),
            };
            // As equality reads a number, or may (it compares no versions).
            let numeric = |value: &str| !matches!(equality_number(value), Ok(None));
            if matches!(op, CompareOp::Eq | CompareOp::Neq)
                && ((lhs_toolset && numeric(&rhs)) || (rhs_toolset && numeric(&lhs)))
            {
                return Err(Reject::Undecided);
            }
            if relational {
                let ordering = compare_relational_values(&lhs, &rhs).map_err(|()| {
                    // MSBuild throws when either side is neither a number nor
                    // a version, whatever the other side holds.
                    if certainly_neither_number_nor_version(&lhs)
                        || certainly_neither_number_nor_version(&rhs)
                    {
                        Reject::Illegal
                    } else {
                        Reject::Unmodelled
                    }
                })?;
                return Ok(match op {
                    CompareOp::Lt => ordering.is_lt(),
                    CompareOp::Lte => !ordering.is_gt(),
                    CompareOp::Gt => ordering.is_gt(),
                    CompareOp::Gte => !ordering.is_lt(),
                    CompareOp::Eq | CompareOp::Neq => unreachable!(),
                });
            }
            // Equality throws on no value.
            let equal = compare_equality_values(&lhs, &rhs).map_err(|()| Reject::Undecided)?;
            Ok(match op {
                CompareOp::Eq => equal,
                CompareOp::Neq => !equal,
                CompareOp::Lt | CompareOp::Lte | CompareOp::Gt | CompareOp::Gte => unreachable!(),
            })
        }
    }
}

/// What MSBuild's equality made of an operand asking whether it is empty
/// ([`probe_emptiness`]).
enum Probed {
    /// It expanded the operand, which was empty where the expansion is.
    Expanded(Result<String, Reject>),
    /// It took the operand as non-empty without expanding it.
    NotExpanded,
}

impl Probed {
    /// Whether the operand is empty; the expansion's failure where that is
    /// what decides it.
    fn emptiness(&self) -> Result<bool, Reject> {
        match self {
            Probed::Expanded(result) => result.as_ref().map(String::is_empty).map_err(|r| *r),
            Probed::NotExpanded => Ok(false),
        }
    }
}

/// Whether MSBuild's equality takes the operand `scalar` as empty
/// (`StringExpressionNode.EvaluatesToEmpty`), expanding it only as MSBuild
/// does: text it has nothing to expand in is empty when it is, text of one or
/// two characters is not, and neither is text that is not one reference whole
/// (`$(`, `%(` or `@(` first, `)` last), which it does not expand at all
/// (`'a$(P[9])' == ''` is false in a build, and throws on nothing; probed,
/// `msbuild-condition-oracle`, SDK 10.0.401). Any other it expands, its
/// properties in full, as a comparison would.
fn probe_emptiness(
    scalar: &ScalarExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Probed {
    let raw = match scalar {
        ScalarExpr::String(raw) | ScalarExpr::Property(raw)
            if raw.contains("$(") || raw.contains('%') =>
        {
            raw.as_str()
        }
        _ => {
            return Probed::Expanded(expand_scalar_for_condition(scalar, props, fs, undefined));
        }
    };
    let bytes = raw.as_bytes();
    if bytes.len() <= 2
        || bytes[1] != b'('
        || !matches!(bytes[0], b'$' | b'%' | b'@')
        || !raw.ends_with(')')
    {
        return Probed::NotExpanded;
    }
    Probed::Expanded(expand_scalar_for_condition(scalar, props, fs, undefined))
}

/// Whether the operand `scalar` is one `$(…)` whose only issue is a boolean
/// we do not compute ([`Issue::ReturnsBoolean`]), so that coercing it cannot
/// throw.
fn lone_boolean(scalar: &ScalarExpr, props: &PropertyMap, fs: Ctx<'_>) -> bool {
    let (ScalarExpr::String(raw) | ScalarExpr::Property(raw)) = scalar else {
        return false;
    };
    // The operand is that one expression, with nothing beside it: text
    // around it would make the boolean a word (`'x$(…)'` is `xFalse`).
    let (_, issues) = fs.substitute(raw, props);
    matches!(issues.as_slice(), [Issue::ReturnsBoolean { expression }] if expression == raw)
}

fn expand_scalar_for_condition(
    scalar: &ScalarExpr,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<String, Reject> {
    match scalar {
        // MSBuild expands a quoted operand only when its scanner saw something
        // to expand in it (`Scanner.ParseQuotedString`: a `$(`, `@(`, `%(` or
        // any `%`). Any other is compared as written, so its `\` never meets
        // the Unix path adjustment an expansion applies.
        ScalarExpr::String(raw) if !raw.contains("$(") && !raw.contains('%') => Ok(raw.clone()),
        ScalarExpr::String(raw) => expand_operand(raw, props, fs, undefined),
        ScalarExpr::Bare(raw) => Ok(raw.clone()),
        ScalarExpr::Property(raw) => expand_operand(raw, props, fs, undefined),
        ScalarExpr::SystemVersionPart { arg, part } => {
            // `Parse` throws on what it cannot read, so an argument whose value
            // we do not know (a boolean we do not compute) may throw here.
            let version = expand_system_version_parse_arg(arg, props, fs, undefined)
                .map_err(|reject| reject.max(Reject::Unmodelled))?;
            let version = parse_system_version(&version).map_err(Reject::from)?;
            let idx = match part {
                VersionPart::Build => 2,
                VersionPart::Revision => 3,
            };
            Ok(version[idx].to_string())
        }
    }
}

/// The `$('$(X.Split('-')[0])')` idiom inside a `[System.Version]::Parse`
/// argument: returns the property name when the (trimmed, quote-stripped)
/// argument is exactly a `$(...)` reference carrying that `.Split` call.
/// The taint-side counterpart lives in
/// [`super::properties::property_references`], which extracts the base
/// property of any `.Split` call so uncertainty scans see what this resolves.
fn split_dash_zero_property(raw: &str) -> Option<&str> {
    let raw = raw.trim();
    let raw = raw
        .strip_prefix('\'')
        .and_then(|s| s.strip_suffix('\''))
        .unwrap_or(raw);
    let inner = raw.strip_prefix("$(")?.strip_suffix(')')?;
    strip_suffix_ignore_ascii_case(inner, ".Split('-')[0]")
}

fn expand_system_version_parse_arg(
    raw: &str,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<String, Reject> {
    if let Some(property) = split_dash_zero_property(raw) {
        // A condition's trust is the whole-tree scan, not its operands' (see
        // [`expand_for_condition`]).
        if let Some(value) = fs.value(props, property) {
            // A condition operand is a point of use: MSBuild compares the
            // *unescaped* value, the one this world holds.
            let value = value.unescape();
            return Ok(value.split('-').next().unwrap_or("").to_string());
        }
        undefined.push(property.to_string());
        return Ok(String::new());
    }
    let raw = raw.trim();
    let raw = raw
        .strip_prefix('\'')
        .and_then(|s| s.strip_suffix('\''))
        .unwrap_or(raw);
    expand_operand(raw, props, fs, undefined)
}

fn eval_msbuild_version_function(
    inner: &str,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<bool, Reject> {
    // MSBuild expands the call as it expands any property function, and
    // reads the boolean it renders: the expression evaluator reads the
    // arguments (any of the three string delimiters) and classifies a
    // failure as MSBuild's throw or an unmodelled shape.
    let value = expand_operand(&format!("$({inner})"), props, fs, undefined)?;
    parse_msbuild_bool(&value).ok_or(Reject::Unmodelled)
}

/// Relational comparison, mirroring MSBuild's
/// `NumericComparisonExpressionNode.BoolEvaluate` dispatch exactly: both
/// sides numeric → compare as doubles; else both sides `System.Version` →
/// compare as versions (missing components count as `-1`, so `2.0 < 2.0.0`);
/// else one of each → the mixed major-only rule
/// ([`compare_version_and_number`]). A side that is neither is a project
/// error in MSBuild — Unsupported here.
fn compare_relational_values(lhs: &str, rhs: &str) -> Result<std::cmp::Ordering, ()> {
    let lhs_number = parse_msbuild_number(lhs);
    let rhs_number = parse_msbuild_number(rhs);
    if let (Some(lhs), Some(rhs)) = (lhs_number, rhs_number) {
        // Both finite by construction, so the comparison is total.
        return lhs.partial_cmp(&rhs).ok_or(());
    }
    match (parse_system_version(lhs), parse_system_version(rhs)) {
        (Ok(lhs), Ok(rhs)) => Ok(lhs.cmp(&rhs)),
        (Ok(lhs), Err(())) => rhs_number
            .map(|number| compare_version_and_number(&lhs, number))
            .ok_or(()),
        (Err(()), Ok(rhs)) => lhs_number
            .map(|number| compare_version_and_number(&rhs, number).reverse())
            .ok_or(()),
        (Err(()), Err(())) => Err(()),
    }
}

/// Whether MSBuild's relational operators certainly read `value` as neither a
/// number nor a version, so that comparing it throws
/// (`NumericComparisonExpressionNode`: MSB4086).
///
/// The one operand MSBuild reads otherwise is `$(MSBuildToolsVersion)`
/// expanding to `Current`, which it takes as Visual Studio's version.
fn certainly_neither_number_nor_version(value: &str) -> bool {
    value != "Current" && certainly_not_a_number(value) && certainly_not_a_version(value)
}

/// Whether `ConversionUtilities.TryConvertDecimalOrHexToDouble` certainly
/// fails on `value`: [`parse_msbuild_number`] fails, and `value` is free of
/// what `double.TryParse` takes beyond that grammar. It takes trailing NULs
/// (`'1%00' < 2` is true), the NaN and infinity symbols in any case and sign
/// (`nan < 1` is false; an infinity is then refused as a number), and it
/// classifies characters outside ASCII by tables not modelled here.
fn certainly_not_a_number(value: &str) -> bool {
    if !value.is_ascii() || value.contains('\0') {
        return false;
    }
    let lower = value.to_ascii_lowercase();
    !lower.contains("nan") && !lower.contains("infinity") && parse_msbuild_number(value).is_none()
}

/// Whether .NET's `Version.TryParse` certainly fails on `value`. For ASCII
/// text without NULs this is exact: two to four `.`-separated components,
/// each an `int.TryParse(NumberStyles.Integer)` (ASCII whitespace trimmed, one
/// optional sign, ASCII digits, within `int`) that is not negative, so `-0`
/// is a component and `-1` is not (`'1.-0' < 2` is true, `'1.-1' < 2` an
/// error).
fn certainly_not_a_version(value: &str) -> bool {
    if !value.is_ascii() || value.contains('\0') {
        return false;
    }
    let parts: Vec<&str> = value.split('.').collect();
    let component = |part: &str| {
        let part = part.trim_matches(|c: char| matches!(c, '\t'..='\r' | ' '));
        let (negative, digits) = match part.as_bytes().first() {
            Some(b'-') => (true, &part[1..]),
            Some(b'+') => (false, &part[1..]),
            _ => (false, part),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        }
        let significant = digits.trim_start_matches('0');
        if negative {
            significant.is_empty()
        } else {
            significant.len() < 10 || (significant.len() == 10 && significant <= "2147483647")
        }
    };
    !((2..=4).contains(&parts.len()) && parts.into_iter().all(component))
}

/// MSBuild's mixed number/version comparison (the `Compare(Version, double)`
/// overloads in e.g. `LessThanExpressionNode`): only the version's *major*
/// component is compared against the number, and when they tie the version
/// counts as strictly greater — "Version treats the objects with more dots
/// as larger" (`6.0.0.0 > 6` is true). Returns the ordering of the version
/// relative to the number.
fn compare_version_and_number(version: &[i64; 4], number: f64) -> std::cmp::Ordering {
    let major = version[0] as f64;
    if major < number {
        std::cmp::Ordering::Less
    } else {
        // Equal majors: the version side wins outright.
        std::cmp::Ordering::Greater
    }
}

/// Equality, mirroring MSBuild's `MultipleComparisonNode.BoolEvaluate`: an
/// empty side short-circuits to emptiness comparison, then numeric (double)
/// equality, then MSBuild boolean equality (`'on' == 'yes'` is true), then
/// ordinal case-insensitive string equality. Unlike the relational operators,
/// equality never compares versions: `'01.0.0' == '1.0.0'` is false.
fn compare_equality_values(lhs: &str, rhs: &str) -> Result<bool, ()> {
    if lhs.is_empty() || rhs.is_empty() {
        // The empty string is no number, version or boolean.
        return Ok(lhs.is_empty() && rhs.is_empty());
    }
    let (lhs_number, rhs_number) = (equality_number(lhs)?, equality_number(rhs)?);
    if let (Some(lhs), Some(rhs)) = (lhs_number, rhs_number) {
        // NaN equals nothing, itself included.
        return Ok(lhs == rhs);
    }
    if lhs == rhs {
        return Ok(true);
    }
    if let (Some(lhs), Some(rhs)) = (parse_msbuild_bool(lhs), parse_msbuild_bool(rhs)) {
        return Ok(lhs == rhs);
    }
    // MSBuild string equality is ordinal case-insensitive, which folds the
    // full Unicode case map (e.g. `'É' == 'é'` is true). We don't carry a
    // Unicode case-mapping table, and `eq_ignore_ascii_case` only folds
    // `A-Z`/`a-z`. Byte-equal values already returned true above; pure ASCII
    // values are safe to fold here; other non-byte-equal values are
    // Unsupported rather than a guessed false gate.
    if lhs.is_ascii() && rhs.is_ascii() {
        Ok(lhs.eq_ignore_ascii_case(rhs))
    } else {
        Err(())
    }
}

/// The number MSBuild's equality reads `value` as, if any; `Err` where we do
/// not know whether it reads one. Beyond [`parse_msbuild_number`], it reads a
/// NaN spelling (`NaN` in any case, a sign before it, spaces about it) as NaN,
/// since .NET matches the symbol whatever the number style, and a number
/// followed by NULs as that number: `'NaN' == 'NaN'` is false, and
/// `'1' == '1%00'` true (both probed, msbuild-condition-oracle, SDK 10.0.401).
/// Any other spelling of NaN, or a NUL elsewhere, is not modelled.
fn equality_number(value: &str) -> Result<Option<f64>, ()> {
    let core = value.trim_matches(' ');
    let unsigned = core.strip_prefix(['+', '-']).unwrap_or(core);
    if unsigned.eq_ignore_ascii_case("nan") {
        return Ok(Some(f64::NAN));
    }
    // Another spelling that is NaN but for whitespace, signs and NULs.
    let mut loose = value
        .chars()
        .filter(|&c| !c.is_whitespace() && !matches!(c, '\0' | '+' | '-'))
        .map(|c| c.to_ascii_lowercase());
    let loosely_nan = loose.next() == Some('n')
        && loose.next() == Some('a')
        && loose.next() == Some('n')
        && loose.next().is_none();
    let digits = value.trim_end_matches('\0');
    if digits.contains('\0') || loosely_nan {
        return Err(());
    }
    Ok(parse_msbuild_number(digits))
}

/// A numeric condition operand, mirroring
/// `ConversionUtilities.TryConvertDecimalOrHexToDouble`: either a decimal
/// literal (optional leading sign, digits with at most one `.` — no
/// whitespace, no exponent, no thousands separators; values that round to
/// infinity are rejected), or a hex literal (`0x` + hex digits parsed as a
/// 32-bit value whose bit pattern is reinterpreted as signed, so
/// `0xFFFFFFFF` is `-1`). MSBuild compares these as .NET doubles; `f64`
/// string parsing is correctly rounded in both Rust and .NET, so the values
/// agree bit-for-bit.
fn parse_msbuild_number(value: &str) -> Option<f64> {
    if let Some(hex) = strip_prefix_ignore_ascii_case(value, "0x") {
        if hex.is_empty() || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        let bits = u32::from_str_radix(hex, 16).ok()?;
        return Some(bits as i32 as f64);
    }
    let unsigned = value.strip_prefix(['+', '-']).unwrap_or(value);
    let mut dots = 0usize;
    let mut digits = 0usize;
    for b in unsigned.bytes() {
        match b {
            b'.' => dots += 1,
            b'0'..=b'9' => digits += 1,
            _ => return None,
        }
    }
    if dots > 1 || digits == 0 {
        return None;
    }
    let number: f64 = value.parse().ok()?;
    number.is_finite().then_some(number)
}

/// MSBuild's boolean vocabulary (`ConversionUtilities.TryConvertStringToBool`):
/// `true`/`on`/`yes` and `false`/`off`/`no`, each optionally negated with a
/// leading `!`, all case-insensitive. Deliberately untrimmed: MSBuild's own
/// conversion is (probed via `ReferenceOutputAssembly=" true "`, dotnet
/// 10.0.301, 2026-07-10 — the padded spelling does not compare true).
pub(crate) fn parse_msbuild_bool(value: &str) -> Option<bool> {
    const TRUE_VALUES: [&str; 6] = ["true", "on", "yes", "!false", "!off", "!no"];
    const FALSE_VALUES: [&str; 6] = ["false", "off", "no", "!true", "!on", "!yes"];
    if TRUE_VALUES.iter().any(|t| value.eq_ignore_ascii_case(t)) {
        return Some(true);
    }
    if FALSE_VALUES.iter().any(|f| value.eq_ignore_ascii_case(f)) {
        return Some(false);
    }
    None
}

/// `Version.TryParse` as MSBuild condition operands (and
/// `[System.Version]::Parse`) see it: 2–4 dot-separated components, each
/// parsed like .NET `int.TryParse(NumberStyles.Integer)` — whitespace-trimmed
/// with an optional leading sign, so `' 2 . 5 '`, `'+2.5'` and `'1.-0'` are
/// versions; a negative component (`'1.-1'`) is none. Missing components are
/// `-1`, ranking below an explicit zero. (.NET also trims non-ASCII Unicode
/// whitespace, a degenerate spelling we reject toward Unsupported instead.)
fn parse_system_version(value: &str) -> Result<[i64; 4], ()> {
    let parts: Vec<&str> = value.split('.').collect();
    if !(2..=4).contains(&parts.len()) {
        return Err(());
    }
    let mut version = [-1, -1, -1, -1];
    for (idx, part) in parts.into_iter().enumerate() {
        // `int.TryParse(NumberStyles.Integer)`: ASCII whitespace about it, one
        // optional sign, ASCII digits; a negative component fails, so `-0` is
        // one and `-1` is not (as `certainly_not_a_version` reads it).
        let part = part.trim_matches(|c: char| c.is_ascii_whitespace());
        let (negative, digits) = match part.strip_prefix('-') {
            Some(digits) => (true, digits),
            None => (false, part.strip_prefix('+').unwrap_or(part)),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(());
        }
        let component = digits.parse::<i32>().map(i64::from).map_err(|_| ())?;
        if negative && component != 0 {
            return Err(());
        }
        version[idx] = component;
    }
    Ok(version)
}

/// Substitute `$(...)` in a condition-string side. Undefined
/// references become `""` (matching MSBuild) but their names are
/// appended to `undefined` so the caller can surface them as
/// [`UndefinedProperty`](super::diagnostic::DiagnosticKind::UndefinedProperty)
/// diagnostics — without this, a condition like
/// `'$(Foo)' == '$(Bar)'` where both sides are unknown to us would
/// trivially resolve to `'' == ''` = true, silently picking a branch
/// MSBuild might not. An unsupported expression on either side
/// (property function, item reference) poisons the whole condition,
/// since we can't compute the result without evaluating it.
///
/// Item-list (`@(Items)`) and metadata (`%(Identity)`) references
/// also poison the condition. `substitute` doesn't flag them
/// (they're not `$(...)`), so we scan the post-substitution value
/// explicitly. Without this, `Condition="'@(Compile)' == ''"` would
/// compare the literal text `@(Compile)` against `''` and silently
/// resolve to false — masking an item-list reference MSBuild would
/// have expanded, and breaking plan D5's "fail loudly on unsupported
/// constructs" stance.
fn expand_for_condition(
    raw: &str,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<Escaped, Reject> {
    // FS-probing property functions follow the same split as `Exists()`:
    // available exactly when the caller supplied a filesystem oracle.
    let (value, issues) = fs.substitute(raw, props);
    // The operand's carried trust is left behind, deliberately. Evaluation
    // short-circuits (`'$(X)' == '' Or '$(X)' == 'x'` never expands the second
    // arm when the first is true), so the trust of what *this* evaluation read
    // would under-report what the real build may read; a condition's trust is
    // the scan of its whole tree instead (`State::condition_trust`, Bucket B of
    // `docs/msbuild-value-carried-provenance-plan.md`).
    let value = value.into_ignoring_trust();
    // MSBuild expands the operand left to right and throws at the first
    // expression it throws on; whatever came before, it throws or rejects.
    // So the worst issue classifies the operand: a throw, then an expression
    // we do not model (which MSBuild may throw on), then a value the Unix
    // path adjustment leaves unknown (which it does not throw on).
    let mut worst: Option<Reject> = None;
    for issue in issues {
        let reject = match issue {
            Issue::Undefined { name } => {
                undefined.push(name);
                continue;
            }
            Issue::Throws { .. } => Reject::Throws,
            Issue::Unsupported { .. } => Reject::Unmodelled,
            Issue::ReturnsBoolean { .. }
            | Issue::ReturnsValue { .. }
            | Issue::PathAdjustmentUndecided { .. } => Reject::Undecided,
        };
        worst = worst.max(Some(reject));
    }
    // Item and metadata references are scanned on the **escaped** text, exactly
    // as MSBuild scans them: an escaped `%25(` is not a metadata reference. In
    // an item's condition MSBuild expands one the substituted text forms, and
    // may throw on it (an item function it does not know, MSB4184). It expands
    // them after the properties, so an operand whose properties leave a value
    // we do not know still forms one (`$(…)$(A)$(B)` with `A` holding `@`):
    // the scan joins the issues' verdict rather than waiting on it. The text
    // of an expression we left unexpanded is scanned too, which only declines.
    if fs.site == Site::ItemPass
        && (value.as_escaped().contains("@(") || value.as_escaped().contains("%("))
    {
        worst = worst.max(Some(Reject::Unmodelled));
    }
    if let Some(reject) = worst {
        return Err(reject);
    }
    // The value stays **in the domain**. Most operands are compared as text and
    // decode immediately ([`expand_operand`]) — but a built-in that splits or
    // trims its argument must do so *before* decoding, because an escaped `%3b`
    // is data rather than a separator and an escaped `%20` is data rather than
    // padding. `HasTrailingSlash` and `Exists` are exactly those.
    Ok(value)
}

/// A condition operand at its **point of use**: decoded exactly once.
///
/// MSBuild compares unescaped values, so `'%74rue' == 'true'` is true and
/// `'$(P)' == 'a b'` is true for `<P>a%20b</P>` (both oracle-pinned).
fn expand_operand(
    raw: &str,
    props: &PropertyMap,
    fs: Ctx<'_>,
    undefined: &mut Vec<String>,
) -> Result<String, Reject> {
    Ok(expand_for_condition(raw, props, fs, undefined)?.unescape())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// [`Probes`] answering `Exists` with `exists`, over an observer the test
    /// never reads.
    fn probes<'a>(exists: &'a dyn Fn(&str) -> bool) -> Probes<'a> {
        Probes {
            exists,
            observer: Box::leak(Box::new(Observer::new())),
            start: Start::Unknown,
        }
    }

    fn props(pairs: &[(&str, &str)]) -> PropertyMap {
        let mut m = PropertyMap::new();
        for (k, v) in pairs {
            m.insert(*k, *v);
        }
        m
    }

    /// Tests in this module assert outcome-only behaviour; shadow the
    /// outer `evaluate` to drop the undefined-property list so the
    /// assertions stay readable. Tests below that *do* check
    /// undefined names call `super::evaluate` explicitly.
    fn evaluate(source: &str, props: &PropertyMap) -> Outcome {
        super::evaluate(source, props).outcome
    }

    #[test]
    fn empty_condition_is_true() {
        assert_eq!(evaluate("", &PropertyMap::new()), Outcome::True);
    }

    /// MSBuild's parser throws on whitespace alone (MSB4092; probed,
    /// `dotnet msbuild` 10.0, in every position a condition takes).
    #[test]
    fn blank_condition_is_illegal() {
        for blank in ["   ", "\t", "\r\n"] {
            assert_eq!(evaluate(blank, &PropertyMap::new()), Outcome::Illegal);
            // MSBuild's parser rejects it, so it throws whatever any value
            // holds.
            assert_eq!(
                judge(
                    blank,
                    &PropertyMap::new(),
                    None,
                    crate::condition::Site::ItemPass,
                    &|_| true
                )
                .throws,
                Throws::Certainly
            );
        }
    }

    /// An operand on trusted values we cannot evaluate, which MSBuild reaches
    /// before the one that would decide the condition, decides nothing: it may
    /// throw (`'abc'.Substring(5)`, MSB4184) where the condition would be false.
    #[test]
    fn an_unevaluated_operand_before_the_deciding_one_decides_nothing() {
        let mut props = PropertyMap::new();
        props.insert("P", "abc");
        let never = |_: &str| false;
        assert_eq!(
            decide_without(
                "'$(P.Substring(5))' == '' And false",
                &props,
                None,
                crate::condition::Site::ItemPass,
                &never
            ),
            Decision::Unsupported
        );
        assert!(!decided_conjunctwise(
            "$([System.String]::Copy('')) Or true",
            &props,
            None,
            crate::condition::Site::ItemPass,
            &never,
            &|_| false
        ));
        // Reached after the deciding operand, it is never evaluated.
        assert_eq!(
            decide_without(
                "false And '$(P.Substring(5))' == ''",
                &props,
                None,
                crate::condition::Site::ItemPass,
                &never
            ),
            Decision::Decided(false)
        );
    }

    /// An operand that throws whatever the uncertain values hold ends the
    /// chain: past one of unknown value, the chain stopped with the absorbing
    /// value or throws, and nothing after it is reached.
    #[test]
    fn a_certain_throw_past_an_unknown_operand_ends_the_chain() {
        let uncertain = |name: &str| name.eq_ignore_ascii_case("U");
        let judged = judge(
            "'$(U)' == 'x' And 1 < abc And Exists('tail')",
            &PropertyMap::new(),
            None,
            crate::condition::Site::ItemPass,
            &uncertain,
        );
        assert_eq!(judged.value, Some(false));
        assert_eq!(judged.throws, Throws::Maybe);
        // The throwing operand is one we cannot evaluate to a boolean, so the
        // value holds only where it is not reached, and decides nothing.
        assert!(judged.unevaluated);
    }

    /// A `$(MSBuildToolsVersion)` reference beside a number is declined, since
    /// MSBuild reads its `Current` as Visual Studio's version; a literal
    /// `Current` compares as a string.
    #[test]
    fn only_a_toolset_version_reference_declines_equality() {
        let props = props(&[("MSBuildToolsVersion", "Current")]);
        assert_eq!(evaluate("'Current' != '17'", &props), Outcome::True);
        // Only an operand that is exactly the reference, beside a number.
        assert_eq!(
            evaluate("'build/$(MSBuildToolsVersion)' == 'build/Current'", &props),
            Outcome::True
        );
        assert_eq!(
            evaluate("'$(MSBuildToolsVersion)' == 'Current'", &props),
            Outcome::True
        );
        // Equality compares no versions, so beside one the text decides.
        assert_eq!(
            evaluate("'$(MSBuildToolsVersion)' == '18.0.0'", &props),
            Outcome::False
        );
        // A number as equality reads one, a trailing NUL included.
        assert_eq!(
            evaluate("'$(MSBuildToolsVersion)' == '18%00'", &props),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate("'$(MSBuildToolsVersion)' != '18'", &props),
            Outcome::Unsupported
        );
    }

    /// `AreFeaturesEnabled` reads `MSBuildDisableFeaturesFromVersion` with no
    /// reference to it, so a leaf calling it is uncertain where that name is.
    #[test]
    fn an_intrinsic_reads_its_implicit_property() {
        let props = props(&[("MSBuildDisableFeaturesFromVersion", "999.999")]);
        let uncertain = |name: &str| name.eq_ignore_ascii_case("MSBuildDisableFeaturesFromVersion");
        let judged = judge(
            "$([MSBuild]::AreFeaturesEnabled('99.99')) And 1 < abc",
            &props,
            None,
            crate::condition::Site::ItemPass,
            &uncertain,
        );
        assert_ne!(judged.throws, Throws::Certainly, "{judged:?}");
        // Nor is anything decided past it: it may throw before the operand
        // that would decide (`'bad'` is no version).
        assert_eq!(
            decide_without(
                "$([MSBuild]::AreFeaturesEnabled('bad')) And false",
                &props,
                None,
                crate::condition::Site::ItemPass,
                &uncertain
            ),
            Decision::Unsupported
        );
        // A spaced call reads it too; a literal that only spells the name
        // reads nothing.
        let mut references = Vec::new();
        implicit_references(
            "$([MSBuild]::AreFeaturesEnabled ('99.99'))",
            &mut references,
        );
        assert_eq!(references, ["MSBuildDisableFeaturesFromVersion"]);
        let mut references = Vec::new();
        implicit_references("AreFeaturesEnabled", &mut references);
        implicit_references("[MSBuild]::AreFeaturesEnabled('1')", &mut references);
        implicit_references("$(A)[MSBuild]::AreFeaturesEnabled(x)", &mut references);
        implicit_references("$ ([MSBuild]::AreFeaturesEnabled(x))", &mut references);
        assert!(references.is_empty(), "{references:?}");
    }

    /// Only a whole NaN spelling is declined: a word that contains `nan`
    /// compares as a string.
    #[test]
    fn a_word_containing_nan_compares_as_a_string() {
        let props = PropertyMap::new();
        assert_eq!(evaluate("'Finance' == 'Finance'", &props), Outcome::True);
        assert_eq!(evaluate("'Finance' == 'finance'", &props), Outcome::True);
        assert_eq!(evaluate("'banana' != 'Finance'", &props), Outcome::True);
        assert_eq!(evaluate("'- n a n' == 'x'", &props), Outcome::Unsupported);
    }

    #[test]
    fn bool_literals_case_insensitive() {
        assert_eq!(evaluate("true", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("True", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("FALSE", &PropertyMap::new()), Outcome::False);
    }

    #[test]
    fn bang_negates_bool_expression() {
        let p = props(&[("Configuration", "Debug")]);
        assert_eq!(evaluate("!false", &p), Outcome::True);
        assert_eq!(
            evaluate("!('$(Configuration)' == 'Debug')", &p),
            Outcome::False
        );
    }

    #[test]
    fn is_null_or_empty_as_a_condition_leaf() {
        // `$([System.String]::IsNullOrEmpty('$(X)'))` reduces to a bool literal
        // via `substitute`, then the condition treats "True"/"False" as the
        // leaf. Pinned against dotnet msbuild 10.0.301.
        let set = props(&[("X", "v10.0")]);
        assert_eq!(
            evaluate("$([System.String]::IsNullOrEmpty('$(X)'))", &set),
            Outcome::False
        );
        assert_eq!(
            evaluate("!$([System.String]::IsNullOrEmpty('$(X)'))", &set),
            Outcome::True
        );
        let empty = props(&[("X", "")]);
        assert_eq!(
            evaluate("$([System.String]::IsNullOrEmpty('$(X)'))", &empty),
            Outcome::True
        );
    }

    #[test]
    fn workflow_build_extensions_import_gate_resolves_false() {
        // The SDK's `Microsoft.WorkflowBuildExtensions.targets` import gate
        // (Microsoft.Common.targets) is the first `walk_opaque` latch in a real
        // `net10.0` chain: its left conjunction is true for any modern TFV and
        // the trailing `Exists('…WorkflowBuildExtensions.targets')` is false, so
        // MSBuild skips the import. Before `IsNullOrEmpty` the whole condition
        // was Unsupported (latching opacity and poisoning ~50 downstream reads);
        // now it must resolve exactly to False. `Exists` returns false for the
        // never-present .NET-Framework/VS targets file.
        let p = props(&[
            ("TargetFrameworkVersion", "v10.0"),
            ("MSBuildToolsPath", "/nonexistent/tools"),
        ]);
        let cond = "('$(TargetFrameworkVersion)' != 'v2.0' and \
                    '$(TargetFrameworkVersion)' != 'v3.5' and \
                    (!$([System.String]::IsNullOrEmpty('$(TargetFrameworkVersion)')) and \
                    !$(TargetFrameworkVersion.StartsWith('v4.0')))) and \
                    Exists('$(MSBuildToolsPath)\\Microsoft.WorkflowBuildExtensions.targets')";
        let eval = super::evaluate_with_exists(cond, &p, probes(&|_| false));
        assert_eq!(eval.outcome, Outcome::False, "{cond}");
    }

    #[test]
    fn bang_does_not_negate_string_comparison_without_parens() {
        let p = props(&[("Configuration", "Debug")]);
        assert_eq!(
            evaluate("!'$(Configuration)' == 'Release'", &p),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate("!'$(Configuration)' != ''", &p),
            Outcome::Unsupported
        );
    }

    #[test]
    fn string_equality_compares_substituted_values() {
        let p = props(&[("Configuration", "Release")]);
        assert_eq!(
            evaluate("'$(Configuration)' == 'Release'", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("'$(Configuration)' != 'Release'", &p),
            Outcome::False
        );
        assert_eq!(
            evaluate("'$(Configuration)' == 'Debug'", &p),
            Outcome::False
        );
    }

    #[test]
    fn string_equality_is_case_insensitive() {
        let p = props(&[("Configuration", "Release")]);
        // Both the value and the literal differ in case — MSBuild
        // matches them.
        assert_eq!(
            evaluate("'$(Configuration)' == 'release'", &p),
            Outcome::True
        );
    }

    #[test]
    fn undefined_property_becomes_empty_string_and_is_reported() {
        // `'$(Missing)' == ''` is the canonical "if not set" idiom.
        // For evaluation purposes the undefined ref expands to "" (so
        // the outcome matches what MSBuild would compute given the
        // same property map), but the name is returned in
        // `undefined_properties` so the caller can mark the project
        // partial — our map may be missing values MSBuild itself
        // would have seen.
        let eval = super::evaluate("'$(Missing)' == ''", &PropertyMap::new());
        assert_eq!(eval.outcome, Outcome::True);
        assert_eq!(eval.undefined_properties, vec!["Missing".to_string()]);
    }

    /// Equality's emptiness question expands a side that is one reference
    /// whole; the comparison after it does not expand it again, so each
    /// undefined name it read is reported once.
    #[test]
    fn a_side_expanded_for_its_emptiness_reports_its_names_once() {
        let eval = super::evaluate("'$(A)$(T)' == 'foo'", &props(&[("A", "foo")]));
        assert_eq!(eval.outcome, Outcome::True);
        assert_eq!(eval.undefined_properties, vec!["T".to_string()]);
    }

    #[test]
    fn both_sides_undefined_collects_both_names() {
        // The motivating case from codex review: both sides expand to
        // "" silently, the comparison is trivially true, and without
        // reporting we'd silently include the gated construct.
        let eval = super::evaluate("'$(A)' == '$(B)'", &PropertyMap::new());
        assert_eq!(eval.outcome, Outcome::True);
        assert_eq!(
            eval.undefined_properties,
            vec!["A".to_string(), "B".to_string()]
        );
    }

    #[test]
    fn defined_property_does_not_appear_in_undefined_list() {
        let p = props(&[("A", "x")]);
        let eval = super::evaluate("'$(A)' == '$(Missing)'", &p);
        assert_eq!(eval.outcome, Outcome::False);
        assert_eq!(eval.undefined_properties, vec!["Missing".to_string()]);
    }

    #[test]
    fn short_circuit_skips_undefined_collection_on_decided_branch() {
        // `false And X` short-circuits before evaluating X, so any
        // undefined refs inside X are not collected — MSBuild itself
        // wouldn't observe them either. We rely on this so a
        // common-case condition like
        //   '$(Configuration)' == 'Debug' And '$(SomeFlag)' == 'on'
        // doesn't drag an extra UndefinedProperty in for SomeFlag
        // when Configuration already resolved the And to false.
        let p = props(&[("A", "x")]);
        let eval = super::evaluate("'$(A)' == 'no' And '$(Missing)' == 'y'", &p);
        assert_eq!(eval.outcome, Outcome::False);
        assert!(
            eval.undefined_properties.is_empty(),
            "{:?}",
            eval.undefined_properties
        );
    }

    /// The reference scan feeding the *taint* channels is a walk of the whole
    /// parsed tree, deliberately blind to evaluation order — unlike the
    /// undefined-collection above, which rides evaluation and so legitimately
    /// misses a short-circuited arm.
    ///
    /// The distinction is load-bearing and easy to erase by "simplifying" both
    /// onto one mechanism. Taint asks *could this branch have depended on the
    /// property*, which a short-circuit does not answer: we skipped the arm
    /// because of what **our** property table said, and the real build's table
    /// may differ precisely because the property is untrustworthy. So a name in
    /// an arm we never evaluated must still be reported.
    #[test]
    fn the_reference_scan_sees_a_short_circuited_arm() {
        fn refs_of(cond: &str) -> Vec<String> {
            let tokens = super::tokenise(cond).expect("tokenises");
            let mut parser = super::Parser {
                tokens: &tokens,
                pos: 0,
                depth: 0,
            };
            let expr = parser.parse_or().expect("parses");
            let mut out = Vec::new();
            super::refs_outside_empty_comparison(&expr, &mut out);
            out
        }

        // `'$(A)' == 'x'` decides the `Or`, so `B`'s arm is never evaluated.
        let scanned = refs_of("'$(A)' == 'x' Or '$(B)' == 'y'");
        assert!(
            scanned.iter().any(|r| r == "B"),
            "a short-circuited arm's reference must still be scanned; got {scanned:?}"
        );

        // Same for `And`, and through a member access on the unreached side.
        let scanned = refs_of("'$(A)' == 'no' And '$(B.Length)' == '3'");
        assert!(
            scanned.iter().any(|r| r == "B"),
            "a short-circuited arm's receiver must still be scanned; got {scanned:?}"
        );
    }

    #[test]
    fn pure_evaluation_short_circuits_unreached_exists() {
        assert_eq!(
            evaluate("true Or Exists('x')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("false And Exists('x')", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn unsupported_condition_returns_no_undefined_names() {
        // When the outcome is Unsupported, the caller emits
        // UnsupportedCondition; any UndefinedProperty for properties
        // mentioned in the same condition would be redundant noise.
        let eval = super::evaluate("'$(Missing)' != '' Or Exists('x')", &PropertyMap::new());
        assert_eq!(eval.outcome, Outcome::Unsupported);
        assert!(eval.undefined_properties.is_empty());
    }

    #[test]
    fn and_or_combine() {
        let p = props(&[("A", "x"), ("B", "y")]);
        assert_eq!(
            evaluate("'$(A)' == 'x' And '$(B)' == 'y'", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("'$(A)' == 'x' And '$(B)' == 'z'", &p),
            Outcome::False
        );
        assert_eq!(
            evaluate("'$(A)' == 'x' Or '$(B)' == 'z'", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("'$(A)' == 'no' Or '$(B)' == 'no'", &p),
            Outcome::False
        );
    }

    #[test]
    fn parens_override_precedence() {
        // Without parens, `And` binds tighter than `Or`:
        //   false Or true And false = false Or (true And false) = false
        assert_eq!(
            evaluate("false Or true And false", &PropertyMap::new()),
            Outcome::False
        );
        // With parens the meaning flips:
        //   (false Or true) And false = true And false = false
        // — boring example. Pick a more discriminating one:
        //   true And (false Or true) = true And true = true
        assert_eq!(
            evaluate("true And (false Or true)", &PropertyMap::new()),
            Outcome::True
        );
        // Without parens: true And false Or true = (true And false) Or true = true
        assert_eq!(
            evaluate("true And false Or true", &PropertyMap::new()),
            Outcome::True
        );
    }

    #[test]
    fn property_function_makes_condition_unsupported() {
        let p = props(&[("X", "foo")]);
        // The property-function `$([System.String]::Copy($(X)))` lives
        // inside a string literal, but substitute() emits Unsupported
        // for it — so the whole condition becomes Unsupported.
        assert_eq!(
            evaluate("'$([System.String]::Copy($(X)))' == 'foo'", &p),
            Outcome::Unsupported
        );
        // A quote inside it ends the string literal (MSBuild's scanner looks
        // for nothing else), which leaves tokens no grammar accepts.
        // Oracle-pinned: rejected.
        assert_eq!(
            evaluate("'$([System.String]::Copy('x'))' == 'x'", &p),
            Outcome::Illegal
        );
    }

    #[test]
    fn exists_without_filesystem_callback_is_unsupported() {
        assert_eq!(
            evaluate("Exists('a.fs')", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn exists_uses_filesystem_callback() {
        let exists = |path: &str| path == "a.fs";
        assert_eq!(
            super::evaluate_with_exists("Exists('a.fs')", &PropertyMap::new(), probes(&exists))
                .outcome,
            Outcome::True
        );
        assert_eq!(
            super::evaluate_with_exists("Exists('b.fs')", &PropertyMap::new(), probes(&exists))
                .outcome,
            Outcome::False
        );
    }

    #[test]
    fn exists_trims_expanded_argument_before_callback() {
        let p = props(&[("File", " marker.txt ")]);
        let exists = |path: &str| path == "marker.txt";
        assert_eq!(
            super::evaluate_with_exists("Exists(' $(File) ')", &p, probes(&exists)).outcome,
            Outcome::True
        );
    }

    #[test]
    fn exists_supports_bang_and_property_substitution() {
        let p = props(&[("File", "a.fs")]);
        let exists = |path: &str| path == "a.fs";
        assert_eq!(
            super::evaluate_with_exists("!Exists('b.fs')", &p, probes(&exists)).outcome,
            Outcome::True
        );
        let eval = super::evaluate_with_exists("Exists('$(File)')", &p, probes(&exists));
        assert_eq!(eval.outcome, Outcome::True);
        assert!(eval.undefined_properties.is_empty());
    }

    #[test]
    fn exists_reports_undefined_properties() {
        let exists = |_path: &str| false;
        let eval = super::evaluate_with_exists(
            "Exists('$(Missing)')",
            &PropertyMap::new(),
            probes(&exists),
        );
        assert_eq!(eval.outcome, Outcome::False);
        assert_eq!(eval.undefined_properties, vec!["Missing".to_string()]);
    }

    #[test]
    fn unknown_function_call_makes_condition_unsupported() {
        assert_eq!(
            evaluate("SomeUnknownFunction('a.fs')", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn unterminated_string_is_illegal() {
        assert_eq!(
            evaluate("'unterminated", &PropertyMap::new()),
            Outcome::Illegal
        );
    }

    #[test]
    fn trailing_garbage_after_valid_prefix_is_illegal() {
        // A condition that parses cleanly for the first few tokens
        // and then has junk must NOT be reported as the prefix's
        // truth value: MSBuild's parser rejects the junk.
        assert_eq!(
            evaluate("'a' == 'a' garbage", &PropertyMap::new()),
            Outcome::Illegal
        );
    }

    #[test]
    fn numeric_version_relational_operators_are_supported() {
        assert_eq!(
            evaluate("'2.0' > '1.9'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'2.0' < '2.0.0'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'v2.0' < '2.1'", &PropertyMap::new()),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate("'10.0' <= '9.0'", &PropertyMap::new()),
            Outcome::False
        );
    }

    /// MSBuild unescapes `%XX` (a `%` followed by two hex digits) inside
    /// conditions before comparing: `'%74rue' == 'true'` is *true* (pinned
    /// against `dotnet msbuild` 10.0.301, property and item gates alike).
    /// We do not model unescaping, so committing a boolean from the raw
    /// text would be a wrong gate — an escape-bearing condition degrades
    /// to `Unsupported` (fail-safe: exclusion plus a diagnostic). A `%`
    /// with any other suffix is literal and evaluates normally.
    #[test]
    fn a_built_in_splits_and_trims_before_it_decodes() {
        // `HasTrailingSlash` expands its argument into an *item list*: split on
        // `;`, trim each entry. Both happen in the escaped domain, and the decode
        // is the leaf — the same rule the item pass follows. Pinned against
        // `dotnet msbuild` 10.0.301 (2026-07-12):
        //
        //   HasTrailingSlash('foo%2f')  -> true   (decoded: `foo/`)
        //   HasTrailingSlash('foo/%20') -> false  (decoded: `foo/ ` — the escaped
        //                                          space is data, and is NOT
        //                                          trimmed away)
        //
        // The second is the whole point: decoding and *then* trimming would eat a
        // character MSBuild keeps, and commit `true` for a value that has no
        // trailing slash at all.
        let props = PropertyMap::new();
        assert_eq!(
            evaluate("HasTrailingSlash('foo%2f')", &props),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash('foo/%20')", &props),
            Outcome::False
        );
        // Authored padding *is* padding, and is still trimmed.
        assert_eq!(
            evaluate("HasTrailingSlash('  foo/  ')", &props),
            Outcome::True
        );
        // The list split is on escaped semicolons, so an escaped `%3b` is data:
        // one entry, which does not end in a slash.
        assert_eq!(
            evaluate("HasTrailingSlash('a%3bb')", &props),
            Outcome::False
        );
    }

    #[test]
    fn escapes_are_decoded_at_the_operand_not_degraded() {
        // MSBuild unescapes `%XX` at the operand leaf, so an escape-bearing
        // *quoted* operand compares as the text it decodes to. Stage E2 of
        // `docs/completed/msbuild-escaped-value-plan.md`: this used to degrade the whole
        // condition, which was fail-safe but cost real gates. All pinned against
        // `dotnet msbuild` 10.0.301 (2026-07-12).
        assert_eq!(
            evaluate("'%74rue' == 'true'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'a%20b' == 'a b'", &PropertyMap::new()),
            Outcome::True
        );
        // …and so does one arriving through a property value.
        let mut props = PropertyMap::new();
        props.insert("P", "a%20b");
        assert_eq!(evaluate("'$(P)' == 'a b'", &props), Outcome::True);

        // A `%` **outside** quotes is not an escape at all: MSBuild's scanner
        // rejects it outright (`MSB4090: Found an unexpected character '7' at
        // position 1 in condition "%74rue"`), and likewise inside a bare numeric
        // (`1%2E0 > 0.5`). Committing a boolean for a condition MSBuild refuses
        // to evaluate would be a wrong gate.
        assert_eq!(evaluate("%74rue", &PropertyMap::new()), Outcome::Illegal);
        assert_eq!(
            evaluate("1%2E0 > 0.5", &PropertyMap::new()),
            Outcome::Illegal
        );

        // Bare `%` (not followed by two hex digits) is literal, not an
        // escape: these stay committed.
        assert_eq!(
            evaluate("'100%' == '100%'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'a%zz' == 'a%zz'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'a%zz' == 'true'", &PropertyMap::new()),
            Outcome::False
        );
    }

    /// When both sides are numeric, relational comparison is double-first —
    /// `1.5 > 1.20` numerically, NOT version-wise (`1.5 < 1.20` as versions).
    /// Pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn dotted_numeric_relational_operands_compare_as_doubles() {
        assert_eq!(
            evaluate("'1.5' > '1.20'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'1.2' < '1.10'", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn equality_uses_numeric_comparison_when_both_sides_are_numeric() {
        assert_eq!(evaluate("1 == 1.0", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("'1' == '1.0'", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("01 == 1", &PropertyMap::new()), Outcome::True);
        assert_eq!(
            evaluate("'1.5' == '1.50'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(evaluate("1 != 1.0", &PropertyMap::new()), Outcome::False);
        assert_eq!(evaluate("'01' != '1'", &PropertyMap::new()), Outcome::False);
    }

    #[test]
    fn ordinary_comparisons_preserve_operand_whitespace() {
        assert_eq!(
            evaluate("' 1 ' == '1'", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(evaluate("' 1 ' != '1'", &PropertyMap::new()), Outcome::True);
        assert_eq!(
            evaluate("' 2 ' > '1'", &PropertyMap::new()),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate("' 2.0 ' == '2.0'", &PropertyMap::new()),
            Outcome::False
        );

        let p = props(&[("Value", " 2 ")]);
        assert_eq!(evaluate("'$(Value)' == '2'", &p), Outcome::False);
        assert_eq!(evaluate("'$(Value)' > '1'", &p), Outcome::Illegal);
    }

    /// Unlike the relational operators, MSBuild `==` / `!=` never fall back
    /// to `System.Version` comparison — non-numeric dotted values compare as
    /// strings. Every case here is pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn equality_never_compares_versions() {
        assert_eq!(
            evaluate("'2.0' == '2.0.0'", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("'2.0' != '2.0.0'", &PropertyMap::new()),
            Outcome::True
        );
        // Version-equal but string-different spellings are NOT equal.
        assert_eq!(
            evaluate("'01.0.0' == '1.0.0'", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("'1.0.0' == '1.00.0'", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("' 2 . 5 ' == '2.5'", &PropertyMap::new()),
            Outcome::False
        );
    }

    /// MSBuild's `==` coerces both sides to its boolean vocabulary
    /// (`true`/`on`/`yes`, `false`/`off`/`no`, `!`-negations) before falling
    /// back to string comparison. Pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn equality_compares_msbuild_booleans() {
        assert_eq!(
            evaluate("'on' == 'yes'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'!false' == 'true'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'!TRUE' == 'FALSE'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'off' != 'no'", &PropertyMap::new()),
            Outcome::False
        );
        // Bool coercion only fires when BOTH sides are boolean spellings.
        assert_eq!(evaluate("'on' == 'x'", &PropertyMap::new()), Outcome::False);
    }

    /// Hex literals are numeric operands: parsed as a 32-bit value whose bit
    /// pattern is reinterpreted as signed (`Int32.TryParse` with
    /// `AllowHexSpecifier`). Pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn hex_operands_compare_numerically() {
        assert_eq!(
            evaluate("'0x10' == '16'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'0xFF' > '254'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'0x10' > '15'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'0xFFFFFFFF' == '-1'", &PropertyMap::new()),
            Outcome::True
        );
        // Overflowing 32 bits stops being numeric: string comparison.
        assert_eq!(
            evaluate("'0x100000000' == '4294967296'", &PropertyMap::new()),
            Outcome::False
        );
    }

    /// MSBuild numeric equality is .NET *double* equality — values collapse
    /// to the nearest representable f64 before comparing. Pinned against
    /// `dotnet msbuild` 10.0.300.
    #[test]
    fn equality_uses_double_rounding() {
        assert_eq!(
            evaluate("'0.1' == '0.10000000000000000001'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "'99999999999999999999999999999999999999' == '99999999999999999999999999999999999998'",
                &PropertyMap::new()
            ),
            Outcome::True
        );
        assert_eq!(evaluate("'-0' == '0'", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("'+1' == '1'", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("'2.' == '2'", &PropertyMap::new()), Outcome::True);
    }

    /// The numeric grammar excludes exponents (`NumberStyles` without
    /// `AllowExponent`), so `'1e2'` is a string, not 100. Pinned against
    /// `dotnet msbuild` 10.0.300.
    #[test]
    fn exponent_spellings_are_not_numeric() {
        assert_eq!(
            evaluate("'1e2' == '100'", &PropertyMap::new()),
            Outcome::False
        );
    }

    /// An empty side short-circuits equality to emptiness comparison
    /// (`MultipleComparisonNode.EvaluatesToEmpty`), before the string path
    /// would bail to Unsupported on non-ASCII content. Pinned against
    /// `dotnet msbuild` 10.0.300.
    #[test]
    fn empty_comparison_against_non_ascii_value_is_supported() {
        assert_eq!(evaluate("'É' == ''", &PropertyMap::new()), Outcome::False);
        assert_eq!(evaluate("'É' != ''", &PropertyMap::new()), Outcome::True);
    }

    #[test]
    fn target_framework_version_condition_is_supported() {
        let p = props(&[("_TargetFrameworkVersionWithoutV", "2.0")]);
        assert_eq!(
            evaluate("'$(_TargetFrameworkVersionWithoutV)' < '2.1'", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("'$(_TargetFrameworkVersionWithoutV)' >= '2.1'", &p),
            Outcome::False
        );
    }

    #[test]
    fn msbuild_version_comparison_functions_are_supported() {
        let p = props(&[("TargetFrameworkVersion", "v8.0")]);
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals($(TargetFrameworkVersion), '8.0'))",
                &p
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionLessThan($(TargetFrameworkVersion), '8.0'))",
                &p
            ),
            Outcome::False
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals('2.0', '2.0.0'))",
                &p
            ),
            Outcome::True
        );
    }

    // Pinned against `dotnet msbuild` 10.0.300:
    //   $([MSBuild]::VersionEquals('2.0', '2.0.0'))                    => TRUE
    //   $([MSBuild]::VersionEquals('v1.2.3-pre+metadata', '1.2.3'))    => TRUE
    //   $([MSBuild]::VersionEquals('01.0', '1.0'))                     => TRUE
    //   $([MSBuild]::VersionEquals('1.2', '1.3'))                      => FALSE
    //   $([MSBuild]::VersionNotEquals('2.0', '2.0.0'))                 => FALSE
    //   $([MSBuild]::VersionNotEquals('1.2', '1.3'))                   => TRUE
    //   $([msbuild]::versionequals('1.0','1'))                         => TRUE
    //   $([MSBuild]::VersionEquals('abc', '1.0'))                      => MSB4184
    // (The real .NET SDK gates on these, e.g.
    // `Microsoft.NET.TargetFrameworkInference.targets`:
    // `$([MSBuild]::VersionEquals($(TargetPlatformVersion), 0.0))`.)
    #[test]
    fn msbuild_version_equality_functions_are_supported() {
        let p = props(&[("TargetPlatformVersion", "0.0")]);
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionEquals($(TargetPlatformVersion), 0.0))",
                &p
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate("$([MSBuild]::VersionEquals('2.0', '2.0.0'))", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionEquals('v1.2.3-pre+metadata', '1.2.3'))",
                &p
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate("$([MSBuild]::VersionEquals('01.0', '1.0'))", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("$([MSBuild]::VersionEquals('1.2', '1.3'))", &p),
            Outcome::False
        );
        assert_eq!(
            evaluate("$([MSBuild]::VersionNotEquals('2.0', '2.0.0'))", &p),
            Outcome::False
        );
        assert_eq!(
            evaluate("$([MSBuild]::VersionNotEquals('1.2', '1.3'))", &p),
            Outcome::True
        );
        assert_eq!(
            evaluate("$([msbuild]::versionequals('1.0','1'))", &p),
            Outcome::True
        );
        // A malformed operand throws (MSB4184; probed, msbuild-condition-oracle,
        // SDK 10.0.401).
        assert_eq!(
            evaluate("$([MSBuild]::VersionEquals('abc', '1.0'))", &p),
            Outcome::Illegal
        );
    }

    #[test]
    fn msbuild_version_comparison_functions_use_simple_version_operands() {
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals('1', '1.0'))",
                &PropertyMap::new(),
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThan('10.0.100-preview.1', '10.0.99'))",
                &PropertyMap::new(),
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThan('10.0.100-preview.1', '10.0.100'))",
                &PropertyMap::new(),
            ),
            Outcome::False
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals('v1.2.3-pre+metadata', '1.2.3.0'))",
                &PropertyMap::new(),
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionLessThan('3.2', '3.14-pre'))",
                &PropertyMap::new(),
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals('3+metadata', '3.0'))",
                &PropertyMap::new(),
            ),
            Outcome::True
        );
    }

    #[test]
    fn msbuild_version_comparison_functions_reject_invalid_version_operands() {
        // Each throws (MSB4184; probed, msbuild-condition-oracle, SDK 10.0.401).
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThan('1.2.3.4.5', '1.0'))",
                &PropertyMap::new(),
            ),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThan('2147483648.0', '1.0'))",
                &PropertyMap::new(),
            ),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate(
                "$([MSBuild]::VersionGreaterThanOrEquals('vv1.2', '1.0'))",
                &PropertyMap::new(),
            ),
            Outcome::Illegal
        );
    }

    #[test]
    fn msbuild_version_function_respects_boolean_short_circuit() {
        let eval = super::evaluate(
            "'$(Known)' == 'no' And $([MSBuild]::VersionGreaterThanOrEquals($(Missing), '8.0'))",
            &props(&[("Known", "yes")]),
        );
        assert_eq!(eval.outcome, Outcome::False);
        assert!(eval.undefined_properties.is_empty());
    }

    #[test]
    fn system_version_parse_component_comparisons_are_supported() {
        let p = props(&[("WindowsSdkPackageVersion", "10.0.26100.34-preview")]);
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('$(WindowsSdkPackageVersion.Split('-')[0])').Build) <= 26100",
                &p
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('$(WindowsSdkPackageVersion.Split('-')[0])').Revision) <= 33",
                &p
            ),
            Outcome::False
        );
    }

    #[test]
    fn system_version_parse_rejects_unsplit_prerelease_versions() {
        let p = props(&[("WindowsSdkPackageVersion", "10.0.26100.34-preview")]);
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('$(WindowsSdkPackageVersion)').Build) <= 26100",
                &p
            ),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0.1-preview').Build) <= 1",
                &PropertyMap::new()
            ),
            Outcome::Unsupported
        );
    }

    #[test]
    fn system_version_parse_missing_build_and_revision_are_negative_one() {
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0').Build) < 0",
                &PropertyMap::new()
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0.1').Revision) < 0",
                &PropertyMap::new()
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0').Build) >= 0",
                &PropertyMap::new()
            ),
            Outcome::False
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0').Build) == -1",
                &PropertyMap::new()
            ),
            Outcome::True
        );
    }

    /// MSBuild's relational operators accept a plain number against a
    /// version (`NumericComparisonExpressionNode`'s mixed `Compare`
    /// overloads): the number is compared against the version's *major*
    /// component only, and on a tie the version counts as strictly greater
    /// ("6.0.0.0 > 6"). Every case pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn mixed_number_and_version_relational_comparisons_are_supported() {
        let cases = [
            ("'1' < '2.0.0'", Outcome::True),
            ("'1.0.0' > '1'", Outcome::True),
            // Major tie: the version side is strictly greater.
            ("'2' < '2.0.0'", Outcome::True),
            ("'2' <= '2.0.0'", Outcome::True),
            ("'2' >= '2.0.0'", Outcome::False),
            ("'1' < '1.0.1'", Outcome::True),
            ("'3' > '2.9.0'", Outcome::True),
            // Only the major component is consulted: 0.5 vs major 0.
            ("'.5' < '0.75.0'", Outcome::False),
            ("'0x10' < '16.0.1'", Outcome::True),
            ("'-1' < '0.0.1'", Outcome::True),
        ];
        for (cond, expected) in cases {
            assert_eq!(evaluate(cond, &PropertyMap::new()), expected, "{cond}");
        }
    }

    /// `Version.TryParse` runs components through `int.TryParse`, which
    /// trims whitespace and accepts a leading `+` — so `'+2.5'` and
    /// `' 2 . 5 '` are versions, not junk. Pinned against `dotnet msbuild`
    /// 10.0.300.
    #[test]
    fn version_operands_accept_signed_and_whitespace_components() {
        assert_eq!(
            evaluate("'+2.5' < '2.5.0'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'+2.5' > '2.5.0'", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("' 2 . 5 ' > '2.4'", &PropertyMap::new()),
            Outcome::True
        );
    }

    /// MSBuild's scanner lexes bare numerics greedily — hex, dot-led,
    /// sign-led, and multi-dot (version) spellings are all one numeric
    /// token, with validity decided by the later conversion. Pinned against
    /// `dotnet msbuild` 10.0.300.
    #[test]
    fn bare_numeric_spellings_match_msbuild() {
        let cases = [
            ("0x10 == 16", Outcome::True),
            (".5 < 1", Outcome::True),
            ("-.5 < 0", Outcome::True),
            ("1.2.3 < 1.2.4", Outcome::True),
        ];
        for (cond, expected) in cases {
            assert_eq!(evaluate(cond, &PropertyMap::new()), expected, "{cond}");
        }
    }

    /// MSBuild tolerates whitespace at every joint of the property-function
    /// syntax: inside `$( … )`, between the member name and its argument
    /// list, around arguments, and around the trailing member access.
    /// Pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn property_function_whitespace_is_tolerated() {
        let cases = [
            "$( [MSBuild]::VersionGreaterThan('2','1') )",
            "$([MSBuild]::VersionGreaterThan ('2','1'))",
            "$([System.Version]::Parse ('10.0.1').Build) == 1",
            "$([System.Version]::Parse( '10.0.1' ).Build) == 1",
            "$([System.Version]::Parse('10.0.1') .Build) == 1",
            "$([System.Version]::Parse('10.0.1').Build ) == 1",
        ];
        for cond in cases {
            assert_eq!(evaluate(cond, &PropertyMap::new()), Outcome::True, "{cond}");
        }
    }

    /// MSBuild resolves property-function type and member names
    /// case-insensitively. Pinned against `dotnet msbuild` 10.0.300.
    #[test]
    fn msbuild_version_function_names_are_case_insensitive() {
        let cases = [
            "$([msbuild]::VersionGreaterThan('2','1'))",
            "$([MSBuild]::versiongreaterthan('2','1'))",
            "$([MSBUILD]::VERSIONGREATERTHAN('2','1'))",
            "$([MSBuild]::versionlessthan('1.0', '2'))",
        ];
        for cond in cases {
            assert_eq!(evaluate(cond, &PropertyMap::new()), Outcome::True, "{cond}");
        }
    }

    /// `[System.Version]::Parse(...).Build` and the `.Split('-')[0]` idiom
    /// resolve case-insensitively too. Pinned against `dotnet msbuild`
    /// 10.0.300.
    #[test]
    fn system_version_parse_is_case_insensitive() {
        assert_eq!(
            evaluate(
                "$([System.version]::parse('10.0.1').build) == 1",
                &PropertyMap::new()
            ),
            Outcome::True
        );
        assert_eq!(
            evaluate(
                "$([System.Version]::Parse('10.0.1').BUILD) == 1",
                &PropertyMap::new()
            ),
            Outcome::True
        );
        let p = props(&[("V", "10.0.26100.34-preview")]);
        assert_eq!(
            evaluate(
                "$([System.version]::parse('$(V.split('-')[0])').build) <= 26100",
                &p
            ),
            Outcome::True
        );
    }

    #[test]
    fn bang_does_not_negate_scalar_comparison_without_parens() {
        assert_eq!(
            evaluate("!1 == 2", &PropertyMap::new()),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate(
                "!$([System.Version]::Parse('10.0').Build) == 2",
                &PropertyMap::new()
            ),
            Outcome::Unsupported
        );
        assert_eq!(evaluate("!(1 == 2)", &PropertyMap::new()), Outcome::True);
    }

    #[test]
    fn non_version_relational_comparison_is_illegal() {
        assert_eq!(
            evaluate("'alpha' > 'beta'", &PropertyMap::new()),
            Outcome::Illegal
        );
        // `$(MSBuildToolsVersion)` expanding to `Current` compares as Visual
        // Studio's version (oracle-pinned: `$(MSBuildToolsVersion) < 18` is
        // false), so a `Current` operand is no claim.
        let p = props(&[("MSBuildToolsVersion", "Current")]);
        assert_eq!(
            evaluate("$(MSBuildToolsVersion) < 18", &p),
            Outcome::Unsupported
        );
    }

    #[test]
    fn item_reference_inside_string_makes_condition_unsupported() {
        // `substitute` only handles `$(...)`, so a literal `@(...)`
        // inside a string literal would survive expansion and the
        // Compare would silently treat it as plain text. That would
        // produce the wrong truth value with no diagnostic — exactly
        // the failure mode plan D5's fail-loud rule exists to
        // prevent.
        assert_eq!(
            evaluate("'@(Compile)' == ''", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn metadata_reference_inside_string_makes_condition_unsupported() {
        assert_eq!(
            evaluate("'%(Identity)' == 'foo.fs'", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn item_reference_introduced_via_substitution_makes_condition_unsupported() {
        // The reference can also arrive via a property: a property whose
        // value happens to be `@(Files)` substitutes cleanly (no $(...)
        // inside), and a condition of the item pass then expands the item
        // list the substitution forms, which we do not model. One of the
        // property pass reads it as text (`Site`).
        let p = props(&[("Sources", "@(Files)")]);
        let at = |site| super::evaluate_at("'$(Sources)' == ''", &p, None, site).outcome;
        assert_eq!(at(super::Site::ItemPass), Outcome::Unsupported);
        assert_eq!(at(super::Site::PropertyPass), Outcome::False);
    }

    #[test]
    fn unknown_operator_anywhere_makes_condition_unsupported() {
        // An unmodelled function call lexes as a token sequence the parser
        // can't fit anywhere; we fail the whole condition rather than guess
        // at a truth value for the unmodelled operator. This is the
        // conservative half of plan D5's "fail loudly" stance: better to
        // mark the construct excluded than silently flip its truth value.
        assert_eq!(
            evaluate(
                "'$(X)' == '' Or SomeUnknownFunction('x')",
                &PropertyMap::new()
            ),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate("true And SomeUnknownFunction('x')", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn substitution_inside_string_concatenates_with_surrounding_text() {
        let p = props(&[("Version", "8.0")]);
        assert_eq!(evaluate("'net$(Version)' == 'net8.0'", &p), Outcome::True);
    }

    #[test]
    fn nested_parens_handled() {
        assert_eq!(
            evaluate("((true And false) Or (true And true))", &PropertyMap::new()),
            Outcome::True
        );
    }

    #[test]
    fn byte_equal_non_ascii_strings_are_equal() {
        // Trivially-equal non-ASCII strings don't need case folding;
        // we shouldn't bail on them.
        assert_eq!(
            evaluate("'café' == 'café'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("'café' != 'café'", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn non_byte_equal_non_ascii_strings_are_unsupported() {
        // MSBuild's ordinal-ignore-case fold would handle 'É' vs 'é'
        // correctly; our `eq_ignore_ascii_case` would silently return
        // false. Bail to Unsupported rather than flip the gate on
        // case differences we can't fold.
        assert_eq!(
            evaluate("'É' == 'é'", &PropertyMap::new()),
            Outcome::Unsupported
        );
        // Same handling for !=: we can't decide either way.
        assert_eq!(
            evaluate("'É' != 'é'", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn mixed_ascii_and_non_ascii_unequal_is_unsupported() {
        // Pure ASCII vs non-ASCII isn't byte-equal; the safe move
        // is still Unsupported, because we have no general way to
        // prove case folding wouldn't bring them together.
        assert_eq!(
            evaluate("'foo' == 'fÖo'", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn unbalanced_paren_is_illegal() {
        assert_eq!(
            evaluate("(true And false", &PropertyMap::new()),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate("true And false)", &PropertyMap::new()),
            Outcome::Illegal
        );
    }

    // --- HasTrailingSlash(...) ---
    //
    // MSBuild's second built-in condition function (after Exists). It
    // expands its single argument into a task item — which trims
    // surrounding whitespace — then reports whether the last character is
    // `/` or `\`. An empty result is false; a multi-item (`;`) argument is
    // a project error. Every case pinned against `dotnet msbuild` 10.0.300.

    #[test]
    fn has_trailing_slash_checks_last_character() {
        assert_eq!(
            evaluate("HasTrailingSlash('a/')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash('a\\')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash('a')", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("HasTrailingSlash('')", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn has_trailing_slash_trims_expanded_argument() {
        // The argument goes through item-spec expansion, which trims
        // surrounding whitespace before the last-character check.
        assert_eq!(
            evaluate("HasTrailingSlash(' a/ ')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash(' /a ')", &PropertyMap::new()),
            Outcome::False
        );
        assert_eq!(
            evaluate("HasTrailingSlash('   ')", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn has_trailing_slash_expands_and_negates() {
        let p = props(&[("OutDir", "bin/Debug/")]);
        assert_eq!(evaluate("HasTrailingSlash('$(OutDir)')", &p), Outcome::True);
        assert_eq!(
            evaluate("!HasTrailingSlash('$(OutDir)')", &p),
            Outcome::False
        );
        let p = props(&[("OutDir", "bin/Debug")]);
        assert_eq!(
            evaluate("'$(OutDir)' != '' and !HasTrailingSlash('$(OutDir)')", &p),
            Outcome::True
        );
    }

    #[test]
    fn has_trailing_slash_reports_undefined_argument() {
        let eval = super::evaluate("HasTrailingSlash('$(Missing)')", &PropertyMap::new());
        assert_eq!(eval.outcome, Outcome::False);
        assert_eq!(eval.undefined_properties, vec!["Missing".to_string()]);
    }

    #[test]
    fn has_trailing_slash_multi_item_argument_is_illegal() {
        // Two non-empty items is a project error.
        assert_eq!(
            evaluate("HasTrailingSlash('a/;b')", &PropertyMap::new()),
            Outcome::Illegal
        );
        assert_eq!(
            evaluate("HasTrailingSlash('a;b/')", &PropertyMap::new()),
            Outcome::Illegal
        );
        // .NET's `Trim` is not modelled outside ASCII, so no claim there.
        assert_eq!(
            evaluate("HasTrailingSlash('a;\u{e9}')", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn has_trailing_slash_drops_empty_list_entries() {
        // MSBuild trims each list entry and drops empty ones, so a lone
        // trailing/leading `;` leaves a single decidable item. Pinned
        // against dotnet msbuild 10.0.300.
        assert_eq!(
            evaluate("HasTrailingSlash('a/;')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash(';/')", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(
            evaluate("HasTrailingSlash('a/ ; ')", &PropertyMap::new()),
            Outcome::True
        );
        // All entries empty → no item → no trailing slash.
        assert_eq!(
            evaluate("HasTrailingSlash(';')", &PropertyMap::new()),
            Outcome::False
        );
    }

    #[test]
    fn has_trailing_slash_unquoted_argument_is_unsupported() {
        // Real usage always quotes the argument (`HasTrailingSlash('$(X)')`);
        // a bare-token argument is outside the tight grammar we model.
        assert_eq!(
            evaluate("HasTrailingSlash(abc)", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn item_reference_in_has_trailing_slash_is_unsupported() {
        assert_eq!(
            evaluate("HasTrailingSlash('@(Compile)')", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    // --- bare scalar / property coerced to boolean ---
    //
    // A standalone scalar (property reference, string literal, or bare
    // token) is coerced to bool through MSBuild's boolean vocabulary —
    // `true`/`on`/`yes`/`!false`/… and their negations, case-insensitive.
    // A value outside that vocabulary (`1`, `foo`, the empty string of an
    // unset property) is a project error, so we fail safe to Unsupported.
    // Pinned against `dotnet msbuild` 10.0.300.

    #[test]
    fn bare_property_coerces_to_boolean() {
        assert_eq!(evaluate("$(P)", &props(&[("P", "true")])), Outcome::True);
        assert_eq!(evaluate("$(P)", &props(&[("P", "false")])), Outcome::False);
        assert_eq!(evaluate("$(P)", &props(&[("P", "True")])), Outcome::True);
        // MSBuild's standalone-boolean vocabulary is the same on/yes/off/no
        // set as `==` coercion.
        assert_eq!(evaluate("$(P)", &props(&[("P", "on")])), Outcome::True);
        assert_eq!(evaluate("$(P)", &props(&[("P", "yes")])), Outcome::True);
        assert_eq!(evaluate("$(P)", &props(&[("P", "no")])), Outcome::False);
    }

    #[test]
    fn non_boolean_bare_scalar_is_illegal() {
        // `1` is numeric, not in the boolean vocabulary; a non-bool word
        // and the empty string of an unset property are project errors too.
        assert_eq!(evaluate("$(P)", &props(&[("P", "1")])), Outcome::Illegal);
        assert_eq!(evaluate("$(P)", &props(&[("P", "foo")])), Outcome::Illegal);
        assert_eq!(
            evaluate("$(Missing)", &PropertyMap::new()),
            Outcome::Illegal
        );
        assert_eq!(evaluate("'foo'", &PropertyMap::new()), Outcome::Illegal);
        // Outside ASCII, `OrdinalIgnoreCase` folds letters ASCII folding does
        // not (`ſ` is an `s`), so no claim.
        assert_eq!(
            evaluate("$(P)", &props(&[("P", "ye\u{17f}")])),
            Outcome::Unsupported
        );
    }

    #[test]
    fn bang_negates_coerced_bare_scalar() {
        assert_eq!(evaluate("!$(P)", &props(&[("P", "false")])), Outcome::True);
        assert_eq!(evaluate("!$(P)", &props(&[("P", "true")])), Outcome::False);
    }

    #[test]
    fn string_literal_coerces_to_boolean() {
        assert_eq!(evaluate("'true'", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("'on'", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("'$(P)'", &props(&[("P", "true")])), Outcome::True);
    }

    #[test]
    fn bare_word_boolean_literals_are_supported() {
        // MSBuild's boolean vocabulary works as bare (unquoted) condition
        // words, not just `true`/`false`. Pinned against dotnet msbuild
        // 10.0.300.
        assert_eq!(evaluate("on", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("yes", &PropertyMap::new()), Outcome::True);
        assert_eq!(evaluate("off", &PropertyMap::new()), Outcome::False);
        assert_eq!(evaluate("no", &PropertyMap::new()), Outcome::False);
        assert_eq!(evaluate("!off", &PropertyMap::new()), Outcome::True);
        // A non-boolean bare word is a project error.
        assert_eq!(evaluate("maybe", &PropertyMap::new()), Outcome::Illegal);
    }

    #[test]
    fn bare_word_is_a_string_comparison_operand() {
        // Unquoted words are simple-string operands, compared like quoted
        // strings (case-insensitive). Pinned against dotnet msbuild 10.0.300.
        assert_eq!(
            evaluate("Release == 'Release'", &PropertyMap::new()),
            Outcome::True
        );
        assert_eq!(evaluate("on == 'x'", &PropertyMap::new()), Outcome::False);
    }

    #[test]
    fn bang_before_comparison_stays_unsupported() {
        // `!'a' == 'b'` binds as `(!'a') == 'b'` in MSBuild, which errors
        // (a bool compared to a string). We must not silently read it as
        // `!('a' == 'b')`.
        assert_eq!(
            evaluate("!'a' == 'b'", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn boolean_literal_as_comparison_operand() {
        // `true`/`false` are usable as unquoted comparison operands on either
        // side, compared through the boolean vocabulary. The .NET SDK
        // container targets gate on `$(X.Contains('-')) == false`. Pinned
        // against dotnet msbuild 10.0.300.
        assert_eq!(
            evaluate("$(P) == false", &props(&[("P", "False")])),
            Outcome::True
        );
        assert_eq!(
            evaluate("$(P) == false", &props(&[("P", "True")])),
            Outcome::False
        );
        assert_eq!(
            evaluate("$(P) == true", &props(&[("P", "True")])),
            Outcome::True
        );
        assert_eq!(
            evaluate("false == $(P)", &props(&[("P", "False")])),
            Outcome::True
        );
        assert_eq!(
            evaluate("$(P.Contains('-')) == false", &props(&[("P", "8.0.100")])),
            Outcome::True
        );
    }

    #[test]
    fn whitespace_around_simple_property_reference_is_illegal() {
        // MSBuild rejects a simple property reference with interior
        // whitespace (`$( Foo )`, `$(Foo )`, `$( Foo)`), unlike `$(Foo)`.
        // Committing to `Foo`'s value there would be a wrong gate. Pinned
        // against dotnet msbuild 10.0.300.
        let p = props(&[("Foo", "true")]);
        assert_eq!(evaluate("$(Foo)", &p), Outcome::True);
        assert_eq!(evaluate("$( Foo )", &p), Outcome::Illegal);
        assert_eq!(evaluate("$(Foo )", &p), Outcome::Illegal);
        assert_eq!(evaluate("$( Foo)", &p), Outcome::Illegal);
        assert_eq!(evaluate("$( Foo ) == 'true'", &p), Outcome::Illegal);
        // Property-function forms DO tolerate surrounding whitespace.
        assert_eq!(evaluate("$( Foo.Contains('r') )", &p), Outcome::True);
    }

    #[test]
    fn bare_property_as_comparison_operand() {
        assert_eq!(
            evaluate("$(P) == 'y'", &props(&[("P", "y")])),
            Outcome::True
        );
        assert_eq!(
            evaluate("$(P) != 'y'", &props(&[("P", "x")])),
            Outcome::True
        );
    }

    #[test]
    fn bare_unsupported_property_function_is_unsupported() {
        // A bare `$(...)` that isn't a modelled function still poisons the
        // condition when the substituter can't evaluate it.
        assert_eq!(
            evaluate("$([System.String]::Copy('x'))", &props(&[("X", "y")])),
            Outcome::Unsupported
        );
    }

    #[test]
    fn contains_property_function_in_condition_is_supported() {
        // The motivating F# SDK shape: `!$(V.Contains('{'))`.
        assert_eq!(
            evaluate("!$(P.Contains('{'))", &props(&[("P", "8.0.0")])),
            Outcome::True
        );
        assert_eq!(
            evaluate("!$(P.Contains('{'))", &props(&[("P", "{{x}}")])),
            Outcome::False
        );
    }

    #[test]
    fn contains_receiver_is_tracked_as_non_default_reference() {
        // The receiver of a `.Contains` call is a genuine branch-decision
        // property; an undefined one must surface *outside* the is-it-set
        // exemption so a gate depending on it is treated as uncertain
        // rather than certain.
        // Both the tight and the whitespace-before-`(` spellings must track
        // the receiver (MSBuild accepts both, so the scanner must too).
        for cond in ["$(Missing.Contains('x'))", "$(Missing.Contains ('x'))"] {
            let eval = super::evaluate(cond, &PropertyMap::new());
            assert_eq!(eval.outcome, Outcome::False, "{cond}");
            assert_eq!(
                eval.undefined_properties,
                vec!["Missing".to_string()],
                "{cond}"
            );
            assert_eq!(
                eval.undefined_outside_empty_comparison,
                vec!["Missing".to_string()],
                "{cond}"
            );
        }
    }

    #[test]
    fn raw_item_marker_masked_by_string_method_is_unsupported() {
        // A raw `@(` / `%(` opener in a string-method argument makes MSBuild
        // reject the whole condition at lex time: its scanner lexes item-list
        // (`@(`) and metadata (`%(`) markers straight from the raw condition
        // text, before any property expansion. Reducing `$(V.Contains('@('))`
        // to a bool would consume the marker inside the method and hide it
        // from every later check, letting us commit to a branch MSBuild never
        // reaches. The up-front raw-source marker scan closes that class.
        //
        // The first two MSBuild rejects for another reason: its scanner
        // counts a reference's parentheses without regard to quotes, so a
        // quoted `(` leaves it unclosed. The third it evaluates, in an item's
        // condition at least (oracle-pinned: false).
        for (cond, outcome) in [
            ("$(V.Contains('@('))", Outcome::Illegal),
            ("$(V.StartsWith('%('))", Outcome::Illegal),
            ("$(V.EndsWith('@(x)'))", Outcome::Unsupported),
        ] {
            assert_eq!(evaluate(cond, &props(&[("V", "x")])), outcome, "{cond}");
        }
    }

    #[test]
    fn raw_marker_anywhere_in_condition_is_unsupported() {
        // The scan is not method-specific: any raw item/metadata marker in the
        // source text is Unsupported, whether it sits inside a built-in
        // function argument, a comparison operand string literal, or a
        // metadata reference standing on its own.
        assert_eq!(
            evaluate("HasTrailingSlash('@(x)/')", &PropertyMap::new()),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate("'$(A)' == '@(x)'", &props(&[("A", "y")])),
            Outcome::Unsupported
        );
        assert_eq!(
            evaluate("'%(Identity)' == 'x'", &PropertyMap::new()),
            Outcome::Unsupported
        );
    }

    #[test]
    fn marker_delivered_only_via_substitution_still_commits() {
        // A marker that appears only *after* `$()` substitution is not in the
        // raw source, so the scan leaves it alone — matching MSBuild, which
        // never re-lexes substituted text. Here the `.Contains` needle arrives
        // via `$(N)` and reduces to an ordinary substring test.
        let p = props(&[("V", "a@(b"), ("N", "@(")]);
        assert_eq!(evaluate("$(V.Contains('$(N)'))", &p), Outcome::True);
    }

    #[test]
    fn fsharp_core_maximum_major_version_gate_is_supported() {
        // The exact condition from Microsoft.FSharp.Core.NetSdk.props gating
        // FSharpCoreMaximumMajorVersion. Resolved end-to-end (equality,
        // And, the .Contains property function, and `!` coercion).
        let cond = "'$(FSCorePackageVersionSet)' == 'true' and '$(FSCorePackageVersion)' != '' \
                    and !$(FSCorePackageVersion.Contains('{'))";
        assert_eq!(
            evaluate(
                cond,
                &props(&[
                    ("FSCorePackageVersionSet", "true"),
                    ("FSCorePackageVersion", "8.0.0"),
                ]),
            ),
            Outcome::True
        );
        // The unreplaced token placeholder still contains `{`, so the gate
        // is false (the SDK skips setting the max major version).
        assert_eq!(
            evaluate(
                cond,
                &props(&[
                    ("FSCorePackageVersionSet", "true"),
                    ("FSCorePackageVersion", "{{FSCorePackageVersionValue}}"),
                ]),
            ),
            Outcome::False
        );
    }
}

#[cfg(test)]
mod prop_tests {
    //! Property-based tests for the condition evaluator.
    //!
    //! Strategy: generate a random AST inside our grammar, render it
    //! as a condition string, feed it back through the production
    //! evaluator, and compare against a directly-computed truth
    //! value. This exercises the lexer, parser, and evaluator
    //! end-to-end against a reference implementation that ignores
    //! surface syntax outside literals (token-separating whitespace,
    //! operator casing, parens).
    //!
    //! Restrictions on generated input:
    //!   * String literals contain only "safe" bytes — no `'` (would
    //!     close the literal), no `$` (no substitution semantics to
    //!     test here), no control chars.
    //!   * Tree depth is bounded so generation terminates.
    //!
    //! Coverage instrumentation: every property tracks how often it
    //! observes True vs False outcomes and asserts both regimes are
    //! visited. A property that only ever sees one branch isn't
    //! exploring the space.

    use std::sync::atomic::{AtomicUsize, Ordering};

    use proptest::prelude::*;

    use super::*;

    /// Proptests only care about the truth value; shadow the outer
    /// `evaluate` to drop the undefined-property list so the existing
    /// `prop_assert_eq!(evaluate(...), Outcome::True, ...)` assertions
    /// continue to compile after the signature widening.
    fn evaluate(source: &str, props: &PropertyMap) -> Outcome {
        super::evaluate(source, props).outcome
    }

    /// A node in the reference AST. Exactly mirrors the subset of
    /// MSBuild condition syntax we model — boolean literals, string
    /// equality / inequality, And, Or, parens (parens aren't an AST
    /// node; the renderer adds them around every binary op so the
    /// generated string is unambiguous regardless of precedence).
    #[derive(Debug, Clone)]
    enum Ast {
        BoolLit(bool),
        Eq(String, String),
        Neq(String, String),
        And(Box<Ast>, Box<Ast>),
        Or(Box<Ast>, Box<Ast>),
    }

    /// Reference evaluator. Comparing this against the production
    /// `evaluate` is the whole point — if these disagree, either the
    /// reference is wrong or the production parser/evaluator is.
    fn truth(ast: &Ast) -> bool {
        match ast {
            Ast::BoolLit(b) => *b,
            Ast::Eq(a, b) => reference_equality(a, b),
            Ast::Neq(a, b) => !reference_equality(a, b),
            Ast::And(a, b) => truth(a) && truth(b),
            Ast::Or(a, b) => truth(a) || truth(b),
        }
    }

    /// MSBuild's `==` dispatch (empty → numeric → boolean → string),
    /// restated over the operand strings directly. The *scalar* parsers are
    /// deliberately the production ones — their semantics are pinned
    /// separately by the unit tests verified against `dotnet msbuild` — so
    /// this property's job is the surrounding pipeline: rendering,
    /// tokenising, parsing, and evaluation-order must land every operand
    /// pair in this same comparison.
    fn reference_equality(lhs: &str, rhs: &str) -> bool {
        if lhs.is_empty() || rhs.is_empty() {
            return lhs.is_empty() && rhs.is_empty();
        }
        if let (Some(lhs), Some(rhs)) = (
            super::parse_msbuild_number(lhs),
            super::parse_msbuild_number(rhs),
        ) {
            return lhs == rhs;
        }
        if let (Some(lhs), Some(rhs)) = (
            super::parse_msbuild_bool(lhs),
            super::parse_msbuild_bool(rhs),
        ) {
            return lhs == rhs;
        }
        lhs.eq_ignore_ascii_case(rhs)
    }

    /// Render an AST as a condition string. We wrap every binary op
    /// in parens — that way the round-trip property doesn't depend on
    /// our precedence implementation matching the renderer's
    /// assumption. Precedence is tested separately by the unit tests
    /// above.
    fn render(ast: &Ast) -> String {
        match ast {
            Ast::BoolLit(true) => "true".into(),
            Ast::BoolLit(false) => "false".into(),
            Ast::Eq(a, b) => format!("'{a}' == '{b}'"),
            Ast::Neq(a, b) => format!("'{a}' != '{b}'"),
            Ast::And(a, b) => format!("({} And {})", render(a), render(b)),
            Ast::Or(a, b) => format!("({} Or {})", render(a), render(b)),
        }
    }

    /// Generate string-literal contents that won't break the lexer:
    /// no `'` (closes the literal early), no `$` (would introduce
    /// substitution semantics we test separately), and only printable
    /// ASCII — control chars wouldn't add coverage but might trip
    /// the lexer's byte-classification helpers.
    ///
    /// Each character is drawn *directly* from its valid byte range rather
    /// than `any::<u8>().prop_filter(is_ascii_digit)`: a filter over the full
    /// 0–255 byte space rejects ~96% of draws for digits (10/256) and ~80%
    /// for letters (52/256). proptest counts those rejects against the
    /// per-test `max_local_rejects` budget (default 65536), and across a
    /// `cases`-sized run the cumulative count sits right at that boundary —
    /// so a slightly unlucky seed tips it over and the test aborts with
    /// "Too many local rejects". Range strategies never reject, removing the
    /// flake. (See proptest's `RangeInclusive<u8> as Strategy`.)
    fn arb_safe_str() -> impl Strategy<Value = String> {
        prop::collection::vec(
            prop_oneof![
                // Letters (mixed case so we exercise the
                // case-insensitive comparison path)
                prop_oneof![b'A'..=b'Z', b'a'..=b'z'],
                // Digits
                b'0'..=b'9',
                // A small set of safe punctuation. Excluding `'`, `$`,
                // `(`, `)` (these are operators in our grammar — would
                // confuse the lexer if they sat inside a string literal
                // and the literal then participated in concatenation).
                // Actually the lexer doesn't tokenise inside `'...'`, so
                // these are fine — but keeping the list small keeps test
                // failures readable.
                Just(b'_'),
                Just(b'-'),
                Just(b'.'),
                Just(b'/'),
                Just(b' '),
            ],
            0..8usize,
        )
        .prop_map(|bytes| String::from_utf8(bytes).expect("ASCII-only"))
    }

    fn arb_ast() -> impl Strategy<Value = Ast> {
        // Leaf strategies are cheap; branching strategies multiply
        // by ~4 per level. Cap depth at 4 so each test case stays
        // small enough to debug if a counterexample is found.
        let leaf = prop_oneof![
            any::<bool>().prop_map(Ast::BoolLit),
            (arb_safe_str(), arb_safe_str()).prop_map(|(a, b)| Ast::Eq(a, b)),
            (arb_safe_str(), arb_safe_str()).prop_map(|(a, b)| Ast::Neq(a, b)),
        ];
        leaf.prop_recursive(4, 32, 2, |inner| {
            prop_oneof![
                (inner.clone(), inner.clone())
                    .prop_map(|(a, b)| Ast::And(Box::new(a), Box::new(b))),
                (inner.clone(), inner).prop_map(|(a, b)| Ast::Or(Box::new(a), Box::new(b))),
            ]
        })
    }

    fn arb_valid_msbuild_version_operand() -> impl Strategy<Value = String> {
        (
            prop_oneof![Just(""), Just("v"), Just("V")],
            prop::collection::vec(0u32..=99, 1..=4usize),
            prop_oneof![
                Just("".to_string()),
                "[A-Za-z][A-Za-z0-9]*(\\.[0-9]{1,2}){0,2}".prop_map(|s| format!("-{s}")),
                "[A-Za-z][A-Za-z0-9]*(\\.[0-9]{1,2}){0,2}".prop_map(|s| format!("-{s}+metadata")),
                Just("+metadata".to_string()),
            ],
        )
            .prop_map(|(prefix, parts, suffix)| {
                let numeric = parts
                    .into_iter()
                    .map(|part| part.to_string())
                    .collect::<Vec<_>>()
                    .join(".");
                format!("{prefix}{numeric}{suffix}")
            })
    }

    fn arb_invalid_msbuild_version_operand() -> impl Strategy<Value = String> {
        prop_oneof![
            prop::collection::vec(0u32..=99, 5..=7usize).prop_map(|parts| {
                parts
                    .into_iter()
                    .map(|part| part.to_string())
                    .collect::<Vec<_>>()
                    .join(".")
            }),
            (0usize..4, 2_147_483_648u64..=2_147_483_700u64).prop_map(
                |(bad_idx, bad_component)| {
                    let mut parts = [1u64, 2, 3, 4];
                    parts[bad_idx] = bad_component;
                    parts
                        .into_iter()
                        .map(|part| part.to_string())
                        .collect::<Vec<_>>()
                        .join(".")
                },
            ),
            (0u32..=99).prop_map(|major| format!("vv{major}")),
            (0u32..=99, 0u32..=99).prop_map(|(major, minor)| format!("{major}..{minor}")),
        ]
    }

    fn arb_equivalent_decimal_literals() -> impl Strategy<Value = (String, String)> {
        prop_oneof![
            (0u32..=10_000, 0usize..=3, 0usize..=3, 0usize..=3).prop_map(
                |(number, lhs_leading, rhs_leading, rhs_trailing)| {
                    let lhs = format!("{}{}", "0".repeat(lhs_leading), number);
                    let mut rhs = format!("{}{}", "0".repeat(rhs_leading), number);
                    if rhs_trailing > 0 {
                        rhs.push('.');
                        rhs.push_str(&"0".repeat(rhs_trailing));
                    }
                    (lhs, rhs)
                },
            ),
            (0u32..=1_000, 1u32..=999, 0usize..=3, 0usize..=3, 0usize..=3,).prop_map(
                |(whole, fraction, lhs_leading, rhs_leading, extra_trailing)| {
                    let fraction = format!("{fraction:03}");
                    let lhs = format!("{}{}.{}", "0".repeat(lhs_leading), whole, fraction);
                    let rhs = format!(
                        "{}{}.{}{}",
                        "0".repeat(rhs_leading),
                        whole,
                        fraction,
                        "0".repeat(extra_trailing)
                    );
                    (lhs, rhs)
                },
            ),
        ]
    }

    /// Expand existing whitespace runs and pad both ends of a
    /// rendered condition string. We deliberately do NOT insert
    /// whitespace at new positions: separating `==` into `= =` or
    /// splitting an identifier in half would actually change
    /// tokenisation, and that's not the claim being tested. The
    /// renderer already places single spaces between every
    /// token-distinct pair (because the binary-op syntax dictates
    /// it), so widening those runs exercises the lexer's
    /// "whitespace runs are insignificant" behaviour without
    /// re-tokenising the input. Whitespace inside `'...'` literals
    /// IS significant (preserves the string value), so we copy them
    /// verbatim.
    fn pad_whitespace(s: &str) -> String {
        let mut out = String::with_capacity(s.len() * 2);
        let mut in_string = false;
        for c in s.chars() {
            if in_string {
                out.push(c);
                if c == '\'' {
                    in_string = false;
                }
                continue;
            }
            if c == '\'' {
                in_string = true;
                out.push(c);
                continue;
            }
            if c.is_whitespace() {
                out.push(' ');
                out.push(' ');
            } else {
                out.push(c);
            }
        }
        format!("  {}  ", out)
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 512,
            ..ProptestConfig::default()
        })]

        /// Generated AST renders to a string whose evaluated outcome
        /// matches the reference truth value. End-to-end check of
        /// lex → parse → eval.
        #[test]
        fn render_eval_matches_reference_truth(ast in arb_ast()) {
            let rendered = render(&ast);
            let expected = truth(&ast);
            let got = evaluate(&rendered, &PropertyMap::new());
            let expected_outcome = if expected { Outcome::True } else { Outcome::False };
            // Surface the rendered form on failure so a counterexample
            // is actionable without re-rendering by hand.
            prop_assert_eq!(
                got, expected_outcome,
                "mismatch on rendered condition {:?}", rendered
            );
            // Track distribution so a degenerate generator can't
            // satisfy the property by always producing the same
            // branch.
            if expected {
                TRUTH_TRUE.fetch_add(1, Ordering::Relaxed);
            } else {
                TRUTH_FALSE.fetch_add(1, Ordering::Relaxed);
            }
        }

        /// Random whitespace between tokens must not change the
        /// outcome. Pinned separately because whitespace handling is
        /// the easiest lexer bug to hide.
        #[test]
        fn whitespace_padding_is_insignificant(ast in arb_ast()) {
            let rendered = render(&ast);
            let padded = pad_whitespace(&rendered);
            let lhs = evaluate(&rendered, &PropertyMap::new());
            let rhs = evaluate(&padded, &PropertyMap::new());
            prop_assert_eq!(
                lhs, rhs,
                "whitespace changed outcome: original {:?} padded {:?}", rendered, padded
            );
        }

        /// `'x' == 'x'` is true for every safe string. Tests the
        /// reflexivity of string equality and that the lexer
        /// preserves literal contents end-to-end.
        #[test]
        fn equality_is_reflexive(s in arb_safe_str()) {
            let cond = format!("'{s}' == '{s}'");
            prop_assert_eq!(evaluate(&cond, &PropertyMap::new()), Outcome::True,
                "reflexivity violated for {:?}", s);
        }

        /// MSBuild documents string `==` as case-insensitive.
        /// Compare a string against its uppercase form: must equal.
        #[test]
        fn equality_is_case_insensitive(s in arb_safe_str()) {
            let upper = s.to_ascii_uppercase();
            let cond = format!("'{s}' == '{upper}'");
            prop_assert_eq!(evaluate(&cond, &PropertyMap::new()), Outcome::True,
                "case-insensitive equality violated for {:?} vs {:?}", s, upper);
        }

        /// The MSBuild version helper functions compare missing Build/Revision
        /// components as zero, but their operands still have to fit
        /// System.Version's shape and component range: MSBuild throws on one
        /// that does not (each family probed, msbuild-condition-oracle, SDK
        /// 10.0.401; `rejection_generative_diff` grades the claim).
        #[test]
        fn msbuild_version_functions_reject_generated_invalid_operands(
            invalid in arb_invalid_msbuild_version_operand(),
            valid in arb_valid_msbuild_version_operand(),
        ) {
            let invalid_lhs =
                format!("$([MSBuild]::VersionGreaterThan('{invalid}', '{valid}'))");
            prop_assert_eq!(
                evaluate(&invalid_lhs, &PropertyMap::new()),
                Outcome::Illegal,
                "invalid lhs operand was accepted in {:?}",
                invalid_lhs,
            );

            let invalid_rhs =
                format!("$([MSBuild]::VersionLessThan('{valid}', '{invalid}'))");
            prop_assert_eq!(
                evaluate(&invalid_rhs, &PropertyMap::new()),
                Outcome::Illegal,
                "invalid rhs operand was accepted in {:?}",
                invalid_rhs,
            );
        }

        #[test]
        fn decimal_equality_normalizes_equivalent_spellings(
            (lhs, rhs) in arb_equivalent_decimal_literals(),
        ) {
            let eq = format!("'{lhs}' == '{rhs}'");
            prop_assert_eq!(
                evaluate(&eq, &PropertyMap::new()),
                Outcome::True,
                "equivalent decimals did not compare equal in {:?}",
                eq,
            );

            let neq = format!("{lhs} != {rhs}");
            prop_assert_eq!(
                evaluate(&neq, &PropertyMap::new()),
                Outcome::False,
                "equivalent bare decimals compared not-equal in {:?}",
                neq,
            );
        }

        /// The condition language is case-insensitive end-to-end — keywords,
        /// property-function type/member names, version prefixes, boolean
        /// vocabulary. Randomly flipping the case of any letters in a
        /// version-function condition must not change the outcome.
        #[test]
        fn version_function_casing_is_insignificant(
            lhs in arb_valid_msbuild_version_operand(),
            rhs in arb_valid_msbuild_version_operand(),
            function in prop::sample::select(&[
                "VersionGreaterThanOrEquals",
                "VersionGreaterThan",
                "VersionLessThanOrEquals",
                "VersionLessThan",
                "VersionEquals",
                "VersionNotEquals",
            ][..]),
            flips in prop::collection::vec(any::<bool>(), 128),
        ) {
            let canonical =
                format!("$([MSBuild]::{function}('{lhs}', '{rhs}'))");
            let mutated: String = canonical
                .chars()
                .zip(flips.iter().cycle())
                .map(|(c, flip)| {
                    if *flip {
                        if c.is_ascii_lowercase() {
                            c.to_ascii_uppercase()
                        } else {
                            c.to_ascii_lowercase()
                        }
                    } else {
                        c
                    }
                })
                .collect();
            prop_assert_eq!(
                evaluate(&canonical, &PropertyMap::new()),
                evaluate(&mutated, &PropertyMap::new()),
                "casing changed outcome: {:?} vs {:?}", canonical, mutated
            );
        }
    }

    // Coverage counters live at module scope (proptest can't share
    // mutable state across cases inside the macro). We tally outcomes
    // as the round-trip property runs, then a separate harness test
    // checks the tally meets a minimum balance so a degenerate
    // generator can't pass by always producing one branch.
    static TRUTH_TRUE: AtomicUsize = AtomicUsize::new(0);
    static TRUTH_FALSE: AtomicUsize = AtomicUsize::new(0);

    /// Coverage assertion: the round-trip property must visit both
    /// truth-value regimes a non-trivial number of times. With 512
    /// cases and a roughly-balanced generator, observing fewer than
    /// 16 of either side is overwhelmingly improbable (well below
    /// 1e-11 even under pessimistic models of the generator). If
    /// this trips, the AST generator has skewed and the property
    /// isn't really exploring the space.
    #[test]
    fn round_trip_property_observed_both_outcomes() {
        // Force the round-trip property to actually run before this
        // assertion fires. Proptest runs tests in arbitrary order;
        // by re-invoking the same evaluator with a trivially-true
        // and trivially-false expression we ensure the counters
        // can't be zero just because of run ordering.
        for _ in 0..16 {
            if evaluate("true", &PropertyMap::new()) == Outcome::True {
                TRUTH_TRUE.fetch_add(1, Ordering::Relaxed);
            }
            if evaluate("false", &PropertyMap::new()) == Outcome::False {
                TRUTH_FALSE.fetch_add(1, Ordering::Relaxed);
            }
        }
        let t = TRUTH_TRUE.load(Ordering::Relaxed);
        let f = TRUTH_FALSE.load(Ordering::Relaxed);
        assert!(
            t >= 16 && f >= 16,
            "coverage too skewed: {t} true / {f} false — generator is not exploring both branches"
        );
    }
}

#[cfg(test)]
mod decide_without_props {
    //! [`decide_without`] held to [`evaluate`], which the unit tests above
    //! hold to `dotnet msbuild`. Conditions are generated over two trusted
    //! properties (`A`, `B`) and two untrusted ones (`U`, `V`); a verdict of
    //! [`Decision::Decided`] is checked against `evaluate` under *every*
    //! assignment of the untrusted pair from a value alphabet that spans
    //! MSBuild's comparison dispatch (empty, numbers, versions, booleans,
    //! strings) plus "undefined".

    use std::sync::atomic::{AtomicUsize, Ordering};

    use proptest::prelude::*;

    use super::*;

    const VALUES: &[&str] = &[
        "", "true", "false", "1", "1.0", "2.0.1", "net10.0", "x", "On",
    ];
    const TRUSTED: &[&str] = &["A", "B"];
    const UNTRUSTED: &[&str] = &["U", "V"];

    fn is_untrusted(name: &str) -> bool {
        UNTRUSTED.iter().any(|u| u.eq_ignore_ascii_case(name))
    }

    fn operand() -> impl Strategy<Value = String> {
        let names: Vec<&str> = TRUSTED.iter().chain(UNTRUSTED).copied().collect();
        prop_oneof![
            prop::sample::select(VALUES).prop_map(|v| format!("'{v}'")),
            prop::sample::select(names.clone()).prop_map(|n| format!("'$({n})'")),
            prop::sample::select(names.clone()).prop_map(|n| format!("'x$({n})'")),
            prop::sample::select(names.clone()).prop_map(|n| format!("$({n})")),
            // Property functions, which may throw on their receiver.
            prop::sample::select(names.clone()).prop_map(|n| format!("'$({n}.Substring(1))'")),
            prop::sample::select(names).prop_map(|n| format!("'$({n}.Trim())'")),
        ]
    }

    fn leaf() -> impl Strategy<Value = String> {
        prop_oneof![
            Just("true".to_string()),
            Just("false".to_string()),
            (
                operand(),
                prop::sample::select(&["==", "!=", "<", ">=", "=="][..]),
                operand()
            )
                .prop_map(|(l, op, r)| format!("{l} {op} {r}")),
            operand(),
        ]
    }

    fn condition() -> impl Strategy<Value = String> {
        leaf().prop_recursive(4, 24, 3, |inner| {
            prop_oneof![
                inner.clone().prop_map(|c| format!("!({c})")),
                prop::collection::vec(inner.clone(), 2..4)
                    .prop_map(|cs| format!("({})", cs.join(" And "))),
                prop::collection::vec(inner, 2..4).prop_map(|cs| format!("({})", cs.join(" Or "))),
            ]
        })
    }

    /// `None` is "undefined".
    fn value_choice() -> impl Strategy<Value = Option<&'static str>> {
        prop_oneof![Just(None), prop::sample::select(VALUES).prop_map(Some)]
    }

    fn map(assignment: &[(&str, Option<&str>)]) -> PropertyMap {
        let mut props = PropertyMap::new();
        for (name, value) in assignment {
            if let Some(value) = value {
                props.insert(*name, *value);
            }
        }
        props
    }

    static CASES: AtomicUsize = AtomicUsize::new(0);
    static DECIDED_DESPITE_UNTRUSTED: AtomicUsize = AtomicUsize::new(0);

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2048))]

        #[test]
        fn decided_means_every_untrusted_value_agrees(
            source in condition(),
            a in value_choice(),
            b in value_choice(),
            u in value_choice(),
            v in value_choice(),
        ) {
            let base = map(&[("A", a), ("B", b), ("U", u), ("V", v)]);
            let decision = decide_without(&source, &base, None, crate::condition::Site::ItemPass, &is_untrusted);
            CASES.fetch_add(1, Ordering::Relaxed);
            let Decision::Decided(decided) = decision else {
                return Ok(());
            };
            let mentions_untrusted = UNTRUSTED.iter().any(|u| source.contains(&format!("$({u})")));
            if mentions_untrusted {
                DECIDED_DESPITE_UNTRUSTED.fetch_add(1, Ordering::Relaxed);
            }
            for u in std::iter::once(None).chain(VALUES.iter().copied().map(Some)) {
                for v in std::iter::once(None).chain(VALUES.iter().copied().map(Some)) {
                    let props = map(&[("A", a), ("B", b), ("U", u), ("V", v)]);
                    let outcome = evaluate(&source, &props).outcome;
                    let agrees = match outcome {
                        Outcome::True => decided,
                        Outcome::False => !decided,
                        // A rejected condition is a project error in MSBuild, and an
                        // unmodelled one may be.
                        Outcome::Illegal | Outcome::Unsupported | Outcome::StartupDirectory => true,
                    };
                    prop_assert!(
                        agrees,
                        "{source}: decided {decided}, but U={u:?} V={v:?} gives {outcome:?}"
                    );
                }
            }
        }

        /// With nothing untrusted, deciding is evaluating.
        #[test]
        fn nothing_untrusted_is_plain_evaluation(
            source in condition(),
            a in value_choice(),
            b in value_choice(),
            u in value_choice(),
            v in value_choice(),
        ) {
            let props = map(&[("A", a), ("B", b), ("U", u), ("V", v)]);
            let decision = decide_without(&source, &props, None, crate::condition::Site::ItemPass, &|_| false);
            let expected = match evaluate(&source, &props).outcome {
                Outcome::True => Decision::Decided(true),
                Outcome::False => Decision::Decided(false),
                Outcome::Illegal | Outcome::Unsupported => Decision::Unsupported,
                Outcome::StartupDirectory => Decision::Depends,
            };
            prop_assert_eq!(decision, expected, "{}", source);
        }
    }

    static JUDGED: AtomicUsize = AtomicUsize::new(0);
    static MAYBE_THROWS_BOTH_WAYS: AtomicUsize = AtomicUsize::new(0);
    static NEVER_THROWS_DESPITE_UNTRUSTED: AtomicUsize = AtomicUsize::new(0);

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2048))]

        /// `judge` held to [`evaluate`] under every assignment of the
        /// untrusted pair: its value is evaluation's wherever evaluation
        /// gives a boolean; it never says MSBuild cannot throw where an
        /// assignment makes evaluation throw; and it says MSBuild throws
        /// for certain only where every assignment does.
        #[test]
        fn judgement_holds_of_every_untrusted_value(
            source in condition(),
            a in value_choice(),
            b in value_choice(),
            u in value_choice(),
            v in value_choice(),
        ) {
            let base = map(&[("A", a), ("B", b), ("U", u), ("V", v)]);
            // Whether the judgement asked about an untrusted name it reached.
            let reached_untrusted = std::cell::Cell::new(false);
            let judged = judge(&source, &base, None, crate::condition::Site::ItemPass, &|name: &str| {
                let is = is_untrusted(name);
                reached_untrusted.set(reached_untrusted.get() || is);
                is
            });
            JUDGED.fetch_add(1, Ordering::Relaxed);
            // The possibility-only walk agrees with the full judgement, and
            // the certainty-only walk claims a certain throw only where the
            // full judgement does.
            prop_assert_eq!(
                may_throw(&source, &base, None, crate::condition::Site::ItemPass, &is_untrusted),
                judged.throws != Throws::Never,
                "{}",
                source
            );
            prop_assert!(
                !throws_whatever(&source, &base, None, crate::condition::Site::ItemPass, &is_untrusted)
                    || judged.throws == Throws::Certainly,
                "{}",
                source
            );
            let (mut threw, mut held) = (false, false);
            for u in std::iter::once(None).chain(VALUES.iter().copied().map(Some)) {
                for v in std::iter::once(None).chain(VALUES.iter().copied().map(Some)) {
                    let props = map(&[("A", a), ("B", b), ("U", u), ("V", v)]);
                    let outcome = evaluate(&source, &props).outcome;
                    match outcome {
                        Outcome::True | Outcome::False => {
                            held = true;
                            let value = outcome == Outcome::True;
                            prop_assert!(
                                judged.value.is_none_or(|judged| judged == value),
                                "{source}: judged {judged:?}, but U={u:?} V={v:?} gives {value}"
                            );
                            prop_assert_ne!(
                                judged.throws,
                                Throws::Certainly,
                                "{}: U={:?} V={:?} gives {}",
                                source,
                                u,
                                v,
                                value
                            );
                        }
                        Outcome::Illegal => {
                            threw = true;
                            prop_assert_ne!(
                                judged.throws,
                                Throws::Never,
                                "{}: U={:?} V={:?} throws",
                                source,
                                u,
                                v
                            );
                        }
                        Outcome::Unsupported | Outcome::StartupDirectory => {}
                    }
                }
            }
            if judged.throws == Throws::Maybe && threw && held {
                MAYBE_THROWS_BOTH_WAYS.fetch_add(1, Ordering::Relaxed);
            }
            if judged.throws == Throws::Never && !judged.unevaluated && reached_untrusted.get() && held {
                NEVER_THROWS_DESPITE_UNTRUSTED.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    /// [`judgement_holds_of_every_untrusted_value`] holds vacuously unless
    /// both of its throw verdicts meet conditions that read an untrusted
    /// property: one that throws on some values and not others, and one that
    /// throws on none.
    #[test]
    fn judging_despite_untrusted_operands_is_exercised() {
        judgement_holds_of_every_untrusted_value();
        let cases = JUDGED.load(Ordering::Relaxed);
        let maybe = MAYBE_THROWS_BOTH_WAYS.load(Ordering::Relaxed);
        let never = NEVER_THROWS_DESPITE_UNTRUSTED.load(Ordering::Relaxed);
        assert!(
            maybe * 50 >= cases,
            "only {maybe} of {cases} cases may throw both ways"
        );
        assert!(
            never * 100 >= cases,
            "only {never} of {cases} cases read an untrusted property and cannot throw"
        );
    }

    /// The soundness property above holds vacuously if nothing that mentions
    /// an untrusted property is ever decided; this is what keeps it honest.
    #[test]
    fn deciding_despite_untrusted_operands_is_exercised() {
        decided_means_every_untrusted_value_agrees();
        let cases = CASES.load(Ordering::Relaxed);
        let decided = DECIDED_DESPITE_UNTRUSTED.load(Ordering::Relaxed);
        assert!(
            decided * 20 >= cases,
            "only {decided} of {cases} cases decided a condition that mentions an \
             untrusted property"
        );
    }
}
