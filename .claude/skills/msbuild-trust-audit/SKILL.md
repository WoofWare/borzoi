---
name: msbuild-trust-audit
description: How to decide whether an MSBuild-evaluated value may be trusted, and the complete twelve-entry checklist an item capture must consult before committing to a value. Use when adding or changing a consumer of a `borzoi-msbuild` evaluated item or property (ProjectReference edges, TargetFramework, output-file names, DefineConstants), when adding a `*_uncertain` flag or any trust gate, and when a reviewer flags one untrusted gate or value flow — audit all twelve entries in that one round instead of patching the one.
---

# Trusting an MSBuild-evaluated value

Two distinct jobs, often confused:

- **Reference semantics** — "this value locates a file / names an edge". The
  generic seam `ParsedProject::property(name)` is the right signal: it returns
  a `PropertyRead`, and only `Value` (a trusted value) and `Unset` (undefined
  in the real build too) are the real build's answer. Match all four variants:
  `UnsetInexact(Refused)` is a write the walk could not compute, which a
  consumer reading a missing key as "never written" gets wrong (#780).
- **Fold gates** — "refuse to analyse this project at all". The generic seam is
  **unusable** here alone. See §2.

## 1. The twelve-entry item-trust checklist

When making a captured MSBuild item list trustworthy, *every* one of these must
consult trust state. A reviewer finds exactly one missing entry per round; each
looks like a one-off and is the same family. Sweep all twelve at once.

1. The element's own `Condition` — **both directions**: an untrusted-false may
   skip a mutation that really runs; an untrusted-true may capture a phantom
   `Include`.
2. The enclosing `<ItemGroup>`'s `Condition` — same two directions.
3. Undecided `<Choose>` / `<When>` branches — mutations in still-possible branches.
4. `<Import>` / `<ImportGroup>` gates, and unresolved or failed imports.
5. `<ItemDefinitionGroup>` metadata defaults — these apply to **all** items
   regardless of document order (pass 2 precedes pass 3).
6. The `Include` **value** expansion. `Expansion::had_issue()` deliberately
   excludes `unpinned_root`, so a cleanly-expanded but unpinned value must be
   checked explicitly: `expansion.unpinned_root` + `raw_uses_sdk_package_taint`.
7. The `Exclude` **value** expansion — the same check as `Include`. (An untrusted
   `$(Skip)` expanding to empty keeps an edge the real build strips.) Shared
   helper: `taint_reference_list_on_untrusted_value`.
8. Metadata **gates** (both directions) and metadata **values**, in both the
   child-element and attribute forms — and case-variant duplicate attributes are
   last-write-wins (`rfind`, not `find`).
9. Metadata **names** you don't model but the consuming protocol treats as
   significant. For `ProjectReference`: `BuildReference`, `Targets`, and the
   `Set*` / property-list mutators. Unrecognised names are inert (probed), so
   this is a closed deny-list, not a catch-all.
10. **Metadata-only `<Compile Update="…">`.** It is skipped wholesale at the
    compile-order seam because it cannot change the item *set* — but it does
    change item *metadata*, whatever the document order and whichever items the
    spec reaches, and it overwrites a value the element declared as readily as
    an absent one (probed, dotnet 10.0.301). So any metadatum you publish must
    decline once one of these carrying that name has been seen. This is the
    same family as entry 5 seen from the other side: 5 is the default that
    arrives before the item, 10 is the mutation that arrives after it, and both
    are invisible to a reader that only inspects the declaring element.
    `ResolvedItem::link` shipped wrong on exactly this; a generative sweep
    reported **228** wrong commits from an axis its author had not thought to
    generate, across this entry, entry 5, and an `<ItemGroup Condition>` route
    to both. The field was ultimately **deleted** — nothing read it — which is
    the other lesson: before paying for a trust verdict on a published value,
    check that the value has a consumer. A metadatum nothing reads is cheaper
    to remove than to make honest.
11. Any **property the consumer locates artifacts by**. The output *file* name is
    `$(TargetName)` (defaulting to `$(AssemblyName)`; padding is preserved
    verbatim in the filename — probed), exposed as `ParsedProject::target_name`
    with `ItemMetadataValue` trust semantics. NuGet's assets record the
    **AssemblyName** stem, *not* TargetName, so the graph-evaluated name must
    out-rank the assets name when locating files. Likewise a body
    `TargetFramework` written under an untrusted gate must not become
    `NodeTfm::Known` — but the outer-gated **plural** (the arcade idiom) is
    unpinned by construction and must stay trusted, because the TFM-invariant
    intersection never believes a single branch anyway.
12. **A project MSBuild may reject** (`ParsedProject::rejection`, #820, #845,
    #783): an import that loads nothing, or a condition MSBuild throws on.
    MSBuild rejection is total: nothing the walk bound, before the failing
    construct or after it, is the build's. A `Certain` rejection and a
    `Possible` one withdraw alike; `Certain` is only a claim the differentials
    grade (and the LSP's error on the `.fsproj`), so never gate a commit on
    `Certain` alone. The evaluator withdraws what has a
    trust channel (every `property()` read, the four `*_uncertain` flags,
    `target_name`, `hidden_content`), but the trust-blind fields
    (`properties`, `target_frameworks`, `lang_version`, `other_flags`,
    `define_constants`, `items`) keep the walk's values. A consumer that
    commits to one of those must gate on `rejection`, or on the flag or read
    the withdrawal sets; one that serves a best guess (the single-file
    `LangVersion`) may read it. A field added to `ParsedProject` joins one
    list or the other, in `rejection`'s docs and in `State::into_project`.

**Rule of thumb:** if a consumer starts reading a new evaluated property with
reference semantics, give it the same Known/Unknown verdict, or the next review
round will.

### MSBuild booleans

Boolean-valued metadata is compared with MSBuild `==` semantics, not string
equality. `ReferenceOutputAssembly` is `'v' == 'true'` after empty→true, so
`on` / `yes` / `!false` are **true**, and `0` / `1` / padded spellings are
**not** (probed dotnet 10.0.301). Use `borzoi_msbuild::msbuild_boolean`. Never
model an MSBuild boolean as `eq_ignore_ascii_case("true")`.

Trust policy, as pinned by tests: cleanly-decided conditions over never-written
properties are exact (the environment model); unsupported grammar, unpinned
properties, and SDK-tainted reads are not. `Choose` gates are stricter — any
diagnostic undecides. The catalogue lives in the
`ParsedProject::project_references_uncertain` docs.

A condition is judged by what its **outcome depends on**, not by what it
mentions: `State::condition_trust` / `condition_is_decided_exactly` run
`condition::decide_without` (three-valued, leaf-wise), so
`'$(Off)' == 'true' And '$(Untrusted)' == 'x'` is exactly false when `Off` is
trusted — but only while the walk has hidden nothing (`walk_opaque` is
`None`). After an undecided import, any held value may have been rewritten
unseen (directly, by a copy of a stale value, ...). The value records that
itself: each opacity latch marks every bound value stale (`Trust::stale`;
reserved names and caller globals excepted), and a value computed from a stale
one inherits it. This decision does not consume it, so nothing settles
an unknown operand after opacity. Don't reopen that boundary with a clock or a
per-name timestamp: codex took four rounds to walk it, and if this decision
ever consumes staleness, the per-value mark is where it reads it. On a
real SDK an untrusted `TargetFramework` therefore still taints `LangVersion`. Ask a
condition's trust through those, never through `trust_for_raw` /
`unpinned_root_for_raw` on its text — that reintroduces the over-taint
WoofWare/borzoi#499 hit. To tell a user *why* a value is untrusted, read the
`UntrustedCause` in `PropertyRead::Untrusted`, or `InexactUnset::cause` for a
name the real build may define.

### Inside the evaluator: the trust is on the value

A property's trust lives on its `PropertyMap` entry, beside the value, and an
expansion's result carries the join of what it read
(`docs/msbuild-value-carried-provenance-plan.md`, P3). So a new read of the
table is `get(name)` → `Held::parts()` (value and trust together), and a read
that leaves the trust behind must say so: `ignoring_trust`,
`get_ignoring_trust`, `get_unescaped_ignoring_trust`. Each existing one has a
comment naming where its trust question is answered; a new one needs the same,
and "nowhere" is the bug. `Trust::CERTAIN` is sealed to `crate::properties` —
if you find yourself wanting it elsewhere, you are about to fabricate
certainty. The item pass still judges its values by `Expansion`'s scan-based
flags (entries 6 and 7 above); its `ignoring_trust` sites are P4's worklist.

**Staleness is read where a value is published or decides an import.**
`Trust::stale` is consumed where a value decides a `Directory.Build.*` import
point (`is_decided_point` in `evaluator/directory_build.rs`, through
`is_certain`), which is what closed #614; where a Compile item's `Include` or
`Condition` reads it in a Compile context (`expand_inner`,
`evaluate_condition_with_exemptions`), which leaves the Compile set uncertain;
and at the end of the walk, where `read_property` publishes a stale value as
`PropertyRead::Untrusted` (so `target_name` is `Unknown` on one, and on a name
unset after hidden content) (#792). A write made inside an import the
walk followed on a gate it could not decide is unpinned with that gate's root
when the import returns, and an import made inside it is not a certain
duplicate later (#791). An import made after hidden content is treated the
same way: that content may already have made it, so MSBuild may skip it as a
duplicate (#891).
`reference_is_untrusted` and `untrusted_cause` leave staleness out on purpose:
they serve the mid-walk condition decisions, where
`condition_is_decided_exactly` already vouches for nothing once the walk is
opaque. The end-of-walk readers cost nothing on the crate suite, the F# corpus
or the LSP project corpus only because a real SDK chain latches no opacity
after the body (an undefined `TargetFramework` read is exact); a new latch on
that chain would withdraw `TargetFramework`, `AssemblyName` and the reference
set with them, so measure one before adding it (the plan's "#614: what each
rule costs" is the template).

## 2. Never gate a fold on the generic provenance seam

An untrusted `ParsedProject::property` read happens for **dozens of
properties on every real SDK project**: a plain `net10.0` library marks 84,
`DefineConstants`, `OutputPath`, `OutDir`, `TargetFrameworkMoniker` and
`IntermediateOutputPath` among them (dotnet 10.0.301). SDK-file uncertainty is
tolerated by design, so a wholesale refusal (`build_parses` and friends) keyed
on one of those needs a second signal separating real risk from SDK noise.
Which properties it marks is per-property, not per-project: `LangVersion` is
*not* marked on an ordinary SDK project, because the SDK's own writes of it sit
under gates the walker decides
(`sdk_project_fold_e2e::ordinary_sdk_projects_have_trusted_langversion_provenance`
pins this). Probe the specific property before assuming either way.

Two patterns that work:

- **A user-authored-only channel.** `define_constants_uncertain` sets
  `!in_sdk_subtree` at every diagnostic set site. The provenance gate covers
  content the walk *entered*, never content it could not see: a hidden SDK
  import may reach a user file, so every opacity latch withdraws the define
  set, the Compile set and the reference list wherever it is (#843, #862,
  #821, #848), and `into_project` asserts all three.
- **A consequence-side flag**, computed where the uncertain value is consumed —
  often cheaper *and* exact, and it still earns its place where the generic
  mark is rare: an untrusted `LangVersion` would otherwise refuse every file
  of that project. The LangVersion case uses
  `Parse::shape_depends_on_language_version`: the lex-filter records reaching a
  version-gated decision (an offside strict push, or a `relaxWhitespace2` pop
  that matters). `false` **proves** the tree is version-invariant
  (first-divergence argument); `true` over-approximates (EOF-anchored pushes
  reconverge — `module M =` mid-edit). So the fold refuses only on untrusted
  provenance × flagged file × a *verified* green-tree difference against a
  re-parse at every other `LanguageVersion::SHAPE_REPRESENTATIVES` band (rowan
  green equality is structural). **Trigger cheap, verify exact.**

## 3. Test any new trust gate against a real SDK

SDK-less unit fixtures never produce SDK taint, so they stay green while every
real project breaks. Use `Workspace::new()` under `nix develop`;
`sdk_project_fold_e2e` pins both directions (plain folds; straddling + taint
refuses).

To find shape-divergent fixtures, don't hand-craft them: proptest an indentation
soup and assert the flag's soundness property
(`crates/cst/tests/all/shape_sensitivity.rs`). The shrunk counterexample
(`"match x with\n"`) is the reusable fixture.

For ground-truthing any claim about MSBuild's own semantics, use the
`msbuild-condition-oracle` skill rather than reasoning from docs.
