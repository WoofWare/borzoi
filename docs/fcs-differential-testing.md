# Differential testing against FCS (parser & lex-filter)

Unqualified paths below (`common/…`, `tests/manifests/…`) are under `crates/cst/` (its `tests/all/` for `common/`).

The parser and lex-filter are checked for byte-faithful behaviour against the
real F# Compiler Service by *differential* tests living in `crates/cst/tests/all/`:

- **What the parser diff tests.** FCS is asked for its `ParsedInput` via
  `tools/fcs-dump ast`; our parser produces a CST/AST. Both are projected
  to the shared `crates/cst/tests/all/common/normalised_ast/` model and compared
  with `assert_eq!`. This tests the *modelled syntactic structure* and the
  caller-selected parse-status expectation (both clean, both erroring, or a
  known acceptance gap). The normaliser deliberately elides trivia and most FCS
  details/ranges; module/decl ranges, and the ranges of the names below them
  (type, union-case, field, member and `let` binder names), are separately
  audited (`common/range_audit.rs`). The lex-filter diff compares our offside
  rewriter's output with the stream FCS's parser reads, block ends included
  (`fcs-dump tokens-lexfilter-internal-batch`, read with
  `parse_fcs_parser_stream`).
- **What the currency must cover.** Eliding is only sound for detail no consumer
  reads. Every public accessor in `crates/cst/src/syntax/union.rs` opens with
  `accessor!("Type::method")`, which under the crate's `accessor-trace` feature
  (on for its own tests) records the call. `parser_corpus_diff` records what the
  projection reads on the files that match FCS and pins it in
  `tests/manifests/accessor_coverage.txt`; `accessor_coverage::
  consumers_read_only_compared_accessors` scans `crates/sema/src` and
  `crates/lsp/src` with `syn` and fails if they call an accessor the projection
  never compares. So when sema or the LSP starts reading a new accessor, project
  it (`normalised_ast/`), add a graded fixture (`common/accessor_coverage.rs`
  `FIXTURES`) if no corpus file holds the construct, or exempt it in
  `NOT_PROJECTED` with the reason FCS has nothing to compare it with. The scan
  matches calls by method name (it has no types), so it can over-ask; and it
  cannot see a consumer that walks raw `SyntaxNode`s.
- **Per-construct tests** — `parser_diff_*.rs` (e.g. `parser_diff_module_structure.rs`
  for members/types, `parser_diff_match.rs`, `parser_diff_let_bindings.rs`, …).
  Each is a `#[test]` calling a helper from `crates/cst/tests/all/common/mod.rs`:
  - `assert_asts_match(src)` — parse `src` with both our parser and FCS, project
    each to a shared *normalised AST*, assert equal **and** that neither side
    reported errors. The normaliser is the comparison currency: it deliberately
    *elides* trivia, ranges, and detail FCS keeps but we don't model yet, so a
    diff test passes as long as the modelled structure matches. To extend it
    when a new field becomes significant, edit the projections in
    `crates/cst/tests/all/common/normalised_ast/`: `model.rs` (the data types),
    `from_cst.rs` (our `Parse` → normalised), `from_fcs.rs` (FCS JSON → normalised).
  - `assert_asts_match_allow_errors(src)` — same, but permits parse errors on
    both sides (for recovery cases like illegal-but-recovered input).
  - `assert_sig_asts_match(src)` — the `.fsi` signature-file counterpart.
  - `assert_asts_match_with_defines(src, &["FOO"])` — with `#if` symbols defined.
- **Whole-corpus sweep** — `parser_corpus_diff.rs` (and `lexfilter_corpus.rs` for
  the lex-filter) walk a real F# source tree (the `BORZOI_CORPUS` env var,
  pinned to the `fsharp-src` flake input under `nix develop`) and diff every
  `.fs`/`.fsi`. These are `#[ignore]`d by default. `parser_corpus_diff` is a
  gate (CI runs it through `tools/ci/corpus-sweeps.sh`); `lexfilter_corpus` is not. It asserts nothing,
  printing a histogram of divergence buckets that points at the next LexFilter
  arm worth porting, and its FCS side costs ~1.65 s per file, well over an hour
  across the corpus. CI does not run it and it is not a pre-push step: run it
  when you are porting LexFilter arms.
- **Categorised parser report** — `fcs_divergence.rs` is an ignored report
  generator over the same corpus. It writes one file per bucket under
  `fcs-divergence/` (or `BORZOI_DIVERGENCE_OUT`): both reject,
  we-reject/FCS-accepts, we-accept/FCS-rejects, clean-but-AST-divergent,
  unmodelled, parser panics, and other batch/IO failures. Use it when you need
  the full worklist rather than the ratcheted corpus gate's sample output.
- **Recovered trees** — where either parser rejects a file, the corpus sweep
  also grades the two recovered trees against each other
  (`common/recovery.rs`): every declaration outside the damaged region (both
  sides' error spans) must match, key for key and shape for shape, and the
  verdict is pinned per file in the manifest. `recovery_sweep.rs` manufactures
  more broken input by deleting one token (or the member name after a `.`, the
  `foo.` shape completion runs on) from clean corpus files. Write a recovery
  case as `common::recovery::assert_recovered_trees_agree(src, n)`. See
  `docs/parser-recovery-oracle.md`, which also lists what remains divergent.
  Recovery is graded more weakly than clean input: losing a declaration FCS
  keeps, where `main` keeps it, blocks; keeping it in a different module than
  FCS does is pinned in a grid manifest and allowed, so answer such a review
  finding with a grid case (that doc's "What recovery must match").

Common commands:

Like `sema`, `assembly`, `nuget` and `lsp`, this crate has a *single* integration-test
binary, `--test all` (`tests/all/main.rs`), whose submodules are the case groups
— see "One test binary per crate" below. Select a group with a `module::` filter
rather than `--test <group>`.

```sh
# Run one per-construct parser diff case group, optionally filtering to a test.
nix develop -c cargo test -p borzoi-cst --test all parser_diff_let_bindings:: -- --nocapture
nix develop -c cargo test -p borzoi-cst --test all parser_diff_let_bindings::diff_ast_name -- --nocapture

# Run the full parser-vs-FCS corpus gate.
nix develop -c cargo test -p borzoi-cst --test all parser_corpus_diff:: -- --ignored --nocapture

# Regenerate the categorised parser divergence worklist.
BORZOI_DIVERGENCE_OUT=target/fcs-divergence \
nix develop -c cargo test -p borzoi-cst --test all fcs_divergence:: -- --ignored --nocapture

# Print the lex-filter divergence histogram (not a gate; over an hour; not in CI).
nix develop -c cargo test -p borzoi-cst --test all lexfilter_corpus:: -- --ignored --nocapture
```

FCS itself is invoked through `tools/fcs-dump/` (an F# program built on demand
via `dotnet build -c Release`; the first test run builds it). It serialises FCS's
`ParsedInput`/token streams to JSON; the Rust harness drives a *long-lived*
`fcs-dump …-batch` child over stdin/stdout to amortise .NET startup (so don't
switch the runner to cargo-nextest — separate test binaries defeat the batching).
Override the binary with `BORZOI_FCS_DUMP=/path/to/fcs-dump`; it must be a
**framework-dependent** build (`dotnet publish --self-contained false`, or the
`dotnet build` output). FCS's script checks take their framework references from
the runtime fcs-dump runs on, so a self-contained bundle would check every file
against its own directory — implementation assemblies plus
FSharp.Compiler.Service itself — and fcs-dump refuses to start that way.

fcs-dump refuses, unopened, any file it or FCS would read that is not a
regular file (a FIFO, a device). That guard is Unix-only, and it has a
check-then-open race (#1087); the "Files that are not regular" block in
`tools/fcs-dump/Program.fs` states both limits.

A request below F# 8.0 — the current FCS's support floor, below which it no
longer behaves as the older compilers did because it deleted the features
introduced there — goes to a second oracle, `tools/fcs-dump-legacy`: a frozen
copy on FCS 43.12.204, never edited, built and spawned only when such a request
arrives (`BORZOI_FCS_DUMP_LEGACY` names a prebuilt one). The cst harness routes
to it (`crates/cst/tests/all/common/oracle.rs`), and so does sema's for a check
pinned below the floor (`infer_legality_pin_diff`), on fixtures and grids, never
a corpus sweep; `docs/ast-versioning-plan.md` D12 has the reasoning. To
inspect the FCS side directly:

```sh
nix develop -c dotnet build tools/fcs-dump/fcs-dump.fsproj -c Release
tools/fcs-dump/bin/Release/net10.0/fcs-dump ast path/to/file.fs
printf '%s\n' path/to/file.fs | tools/fcs-dump/bin/Release/net10.0/fcs-dump ast-batch
tools/fcs-dump/bin/Release/net10.0/fcs-dump tokens-filtered path/to/file.fs
printf '%s\n' path/to/file.fs | tools/fcs-dump/bin/Release/net10.0/fcs-dump tokens-lexfilter-internal-batch
```

`tokens-filtered` is FCS's public tokenizer, which drops every token without an
`FSharpTokenKind`, block ends among them; `tokens-lexfilter-internal-batch` is
the stream the parser reads (via reflection on FCS internals), and is what the
lex-filter differential compares against.

Workflow to add a parser feature: write the failing `assert_asts_match` test(s)
first, confirm they fail (our side errors or diverges), implement, re-run. To see
*why* a case diverges, dump our side with
`borzoi_cst::parser::parse(src).root` (`{:#?}`) and the filtered token stream
with `borzoi_cst::lexfilter::filter(src, borzoi_cst::lexer::lex(src))`.

