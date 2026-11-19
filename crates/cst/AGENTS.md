# `borzoi-cst`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

The lexer, lex-filter (offside rewriter),
recursive-descent parser, and the CST/AST: a flat preorder table per file
(`docs/flat-syntax-tree-plan.md`) behind rowan's red-tree API, written
directly by the parser. Its tests turn on the `rowan-reference` feature,
under which every parse also builds rowan's green tree and asserts the two
trees are the same, and `token-reference`, under which every lex asserts
that the raw token table rebuilds the full-trivia driver iterator's stream
(`docs/token-pipeline-soa-plan.md`), and `walk-reference`, under which every
parse asserts that the diagnostics' partial scans (the warn directives off the
raw table, the feature gates' kind-filtered walk) find what a walk over every
element of the tree finds. Self-contained: depends only on `logos` and
`text-size` (and, behind that test-only feature, `rowan`). Intended to be
reusable outside this repo, through its *substrate*: the untyped tree
(`SyntaxNode`, `SyntaxKind`, `AstNode`) and the version gate
(`syntax::projection`), and through one typed facade per language version,
`syntax::{v4_6, v4_7, v5 … v11, preview}`, each behind the cargo feature of
its name (`unstable-preview` for `preview`) and read through
`Parse::view::<syntax::vN::ParsedInput>()`. A facade owns every node type
and enum of its version's surface; `tools/astgen` generates each from its
lock (`crates/cst/facades/vN.lock`), and a version whose surface equals an
earlier one's is an alias of it. The unpublished `preview` facade's lock is
derived from the union's and regenerated freely. The facades up to `v11`
are **published**: frozen, their locks astgen's input rather
than its output, changing only by the additions
`tools/ci/facade-lock-check.sh` allows, each distinct one with a frozen
consumer fixture (`tests/all/facade_consumers/`) that must keep compiling.
A union accessor or derive added later is opt-in for a frozen facade, and
an enum it never declared (with what names it) is simply not offered, but
a union change that would break one or open a hole in it fails astgen until
the lock takes it or `ACCEPTED_DIVERGENCES` records why not; see "Publishing a
facade" in `docs/ast-versioning-plan.md`, which is also the runbook for
publishing a new language version's facade. The
typed AST the facades re-cast — the *union* of every language version's
surface (`ImplFile`, `Expr`, `Pat`, `Type`, `ModuleDecl`, …, in
`syntax/union.rs` and `syntax/generated/`) — gains a variant whenever a
construct is modelled, so it is exported, at unchanged `syntax::` paths, only
under the `unstable-union` feature. `borzoi-sema`, the LSP,
`borzoi-corpus-diff` and cst's own tests turn it on, and sema and the LSP
turn on no facade; workspace builds therefore always have the union, so CI's
lint job also builds, lints and documents the crate without it.
`tests/all/facade_properties` holds every facade's node types, enums and
accessors to the union's (P2–P4 of `docs/ast-versioning-plan.md`) over a
table astgen generates from the locks.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-cst`; the repository's root `AGENTS.md` has the pre-push gate.

This crate's CI job also runs ignored sweeps, which `cargo test` skips. Run them before pushing:

```sh
bash tools/ci/corpus-sweeps.sh cst            # all of them
bash tools/ci/corpus-sweeps.sh --list cst     # their names, to run one
```

Workspace builds always turn `unstable-union` on, so after a change here run CI's featureless pair as well:

```sh
nix develop -c cargo clippy -p borzoi-cst --lib -- -D warnings
RUSTDOCFLAGS="-D warnings" nix develop -c cargo doc -p borzoi-cst --no-deps --document-private-items
```

Read first:

- `docs/fcs-differential-testing.md` before touching the lexer, lex-filter or parser: the FCS differentials, the corpus gate, and the workflow for adding a construct
- `docs/ast-versioning-plan.md` ("Publishing a facade") before changing a facade or its lock
- `docs/parser-recovery-oracle.md` before changing error recovery
- skills: `parser-divergence-sweep`, `fsharp-fcs-differential-gotchas`
