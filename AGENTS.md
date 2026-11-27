This is an LSP for F#.
It's intentionally scoped tightly to what I think LLM agents might want, rather than e.g. for editor use.

You should find the F# compiler checked out in ../fsharp ; shout if it's not there and you need the F# compiler's source.

## Read the crate's own AGENTS.md

Each crate under `crates/` has an `AGENTS.md` beside its `Cargo.toml` (and a
`CLAUDE.md` that includes it, so Claude Code loads it when it reads files in
that crate). Before changing or reviewing code in one of them, read its file. It records the
crate's invariants, the oracles and sweeps it is held to, and the review
findings already known to be out of scope, none of which this file repeats.

## Workspace layout

A Cargo workspace with ten crates under `crates/` and two tools:

- `crates/cst/` — `borzoi-cst`: lexer, lex-filter (offside rewriter),
  recursive-descent parser, the lossless tree, and the typed AST, both as the
  union of every language version (`unstable-union`) and as frozen
  per-version facades. Self-contained; meant to be reusable outside this repo.
- `crates/msbuild/` — `borzoi-msbuild`: `.fsproj` evaluation (Compile order,
  properties, conditions, the SDK import chain), held to real MSBuild.
  Self-contained; reusable.
- `crates/assembly/` — `borzoi-assembly`: an ECMA-335 reader with an
  F#-flavoured projection of referenced assemblies. Self-contained; reusable.
- `crates/nuget/` — `borzoi-nuget`: NuGet primitives for the in-house
  warm-cache restore, each either identical to `dotnet restore` or declining.
- `crates/spawn/` — `borzoi-spawn`: the one place a child process is spawned
  (`clippy.toml` bans `Command::{spawn,status,output}` everywhere else).
- `crates/oracle-harness/` — `borzoi-oracle-harness`, test-only: resident
  oracle children, exact manifests, the XML nesting pump, the hostile-value
  library.
- `crates/print/` — `borzoi-print`: an owned F# syntax tree, typed by the
  language version it targets, and a reference printer for it.
- `crates/sema/` — `borzoi-sema`: name resolution and type inference over the
  `borzoi-cst` AST, held to FCS.
- `crates/lsp/` — `borzoi` (the package id is just `borzoi`, *not*
  `borzoi-lsp`; use `cargo test -p borzoi`): the LSP server (`cargo run -p borzoi`).
- `crates/corpus-diff/` — `borzoi-corpus-diff`, test-only: the whole-project
  name-resolution differential over real F# projects.
- `tools/astgen/` — `borzoi-astgen`: generates `borzoi-cst`'s typed AST and each facade from its
  lock (`crates/cst/AGENTS.md` and `docs/ast-versioning-plan.md` describe it).
- `tools/stats/` — `borzoi-stats`: the continuous measurements `stats.yml`
  records (`docs/continuous-measurements.md`).

Workspace-level files (`tools/`, `docs/`, `flake.nix`) sit at the repo root.
`tools/` holds the test-only oracles (`fcs-dump`, `msbuild-condition-oracle`,
`nuget-oracle`, `inheritdoc-oracle`, `workload-oracle`), never runtime
dependencies, and the CI scripts. `docs/*-plan.md` are design plans in flight;
`docs/completed/` holds finished ones.

## How correctness is checked

Each component is differentially tested against the real tool it reimplements:
FCS for the parser, name resolution and inference
(`docs/fcs-differential-testing.md` for the parser and lex-filter), MSBuild,
NuGet and Roslyn for theirs. The contract is *certain-implies-exact*: when we
commit to an answer, the reference must agree exactly; a decline makes no
claim. `docs/continuous-measurements.md` has the split between gates and
measurements.

## What in-repo tooling must survive

The development and test tooling has one consumer: us. That covers the
harnesses, oracles, test-support modules and CI scripts, everything under
`crates/oracle-harness/`, and everything under `tools/` except
`tools/csharp-sidecar/`, which ships with borzoi and runs in users'
workspaces. Each tool must give the right answer, or refuse loudly, in the
environments this repo runs it in:

- the `nix develop` devshell on a developer's macOS machine;
- the developer's own shell, for a script this file says to run outside
  `nix develop`;
- CI's Ubuntu runners.

The following are out of scope, and a refusal or a clear panic is a sound
answer to any of them:

- a hostile or misconfigured environment, such as an odd `PATH`, a broken
  `TMPDIR` or a relative `DOTNET_ROOT`;
- an operator working against the tool, such as an `assume-unchanged` or
  symlinked manifest, or a script killed mid-run;
- code under test that acts maliciously;
- a platform that neither CI nor the developer setup above uses.

What stays in scope is the tool's job. A harness is wrong if it can pass while
the property it names fails, or if it answers wrongly in the environments
above. This section covers the tools themselves, not what the product reads.
The hostile inputs below are inputs the product reads, and the product still
owes them.

## A new generator needs a row

`borzoi_oracle_harness::hostile` holds the strange inputs every generator
should search (a file named `-o:Evil.dll`, a FIFO where a file is expected, a
value holding `%0A--out:`), by the kind of input. Its table,
`crates/oracle-harness/src/hostile/boundaries.tsv`, has a row for each
generative differential and perturbation sweep under `crates/`, saying which
hostile kinds the file draws or why none applies, and CI's lint job fails on a
generator with no row. A review finding that needs a contrived input is
answered by adding a dimension there, which every harness of that kind then
owes, not by a fix at the one site. `crates/oracle-harness/AGENTS.md` has the
rest.

## Mutation testing

`tools/mutants/` runs cargo-mutants over named sets of files
(`tools/mutants/sets.tsv`), each pinned in an exact manifest of one verdict
per mutant (`tools/mutants/manifests/<set>.txt`). A mutated program can do
damage by accident (a mutated path computation that deletes the wrong
directory, a loop that never ends), so mutants run only in a Linux sandbox that
contains that: on a Mac, `tools/mutants/run.sh SET` (in Apple's `container`,
with a read-only Nix store, no network, and bounded memory and time), or in
CI's own job, `tools/ci/mutants.sh SET`. The sandbox is against accidents, not
against a mutant written to escape it. Every test binary
runs through a canary (`.cargo/mutants.toml`, `tools/mutants/canary.sh`), so
a bare `cargo mutants` anywhere else fails its baseline and runs no mutant.
A survivor is killed with a test where one belongs; only a mutant no test
*can* observe goes in `tools/mutants/equivalent.tsv`, with the argument.

## One test binary per crate

`cst`, `sema`, `assembly`, `nuget` and `lsp` each have exactly one integration-test
target, `tests/all/main.rs`, whose submodules are the case groups. One binary
links once per change and spawns one resident oracle, not one per group.

So **add a case group as `tests/all/<group>.rs` plus a `mod <group>;` line in
`main.rs`**, not as a new `tests/*.rs`, and run one group with
`--test all <group>::` (`--test <group>` does not resolve). Each binary's
`all_case_groups_are_declared` test fails, naming the file, on an undeclared
group or a stray test target beside `all/`.

Two things the single binary made sharp, both handled in
`borzoi_oracle_harness`, and worth knowing before you add to a harness:

- **The panic hook is process-global.** Sweeps that expect panics must silence
  them with `panic_silence::silence_panics_here()` (a per-thread guard), never
  by swapping the hook: concurrent swaps can leave the silent hook installed for
  good and swallow a *real* failure's message.
- **A resident oracle child cannot serve concurrent callers**: its requests and
  responses are matched positionally. One `BatchChild` behind a mutex serialises
  the whole crate's suite, so `cst` drives a pool of them. The cap is a
  process-wide budget, not per-pool. For the same reason `try_request` refuses,
  unsent, a request that is blank or holds a line break
  (`BatchFailure::NotOneLine`).

Don't switch the runner to cargo-nextest: separate test binaries defeat the
batching.

## Comments

Comments describe the code's *current* state, not the history of how it got
there. Avoid phrasing framed as a delta from a previous version — "no longer a
submodule", "rather than the old X", "dropped Y because…". The diff and commit
message already record what changed; a comment that narrates the change
becomes stale noise the moment the next change lands. State the present
rationale instead (e.g. "`contents: read` covers `actions/checkout`", not
"dropped `pull-requests: read` because we removed dorny").

## Before you push

Iterate with `cargo test -p <the crate you touched>`: the workspace-wide sweep
is a pre-push gate, not an inner loop. A change to `cst` cascades to `sema` and
`lsp` (both depend on it), so those are usually the "affected crates".

Then commit to a non-`main` branch and run the full gate: `cargo fmt`,
`cargo clippy`, `cargo test`, and
`RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features --document-private-items`
(each on the whole workspace; CI gates on doc warnings). `--document-private-items`
is load-bearing: nearly every doc comment here hangs off a private item, so
without it rustdoc never resolves their intra-doc links.

Workspace-wide commands unify features, so they build `borzoi-cst` with
`unstable-union` and `borzoi-assembly`, `borzoi-msbuild` and `borzoi-sema` with
`test-support`. After touching one of those crates, also run CI's featureless
clippy and doc pair for it (its `AGENTS.md` gives the commands).

Each crate's CI job also gates on its `#[ignore]`d sweeps, which `cargo test`
skips. `tools/ci/corpus-sweeps.sh` is the one list of them; run the groups for
the CI jobs your change triggers (a change to `cst` also runs `sema`'s and
`lsp`'s):

```sh
bash tools/ci/corpus-sweeps.sh cst sema lsp    # crates: cst msbuild nuget sema lsp
bash tools/ci/corpus-sweeps.sh --list          # every step, to run one by name
```

Most sweeps pin every graded item in a manifest and fail on movement **in either
direction**, so improving the parser fails `parser_corpus` until the manifest
records it. If every moved line is intended, rerun with
`BORZOI_UPDATE_MANIFESTS=1` and commit the manifest diff. Never loosen a
one-sided floor to turn a red run green without first establishing which
direction it moved and why. Keyed manifests merge item by item once the merge
driver is enabled, once per clone:

```sh
git config merge.borzoi-manifest.driver 'bash tools/manifest-merge.sh %O %A %B %P'
```

`docs/continuous-measurements.md` ("Exact manifests") has the format and the rules.

### The whole-project gate

CI's `corpus-diff` job runs on every pull request, ungated by change filters.
Its steps are those of `tools/ci/project-corpus-gate.sh`, so running the script
runs the job. Run it, outside `nix develop`, before pushing a change that could
move what the LSP answers, which is most changes to `cst`, `sema`, `assembly`,
`msbuild`, `nuget`, `lsp` or `corpus-diff`:

```sh
bash tools/ci/project-corpus-gate.sh                    # every step
bash tools/ci/project-corpus-gate.sh xml-doc-source     # just one; --list names them
```

The script's header covers the shared corpus cache and what to do after a run
that was killed.

### Known flake

`oracle-harness`'s `batch_recovers_from_a_transient_wedge` hardcodes a
300 ms child deadline and flakes on a loaded machine (e.g. sibling worktrees
building concurrently). If it is the *only* failure, check `uptime` before
blaming your diff: it fails on `main` too under load.
