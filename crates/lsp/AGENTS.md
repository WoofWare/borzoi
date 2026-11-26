# `borzoi`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

The package id is `borzoi`, *not* `borzoi-lsp`: use `cargo test -p borzoi`.

The LSP server (binary + library):
diagnostics, project-assets resolution, the C# sidecar (run only for a host
that sets the `enableCSharpProjectReferences` initialization option, as
on-demand restore needs `enableOnDemandRestore`: both execute the workspace's
MSBuild targets). Depends on
`borzoi-cst` for tokens/parse trees and `borzoi-sema` for name
resolution. Consumes `borzoi-msbuild`
for `.fsproj` evaluation *at runtime* — every per-file lookup evaluates
the owning `.fsproj` via `parse_fsproj_with_imports` (SDK + glob
resolvers wired). The evaluation's `define_constants` and diagnostics,
its ordered Compile `items` (the semantic layer's fold order), and its
`project_references` (the inter-project graph: `.fsproj` diagnostics and
the assembly env's reference edges) are all consumed
(`docs/fsproj-consumption-plan.md` tracks the remaining consumers).
The defines and the reference list are `borzoi-verdict` verdicts, and the
LSP forms the served build's once, in `workspace::EvaluatedProject`, folding in
what the evaluator cannot see (an outer dispatch build standing in for an inner
one, a document no evaluation of which is an inner build); every reader takes
them from there or from `ProjectEvaluation`. `crates/lsp/clippy.toml` bans the
evaluator's own verdicts and `ParsedProject::best_guess` elsewhere, so a reader
of the walk's raw values carries an `#[expect]` saying why (#1112, #1176).
`borzoi-assembly` is runtime-live too: referenced assemblies are
read into each project's `AssemblyEnv` (`crates/lsp/src/semantic.rs`).
The crate observes the file system only through `crates/lsp/src/observed.rs`
(`docs/incremental-lsp-plan.md`, D3): source text is owned by the `Vfs`
(`crates/lsp/src/vfs.rs`), whose disk is `observed::HostDisk` and which
counts its opens and `stat`s per generation of the dispatch loop, and every
other read is a method of `Unobserved`, whose variant names the reader and
the plan stage that will route it. The `Vfs` re-reads a disk file only when
its stamp moves or is racy (git's rule, a 2 s window), and every cached fold
is validated against it in each generation that reads it, so a closed
source rewritten with no watch event is still seen
(`incremental_state_machine`'s `WITNESSED`). `crates/lsp/clippy.toml` bans the `std` calls
everywhere else; test code reaches them through `host_fs` (the lib's
`observed::host_fs`, `tests/all/common/host_fs.rs`), never through a
wholesale allow, which would also lift the spawn ban.
A project's `<LangVersion>` is read as the F# compiler of its resolved SDK
reads it (`crates/lsp/src/sdk_language.rs`: default, aliases, newest
recognised and oldest supported version, per feature band). Only bands
`sdk_language_diff` grades against an installed SDK's own `fsc.dll` have a
row, and that test fails on a row no installed SDK grades, so an SDK bump in
the devshell can fail it until the table follows. The compiler is named as
the SDK's own only while nothing outside the SDK can choose another: no
document the evaluation entered outside the SDK's version directory defines a
compiler selector or runs build code of its own (a target or task), whatever
its condition (`ParsedProject::foreign_definitions`; the install's workload
manifests, `ParsedProject::workload_definitions`, are held to the selectors
alone), and the walk hid nothing (`ParsedProject::hidden_content`). The same
test derives the selector set from each SDK's own F# files, accounts for
every variable the `Fsc` task's assembly names, and checks real MSBuild runs
the compiler named. Routes the evaluation cannot see stay unmodelled, as the
rest of the LSP already assumes its own compiler: an SDK-performed import a
project property steers (`NuGetBuildTasksPackTargets`), and response files
(`Directory.Build.rsp`); the boundary is stated in `sdk_language.rs`'s module
docs, so a review finding of that kind is known and out of scope.
Hover's XML documentation lives in `crates/lsp/src/xml_doc/`. Its
`<inheritdoc>` work is held to Roslyn's IDE through
`tools/inheritdoc-oracle`, a test-only C# JSONL batch tool (the
`nuget-oracle` mould) that calls Roslyn's internal expansion by
reflection, evaluates Roslyn's XPath selection, and compiles purpose-built
C# fixtures (rewriting a method name or an `AssemblyRef` in one, for
metadata no compiler writes) or emits assemblies from a description
(System.Reflection.Metadata). `xml_doc_inheritdoc_xpath_diff` holds the
XPath subset to certain-implies-exact against it; `xml_doc_inheritdoc_diff`
(handwritten fixtures), `xml_doc_inheritdoc_cref_diff` (generated reference
sets whose dimensions are the ways Roslyn's importer and declaration-ID
lookup see metadata differently from the env's index, every documented ID
cited by a `cref`), `xml_doc_inheritdoc_generated_diff` (generated C#),
`xml_doc_inheritdoc_metadata_diff` (generated metadata: accessor names,
reference versions/cultures/case, facades, core-library shapes, custom
modifiers, `MethodImpl` rows, doc-file layouts — with a per-dimension
census and liveness) — the generators run a few dozen cases each in
the normal suite, hundreds in their ignored `deep_*` twins,
`BORZOI_INHERITDOC_CASES` overriding them all — and the ignored
`xml_doc_inheritdoc_sweep` (the ASP.NET Core pack, plus a NuGet cache under
`BORZOI_INHERITDOC_SWEEP_ROOT`) hold every `<inheritdoc>` expansion to it.
The oracle's `type-ids` op grades a type's own ID: `xml_doc_type_id_diff`
emits rows whose `` `n `` suffix need not count their parameters (Roslyn
then appends the count; fsc, whose side `borzoi-assembly`'s
`doc_id_fsharp_diff` grades, does not) and holds every one to Roslyn's
`GetDocumentationCommentId`.
The expansion certifies only metadata shaped as C# writes it: every type it
reads must pass `borzoi_assembly::shape::compiler_shape`, or it declines.
So a disagreement with Roslyn over metadata outside that shape (an event's
`fire` accessor, accessors named apart from their property, a `modopt`) is
a bug in the predicate, which must reject it, not a Roslyn rule to model;
and a review finding on such metadata that already declines is closed. The
metadata generator asserts the decline for its out-of-domain dimensions
without the oracle. What the predicate rejects in real packages is measured,
not guessed: `compiler_shape::package_cache_shape_census` (ignored,
`BORZOI_SHAPE_SWEEP_ROOT`) counts it by cause over a NuGet cache, and the
reference pack and csc output must pass it whole.

## Working here

Iterate with `nix develop -c cargo test -p borzoi`; the repository's root `AGENTS.md` has the pre-push gate.

This crate's CI job also runs ignored sweeps, which `cargo test` skips. Run them before pushing:

```sh
bash tools/ci/corpus-sweeps.sh lsp            # all of them
bash tools/ci/corpus-sweeps.sh --list lsp     # their names, to run one
```

Read first:

- `docs/incremental-lsp-plan.md` before changing what a request reads or caches
- `docs/fsproj-consumption-plan.md` for the remaining `.fsproj` consumers
- skills: `resolve-real-project-diff`, `msbuild-trust-audit`
