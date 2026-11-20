# `borzoi-sema`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

Semantic analysis (name resolution
today, type inference later) over the `borzoi-cst` AST. `resolve_file`
builds a position-ordered scope tree and resolves each name use to its
defining binder; `resolve_project` folds that over the Compile order,
threading each file's exports forward; `AssemblyEnv` resolves
fully-qualified paths into referenced assemblies via the
`borzoi-assembly` entity model. Depends on `borzoi-cst` and
`borzoi-assembly`. Differentially tested against FCS; consumed by the
LSP at runtime (`crates/lsp/src/semantic.rs`).
What a file contributes to later files is its `FileSurface`, and
`surface_file` computes it with a walk that skips every expression. Under
the `surface-reference` feature (on in sema's tests, and in the
whole-project gate through `borzoi-corpus-diff`'s feature of that name)
every `resolve_file` also runs that walk and panics unless the two
surfaces are equal, so a surface field that a body decides fails wherever
a file is resolved.
The use differentials only see a binder the walk missed when some graded
use sits in its scope with an outer target to commit to, so **binder
completeness** checks the binders themselves
(`test_support::binder_completeness`): every binder FCS declares — a
definition record, or the declaration a use names — must be one the walk
interns (a `Def`) or knows it declines (`ResolvedFile::opaque_binders`,
`ResolvedFile::opaque_regions`). `tests/all/binder_site_grid.rs` is the
closed table of F#'s binding constructs, each FCS-graded under an empty
and a BCL environment with each row's status pinned; the FCS-graded grids,
`resolve_corpus_diff` and the whole-project gate run the same check on
every cell and file. A binding construct the walk does not know about
starts as a row in that table, not a review finding.
Every range sema records or looks up is FCS's, so a token's range is read
through `borzoi_sema::FcsRange::fcs_range`, and `clippy.toml` bans
`SyntaxToken::text_range` in sema and the LSP. They differ only for the
glued `(*)`, which the tree spells as `(`, `*`, `)` (what every frozen
facade's name accessors return) and FCS names over all three characters
(`borzoi_cst::syntax::fcs_ident_range`).
A referenced F# project read from its source feeds the existence set in two
halves (Stage 1a of the source-references plan). **The entity half** is
`source_existence`: the rows open certification reads (canonical entity
paths, namespace/abbreviation/other, `[<AutoOpen>]`, assembly auto-open
paths), or `Unread` with the reason. Every such question is monotone, so the
claim is containment on those facts, which `tests/all/source_existence_diff.rs`
grades on the set's own facts (`test_support::existence_facts`), pinning
ours' surplus. **The extension half** is the reference's `ExtensionNames`
(`ResolvedProject::extension_names`), the gate's currency for the project's
own files: FCS binds an extension by its logical name, so no compiled
spelling, class `let` or module `let` is read, and the claim is the gate
grids' certain-implies-exact with the reference as a `ReferencedProject`
placement (`infer_extension_scope_grid`, `infer_assembly_extension_grid`,
through `common::ext_scope::check_referenced` and FCS's graph oracle).
`a_referenced_project_binds_extensions_by_logical_name_only` pins the
calls that license that: a backticked compiled spelling, an `[<Extension>]`
module `let` and an `[<Extension>]` class `let` bind nothing of the
reference. `AssemblyEnv::add_source_existence` takes both halves; an unread
entity half makes the set unknowable whatever the names say. Fields no
entity question reads (accessibility, kinds beyond abbreviation, the
`[<Extension>]` flag) are constants: **a stage that reads more of a source
producer derives and grades those itself.** The walk's input enumerates
what only the caller knows (an unreadable Compile item, a refused fold, an
unserved producer TFM), what A's references route each written attribute
name to (`MarkerRoutes`, certified by the full name a written name resolves
to, in any assembly), and whether one may be a type provider
(`ProviderReferences`). Each node the walk reads is a `Leaf` classified into
a closed `Form` whose verdict decides it, and each classifier accounts for
every child of its node, so a child no classifier names declines
(`Unreadable`); `source_existence_domain` grades every `Form::ALL` witness
against FCS, the raw-kind scans (`RAW_SCANS`) have a grid cell each, and
`source_existence_accessors` pins, under `accessor-trace`, every accessor of
a node type the walk reads that it never calls, with its reason. Every
match over a syntax enum in the walk names its kinds
(`clippy::wildcard_enum_match_arm` is denied there). The walk bounds its
input before it walks (`MAX_NAME_BYTES`, `MAX_DEPTH`, `MAX_DECLARATIONS`),
so the rows' memory is bounded by the input with no metering;
`source_existence_budget` runs the bound's corner through `ExistenceSet`
construction under a memory limit. A clean producer's resolver fold is held
to the walk (`test_support::fold_entity_paths`), and every channel it reads
is a `Channel` with a `Treatment`, witnessed by
`the_inventory_is_what_the_walk_does`. The harness grades a hand-written
grid, generated projects and the attribute-placement grid (every
attribute-bearing node of the grammar, held to `syntax/union.rs` by
`every_attribute_bearing_node_has_a_template`), reading FCS's signature
through `fcs-dump`'s `referenced` op and `unpickle_signature`, each verdict
pinned; `source_existence_census` measures, FCS-free, what the walk declines
over the pinned corpus.
Inferred types are not bounded by the tree (each line of `let gK x =
g(K-1) (g(K-1) x)` doubles one), so every walk of the unification table
counts against a type budget (`MAX_TYPE_NODES`, `MAX_TYPE_DEPTH`), and a
file whose inference reaches it publishes no inferred type at all
(`InferredFile::type_budget_exceeded`). `tests/all/infer_type_budget.rs`
runs the growth families under a memory, time and stack limit
(`borzoi_oracle_harness::alloc_limit`, `stack_probe::run_case_limited`);
`infer_corpus_diff` fails if real code comes within a factor of 8 of it.
Resolution and inference recurse once per level of the tree, so what
bounds their stack is the parser's `MAX_TREE_HEIGHT`: `WALK_STACK_BYTES`
is the stack they need for any tree it returns, the LSP's request thread
is spawned with it, and `tests/all/walk_stack_bound.rs` (and the LSP
crate's twin, over the whole request loop) holds every repetition form of
the grammar to half of it, each case in a child process. A change that
fattens a frame on a walk's recursion fails there, naming the shape. A walk
that declines at the top of a tree survives any stack, so how deep each
walk reached into each case is pinned in
`tests/manifests/walk_stack_bound.txt`.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-sema`; the repository's root `AGENTS.md` has the pre-push gate.

This crate's CI job also runs ignored sweeps, which `cargo test` skips. Run them before pushing:

```sh
bash tools/ci/corpus-sweeps.sh sema            # all of them
bash tools/ci/corpus-sweeps.sh --list sema     # their names, to run one
```

Workspace builds always turn this crate's `test-support` feature on, so an item gated on `any(test, feature = "test-support")` can hide a use or an intra-doc link from them. After a change here run CI's featureless pair as well:

```sh
nix develop -c cargo clippy -p borzoi-sema --lib -- -D warnings
RUSTDOCFLAGS="-D warnings" nix develop -c cargo doc -p borzoi-sema --no-deps --document-private-items
```

Read first:

- skills: `member-resolution-soundness` (before any member-access or inheritance change), `resolve-divergence-sweep`, `resolution-explain`, `fsharp-fcs-differential-gotchas`
