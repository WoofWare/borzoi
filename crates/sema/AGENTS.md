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
A referenced F# project's existence surface is read from its source by
`source_existence` (Stage 1a of the source-references plan), for the
**existence consumers only**: the rows the `assembly_env::existence` set
reads (canonical entity paths, namespace/abbreviation/other, `[<AutoOpen>]`,
`[<Extension>]` on abbreviations, extension names and staticness, assembly
auto-open paths), or `Unread` with the reason. Every question that set
answers is monotone, so the claim is containment: the set built from our
rows holds every fact of the set built from FCS's CCU for A, which
`tests/all/source_existence_diff.rs` checks on the set's own facts
(`test_support::existence_facts`), pinning ours' surplus per kind and
failing a surplus abbreviation lender no `Approximation` accounts for at
its own path (`SourceSurface::lender_sources`; one makes every name a
possible extension). Fields no existence question reads
(accessibility, kinds beyond abbreviation, the inferred `[<Extension>]`)
are constants: **a stage that reads more of a source producer derives and
grades those itself.** Its input enumerates what only the caller knows (an
unreadable Compile item, a refused fold, an unserved producer TFM) and what
A's references route each written attribute name to (`MarkerRoutes`:
`Unknown`, or a `Certified` map in which an omitted name reads as
`Unknown`), and whether one of them may be a type provider
(`ProviderReferences`, under which any abbreviation to a named type
declines). Every match over a syntax enum in the walk and its member reader
names its kinds (`clippy::wildcard_enum_match_arm` is denied there), so a
construct no arm reads is a compile error, not a silent skip. The leaves it
interprets (a type's head, an augmentation's head, an abbreviation's target
where a provider may be referenced, an `[<Extension>]` binding's pattern)
are certified form by form in
`LEAF_FORMS`: a form outside the table declines (`OutsideDomain`), and
`source_existence_domain` grades every row against FCS and holds the walk to
each row's verdict, so the predicate and the table cannot drift apart. A
clean producer's resolver fold is held to the walk too: every module and
placed type `resolve_project_files` exports is one of its entities
(`test_support::fold_entity_paths`). Every channel it reads is a `Channel` with a `Treatment`, and
`the_inventory_is_what_the_walk_does` runs a witness of each. The only
positions the walk reads are the lines a marked class `let`'s head spans
(`head_lines`): FCS mangles a taken name by its binder's line, and the walk
emits every line of the head rather than model which token FCS takes the
range from. `source_existence_layout` holds that to FCS with a line break
before every token and a comment line before every line of each grid cell
that reads a position, and the generator mixes the same layout trivia into
random cases. The harness
grades a hand-written grid (`source_existence_grid.rs`), generated projects
(`source_existence_gen.rs`, `deep_` for more seeds), and the
attribute-placement grid (`source_existence_placement.rs`: every
attribute-bearing node of the grammar, held to `syntax/union.rs` by
`every_attribute_bearing_node_has_a_template`, under every marker, at every
target in its `deep_` twin), reading FCS's signature through `fcs-dump`'s
`referenced` op and `unpickle_signature`, each verdict pinned; the corpus
twin is `borzoi-corpus-diff`'s `source_existence_corpus`. The member reader
it shares with `resolve/extension_names.rs` is `member_shape`.
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
