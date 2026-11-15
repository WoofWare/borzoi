# Resolve what a request reads: declaration surfaces, and bodies on demand

> **Status (2026-11-15).** Plan written; no stage implemented. The counts
> below were taken at 5536f10b (`origin/main`) with the throwaway spike
> described under "Measurements", on WoofWare.PawPrint2 at 91e869b4.

## Problem

A first semantic request on a file folds every earlier Compile item through
`resolve_file`, resolving every name in every binding body of every earlier
file. The request reads almost none of it.

Opening `WoofWare.PawPrint/AbstractMachine.fs` in WoofWare.PawPrint2 with the
`.#otel` build of fe24b49d made the first `textDocument/semanticTokens/full`
take 1,558 ms against a cold assembly cache and 968 ms against a warm one,
on a machine at load average about 65 on 18 cores. Of the warm 968 ms,
`resolve_project` took 557 ms, parsing 188 ms, evaluating five project files
152 ms and building the env 67 ms. The file is 44 KB of the 7.2 MB the fold
resolved, and its own `resolve_file` took 3.7 ms.

For orientation only: FsAutoComplete 0.83 answered the same request, driven
over the same protocol on the same file, in 34–37 s, almost all of it spent
type-checking the 229 files before it. FCS checks every earlier file fully,
because F# infers a top-level value's type from its body. borzoi's
resolution does not consume inferred types, and that is the opening this plan
uses.

### What a later file reads from an earlier one

The fold threads one state from file to file. The step that advances it past
a file reads, as far as reading the code finds:

- through `ProjectItems::extend_with` and what it calls: `exports`,
  `export_decls` (through `FileExportIndices::derive`), `contributions`,
  `placed_types`, `unplaced_types`, `unplaced_type_places`,
  `own_module_simple_names`, `own_type_simple_names`, `sig_screen` and
  `declares_core_attribute_alias`;
- in `thread_forward`: `augmentation_instance_names` and
  `augmentation_static_names`, and through `wholesale_extension_contribution`,
  `attributes_may_declare_extension` and `augmentation_names_unknowable`;
- in the fold loop around it: a paired signature's `sig_exports` and screen
  (`append_signature_exports`), and, for an unpaired headerless
  implementation, a shadow of its implicit module, derived from its
  qualified name and pairing (`note_implicit_module_shadow`).

A request on a later file also reads earlier files directly. Definition and
semantic tokens follow a cross-file resolution to its `Def` in the declaring
file's arena (`ResolvedProject::item_def`).

None of these is the resolution of a use inside a binding body. They are
read off declarations: binders in binding heads, type and module definitions,
attributes, opens, and the file's name. The list above was built by reading
code, and a first draft of it missed four entries. So D1 makes the compiler
derive it rather than trusting the list. About 72% of the project's bytes sit inside the bodies
of top-level and member bindings (measured over the 225 files the fold
resolved at fe24b49d, counting the bytes after each outermost `BINDING`'s
`=`).

So for a request on file `i`, every earlier file's body walk produces answers
for requests nobody made. The ResolvedProject keeps them, and a later request
on an earlier file reads them from the cache. That is the only reader they
have.

### Measurements

The harness is `crates/lsp/examples/edit_counts.rs` with `EDIT_COUNTS_EARLY=1`
and `EDIT_COUNTS_LATE=239` (`Program.fs`, 31.7 KB). Its cold
`semanticTokens L` row folds items 2–239 over an env that the
`semanticTokens E` row has already built, so the row is the fold.

The spike (not committed) makes `resolve_expr` return at once in every file
but the fold's last, in both the cold and the incremental fold. A second
switch re-runs the fold without the spike and compares the two:

| message | instructions, today | instructions, earlier bodies skipped |
|---|---:|---:|
| `semanticTokens L` (cold) | 7,041.9 M | 3,121.9 M (−56%) |
| `hover L` (cold, after it) | 702.3 M | 471.8 M |

Per-file and per-phase counts come from `thread_selfcounts` around
`resolve_file` and its phases, over files 2–238 (7.49 MB; the target is
excluded):

| phase | today | earlier bodies skipped |
|---|---:|---:|
| `Prescan::of` | 527 M | 527 M |
| the implicit auto-opens' seed, per block | 177 M | 177 M |
| `earlier_block_contributions` | 23 M | 23 M |
| `block_start_contributions` | 1,132 M | 1,132 M |
| the block's declarations (`module_decl`) | 4,837 M | 951 M |
| the rest (resolver setup, `finish`, the loop) | 52 M | 52 M |
| **`resolve_file`, total** | **6,748 M** | **2,862 M** |

Skipping bodies changes nothing the request answers:

- **The target file's whole `ResolvedFile` is equal** to the one the full fold
  produces (`PartialEq`), at horizon 2 through the cold fold and at horizon
  240 through the incremental fold. That also covers every `preceding_*`
  field the target carries.
- **Every earlier file's threaded fields that the spike compared are equal,
  except for `DefId`.** It compared the fields of the first draft's list:
  everything above but `export_decls`, `unplaced_type_places` and
  `sig_exports`. The project has five signature files, so signature
  materialisation ran, but its `sig_exports` were not compared. It has no
  headerless implementation, so the implicit-module shadow never ran. Raw,
  `exports` differ in 190 files and
  `placed_types` in 56. With each export's `def` masked, `exports` differ in
  none. `placed_types` agree under the existing
  `DeclaredType::same_for_later_files`. A `DefId` is an index into the file's
  arena in walk order (`Resolver::intern`), and a skipped body allocates none
  of its local binders' defs, so every later declaration's index moves. The
  target's equality does not cover `item_def` either, since a resolution
  names an earlier item by its `ItemId`, not its `Def`.

### What the skip leaves

Once bodies are skipped, most of what remains is the same work done again in
every file:

- **`block_start_contributions`, 1.13 G.** It pushes the earlier files' root
  contribution and opens the block's own enclosing namespace
  (`open_own_enclosing_namespace`), which folds every project item of that
  namespace from earlier files into the block's frame. It costs 1.7 M
  instructions in file 3 and 5.6–5.7 M from about file 140 on, in files of a few
  hundred bytes. It is quadratic in the project: each file re-folds what
  every earlier file added.
- **The implicit auto-opens' seed, 0.18 G.** `implicit_open_namespaces` and
  `open_auto_open_modules_in` push FSharp.Core's auto-open modules into every
  block: 0.76 M per block, identical in every file, since it depends only on
  the env.
- **`Prescan::of`, 0.53 G**, about 70 instructions per byte: several whole-tree
  walks before the declaration walk starts.
- **The declaration walk itself, 0.95 G**, about 127 instructions per byte of
  the whole file.

### Where inference stands

Hover, completion, and definition's inference branch call
`inferred_prefix_watched`, which infers the whole prefix
(`infer_project_reusing`). A file's inference reads the types earlier files
published for their top-level values, and those come from their bodies. So
inference does need earlier bodies, and the spike's cheaper `hover L` row is
the cost of answering from less, not a saving: its answers were not checked.
Semantic tokens, references, and definition's resolution branch read
resolution only (`resolved_prefix_and_env_watched`).

### Relation to the other plans

`docs/sema-interning-plan.md` made each lookup cheaper and lists "reducing how
many walks or lookups the resolver does" as a non-goal. This plan is that
complement. `docs/incremental-lsp-plan.md` Stage 9's gate is unmet because an
edit can arrive during a cold fold, which costs at least 0.62 G on
WoofWare.Incremental; this plan shrinks that fold. Neither plan changes
parsing, which this plan leaves alone too.

## Design

### D1. A file's surface is a type

`FileSurface` is what later files may read of an earlier one. The per-file
transition (D4's `advance`) takes `&FileSurface`, and so does every
cross-file read a request makes, `ResolvedProject::item_def` included. The
surface therefore carries the file's declaration defs (D2), its qualified
name and its pairing, besides the fields under "What a later file reads from
an earlier one".

Its contents are not taken from that list. They are whatever makes the
transition and the cross-file reads compile once they are handed only a
`FileSurface`. The compiler then enforces what is today a fact found by
reading: nothing downstream of a file reads anything its surface does not
carry. A new threaded field has to be added to the surface, and the
surface's oracle (D3) then covers it.

### D2. Declaration ids do not depend on bodies

A def interned while the walk is inside an expression is a *local* def. Every
other def is a *declaration* def. `DefId` carries which space it belongs to,
and the arena keeps the two apart, so declaration defs are numbered in the
order the declaration walk meets them, whether or not bodies are walked.

That makes the surface of a full walk equal to the surface of a walk that
skips bodies exactly, with no masking. It also means a later file's reference
to `(file, DefId)` is valid against either walk's arena. Every export and
placed type names a declaration def. A debug assertion in `finish` holds that.

The alternative was to re-walk declarations and map binders by range onto a
seeded arena. It pays a second declaration walk and a range map on every full
walk, for the same guarantee.

### D3. The surface walk is the same walk, with expressions skipped

One walk with a mode, not a second implementation. The resolver's
`walk_bodies` field decides whether `resolve_expr` descends. There is no
thread-local and no second code path to keep in step. The surface walk's
result is a `FileSurface`.

**The property this rests on**: for every file `f` and entering state `p`,
`surface_walk(f, p) == full_walk(f, p).surface()`. The spike observed it on
one project. Stage 3 holds it over the corpora.

### D4. The fold folds surfaces, and a request resolves its own file

The fold over files `0..i` computes surfaces for `0..i-1` and a full walk for
`i`. The per-file transition becomes one function, `advance(state, surface)`,
shared by the cold fold, the incremental fold and the replay. It covers
everything the two folds do today after a file's walk: `thread_forward`,
signature materialisation, and the implicit-module shadow. Two copies of the
transition could disagree, and the replay would inherit whatever a copy
missed. The state entering any file `j` is `advance` replayed over the
surfaces before it. That is the fold's bookkeeping alone: the `semanticTokens
L` row's 7.04 G exceeds the per-file `resolve_file` sum, target included, by
under 0.3 G, and that difference also holds the request's own lookups, so it
is an upper bound. A full walk of an earlier file `j`, wanted by a later
request on `j`, runs against that replayed state.

Who needs what:

- **Semantic tokens, and definition's resolution branch**: the full walk of
  the request's file, and surfaces before it.
- **References**: the full walk of every file that may hold an occurrence,
  each against its own replayed state. That is today's cost, with the walks
  now independent of each other once the surfaces are known.
- **Inference requests** (hover, completion, definition's inference branch):
  full walks of the whole prefix, as today. A session whose first request is
  a hover pays what it pays today. D6 is what changes that.

The incremental fold's cutoff moves to surfaces: an edit whose surface is
unchanged leaves every later file's entering state unchanged, so no later
file is re-walked. Today that holds only when the re-walked file's exports
and contributions compare equal after a full walk.

The replay starts from the beginning each time. If a later measurement shows
the replay in the counts, the fold keeps entering states at checkpoints. That
is decided by measurement, not built ahead of it.

### D5. Per-block setup that does not depend on the file is computed once

- **The implicit auto-opens' seed** depends only on the env. The env computes
  it once and each block copies it in, as the env already memoises namespace
  fold surfaces (`docs/sema-interning-plan.md` Stage 2).
- **The own-namespace fold** entering file `j` is the fold entering file
  `j-1` with file `j-1`'s items of that namespace added. F#'s environment is
  latest-write-wins, so the fold can carry it forward in the threaded state
  rather than rebuild it per block. That holds only if the fold is
  append-only in Compile order. Barriers, generation stamps and shadow
  vetoes may break that, so Stage 6b starts by checking it. If it is not
  append-only, the fallback is a lookup tier that asks `ProjectItems` by name
  when a use reaches it, rather than materialising every item into the frame.

The old code stays as a test-only reference, as the interning plan's
Stage 2 kept its uncached scan.

### D6 (gated). Inference reads what the target uses

A file's inference reads `PrecedingTypes`, and not all of it per item:

- **Per item**: an earlier value's published type (`items`), a type by its
  place (`types`), a case by its id (`cases`), a record by its path
  (`records`). These the closure below can serve.
- **Whole prefix**: `constructor_name_count` counts every constructor-like
  declaration of a name in every earlier file, and `sealed_types` iterates
  every earlier case and record. An earlier file the target never references
  still moves these. An earlier `let Red = 0` makes a later `type Color = Red
  | Blue` followed by `let r = Red` withhold `r`'s type
  (`FileFacts::uncontested_case_name`), and leaving that file out infers
  `r : Color`.

The whole-prefix reads are about declarations: a name that is declared, and
a union or record that exists. If each of them can be computed from
declarations alone, they move into the surface and come from every earlier
file, while inferred value types come only from the files in the closure.
Any whole-prefix read that turns out to need inference rules this design
out, or widens the closure to every file that contributes to it.

The closure: a full walk of the target names exactly the earlier items it
references. The files whose inference it needs are the files that declare
those items, closed over the same relation for each of their bodies. The
unit is a whole file, since that is `infer_project`'s unit today. Inference
within a file stays as it is, so whether a value's type is fixed by a later
binding in the same file, or by its recursive group, is not this design's
concern.

Whether this pays depends on how large the closure is for real files. If a
typical file's closure is most of its prefix, it does not pay. Stage 7
audits the reads and measures the closure before anything is built.

## Implementation plan

> Implement this plan with each stage on its own branch, stacked as necessary
> on previous branches, so that a reviewer can review each branch in isolation.

Every stage lands alone on `main` with the full gate and the whole-project
gate green. Each reports `edit_counts` before and after on WoofWare.PawPrint2
(`EDIT_COUNTS_EARLY=1`, `EDIT_COUNTS_LATE` the last item) and on
WoofWare.Incremental, and restates its expected gain as a measurement.

### Stage 0: the fold count harness

**Dependencies**: none. **Implements**: the measurement every later stage
reports.

A `fold-counts` feature on `borzoi-sema`, off by default as `accessor-trace`
is on `borzoi-cst`, under which the fold records each file's retired
instructions per phase (the rows of the "Measurements" table). `edit_counts`
prints them when the feature is on. Instruction counts need macOS, as
`edit_counts`' do.

**Oracle**: it reproduces the "Measurements" table's "today" column on
WoofWare.PawPrint2 at 91e869b4, within the noise of the rows that read no
files.

### Stage 1: two id spaces

**Dependencies**: none. **Implements**: D2.

`DefId` carries its space. `Resolver::intern` takes it from whether the walk
is inside `resolve_expr`. The arena keeps the two apart, and `ResolvedFile::def`
reads either.

**Oracle**: every gate is unchanged. A manifest line moves only if it prints a
`DefId`'s index, and each such movement is listed in the PR. The debug
assertion that every export and placed type names a declaration def holds
over the corpora. A body edit that adds a local binder leaves every export's
`DefId` unchanged: a property over generated files, which fails before this
stage and passes after it.

### Stage 2: the surface type and the shared transition

**Dependencies**: Stage 1, so that the surface can carry the declaration
defs alone. **Implements**: D1, and D4's `advance`.

`FileSurface`, built in `finish`. The cold and incremental folds' per-file
steps become one `advance(state, &FileSurface)`. `ResolvedProject::item_def`
and the other cross-file reads take the surface. What the surface holds is
whatever makes these compile.

**Oracle**: it compiles with no field of `ResolvedFile` outside the surface
reachable from `advance` or from a cross-file read. Every gate is unchanged,
and every manifest moves zero lines.

### Stage 3: the surface walk, unconsumed

**Dependencies**: Stage 2. **Implements**: D3.

`surface_file(file, preceding, env) -> FileSurface`: the walk with
`walk_bodies` off. Nothing consumes it yet.

**Oracle**: D3's property with exact equality, over:

- every corpus file in isolation, beside `resolve_corpus_diff`;
- every file of every project in the whole-project gate, each against its
  real entering state;
- the generated files of `binder_site_grid` and of the contributor-name
  oracle's generator;
- generated projects with signature-paired implementations and unpaired
  headerless implementations, whose surfaces carry what signature
  materialisation and the implicit-module shadow read.

A planted body dependence must fail it: a walk that records an export from
inside a body, for example. The mutation is checked to have applied before
its failure is trusted.

### Stage 4: a target fold in sema

**Dependencies**: Stage 3. **Implements**: D4, sema side.

`resolve_target(files, i, env)` returns the surfaces of `0..i` and the full
walk of `i`. `ProjectSurfaces::entering(j)` replays the state entering `j`.
The incremental fold's cutoff moves to surface equality.

**Oracle**:

- For every horizon `i` of every project in the whole-project gate, and of
  generated projects, `resolve_target`'s full walk of `i` equals today's
  `resolve_project_files_prefix(files, i + 1, env).file(i)`.
- For every `j`, `ProjectSurfaces::entering(j)` equals the state the cold fold
  enters `j` with, and `item_def` answers every earlier item as the full fold
  does. The generated projects include signature-paired implementations,
  unpaired headerless implementations, and a headerless file renamed between
  two folds.
- The incremental fold's `incremental ≡ batch` differential holds with
  surfaces. A body edit that leaves the surface unchanged re-walks no later
  file.

### Stage 5: resolution requests use the target fold

**Dependencies**: Stage 4. **Implements**: D4, LSP side.

Semantic tokens and definition's resolution branch use the target fold.
References walks each file it reads against its replayed state. Inference
requests keep the full prefix.

**Oracle**: the whole-project gate (its `handler_diff` included) and
`incremental_state_machine` are unchanged.

**Expected**: the cold `semanticTokens L` row on WoofWare.PawPrint2 falls by
about 56% (7.04 G → about 3.1 G).

### Stage 6a: the implicit auto-opens' seed, once per env

**Dependencies**: none. **Implements**: D5's first half.

**Oracle**: a property test holds each block's seeded frame to the per-block
computation, kept as a test-only reference, over generated environments.
Every gate is unchanged.

**Expected**: about −0.17 G on the cold fold.

### Stage 6b: the own-namespace fold, carried forward

**Dependencies**: Stage 4, so that the carried state is the surface fold's.
**Implements**: D5's second half.

The stage first checks whether the fold is append-only. It records every
block's own-namespace fold and compares it with its predecessor's extended
by the files between, over the corpora. Whether the design carries the fold
forward or uses the lookup tier follows from that, and the stage says which
and why.

**Oracle**: the per-block fold is kept as a test-only reference. Each block's
resulting frame, or each lookup's answer through the tier, equals it over
generated multi-file projects whose files share namespaces, including
barriers and same-named blocks. Every gate is unchanged.

**Expected**: up to −1.13 G on the cold fold, and the fold stops being
quadratic in the project.

### Stage 7 (gated): the inference demand census, then the closure

**Dependencies**: Stage 5. **Implements**: D6.

7a first audits every read `infer_file` makes of `PrecedingTypes`. It
classifies each as per item or whole prefix, and for each whole-prefix read
says whether declarations alone determine it. That classification is held by
a property: inference whose whole-prefix facts come from every earlier
file's surface, and whose per-item facts come from every earlier file's
inference, equals today's. The `let Red = 0` case under D6 is one of its
fixtures. 7a then measures, for every file of every whole-project gate
project, the share of its prefix in its demand closure, and prints the
distribution. 7a states its threshold before measuring. 7b is built only if
the audit leaves D6 standing and the median share is small enough that a
hover-first session's cold cost falls by more than the bookkeeping adds.

**Oracle (7b)**: for every file, the hover and completion answers from the
closure's inference equal those from the whole prefix's inference, over the
whole-project gate and over generated projects that collide constructor
names across files the target does not reference.

### Expected end state

For the measured request, the fold's `resolve_file` work falls from about
6.75 G to about 1.6 G: surfaces 0.95 G, prescans 0.53 G, the target's own
walk, and what Stage 6 leaves of the per-block setup. Parsing then becomes
the largest cost of a first request, at about 510 instructions per byte
(`docs/token-pipeline-soa-plan.md`), or about 3.9 G over this project.

## Non-goals

- **Parsing.** An earlier file's bodies still have to be lexed and filtered
  to find where they end under the offside rule. A parse that skips building
  their trees is the next lever after this plan, and it needs its own oracle
  against the full parser.
- **Persisting derived values across restarts**, beyond the existing assembly
  cache.
- **Parallelism.** Once the surfaces are known, D4 makes files' full walks
  independent of each other. This plan does not use that.
- **Changing what any request answers.** Every stage is checked against the
  computation it replaces.
