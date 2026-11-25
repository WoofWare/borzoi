# `borzoi-corpus-diff`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

Test-only, unpublished: an
empirical whole-project name-resolution differential. It loads real F#
projects through the same runtime path the LSP uses (`Workspace` +
project-assets closure + the sema fold), asks FCS for symbol uses, and
compares the two — without letting skipped or erroring projects masquerade as
agreement. Each comparable project is then put to the real request handlers
over the protocol (`handler_diff.rs`): definition, hover and references at
the first, middle and last character of FCS's records, positions converted by
an independent UTF-16 implementation, and again on a copy with non-ASCII text
substituted into comments and strings, which FCS checks too. Depends on
`borzoi`, `borzoi-cst`, `borzoi-msbuild`,
`borzoi-sema`, and `borzoi-spawn` (the `fcs-dump` driver lives in
its library, not its tests, so it is a regular dependency); driven by
`docs/project-corpus-diff-runner.md`.

It also drives the project-graph oracle (`ProjectGraphOracle`,
`fcs-dump uses-project-graph-batch`, typed in
`borzoi_oracle_harness::project_graph`): FCS checking a project with each
F# project reference handed to it from source, as an `FSharpReference`,
which is the semantics borzoi resolves `<ProjectReference>`s against. A
request is a value per project (id, assembly name, target, language
version, sources, defines, references) and `fcs-dump` builds the argument
vector from one template, so no compiler switch crosses the wire; its
`compile` op builds a DLL with FCS's own compiler on the same vector, and
its `referenced` op reports what a dependant reads of a project from source
(held to FCS by `crates/sema/tests/all/referenced_oracle.rs`). Each request
is answered from fresh checker state, and a type provider is refused as a
reference.
`tests/project_resolution/source_references.rs` holds it to **D1(G, C)**:
over generated graphs G (`tests/project_resolution/source_reference_gen.rs`:
every declaration kind a library exports, `.fsi` hiding, `internal` with and
without `InternalsVisibleTo`, names colliding with FSharp.Core, a middle
project, an export that depends on the library's defines), in currency C
(the consumer's whole-project file records and diagnostics), the answer with
each reference from source equals the answer with each reference as the DLL
FCS compiled. Its one assumption is that FCS's check and FCS's compile agree
on one argument vector; it claims nothing about any real build. The file
records come from the whole-project check, not FCS's per-file check (which
defines `EDITING`). Each case must bind its exact anchors (names unique by
construction) and hold at least one record of the library; the pinned
default run's census of records binding into the library, keyed by what FCS
reports of them, is pinned. That is all it claims about coverage: not that
each generated declaration was reached. `deep_` runs 200 cases
(`BORZOI_SOURCE_REF_SEED`, `BORZOI_SOURCE_REF_CASES`), and the
whole-project gate skips it.

`tests/project_resolution/fcs_dump_boundary.rs` holds `fcs-dump`'s resident
ops to the hostile-value library (`crates/oracle-harness/AGENTS.md`): every
wire mutation of a good request to `file-batch`, `uses-project-batch`,
`xmldoc-batch` and `uses-project-graph-batch`, through `BatchChild` and
straight to the oracle (census `fcs_dump_wire`), and every file-system
state, change, name, spelling and source mutation of a small project to
`uses-project-batch`, where a resident child must answer as a fresh one
does (census `fcs_dump_project`). `BORZOI_HOSTILE_CASES=<text>` narrows the
project census to the cases whose description holds the text, for
iterating; such a run fails once it is done, whatever it reached.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-corpus-diff`; the repository's root `AGENTS.md` has the pre-push gate.

Read first:

- `docs/project-corpus-diff-runner.md`
- skill: `resolution-explain`
