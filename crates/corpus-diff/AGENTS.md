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

`tests/project_resolution/fcs_dump_boundary.rs` holds `fcs-dump`'s resident
ops to the hostile-value library (`crates/oracle-harness/AGENTS.md`): every
wire mutation of a good request to `file-batch`, `uses-project-batch` and
`xmldoc-batch`, through `BatchChild` and straight to the oracle
(census `fcs_dump_wire`), and every file-system state, change, name,
spelling and source mutation of a small project to `uses-project-batch`,
where a resident child must answer as a fresh one does (census
`fcs_dump_project`). `BORZOI_HOSTILE_CASES=<text>` narrows the project
census to the cases whose description holds the text, for iterating; the
census then fails.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-corpus-diff`; the repository's root `AGENTS.md` has the pre-push gate.

Read first:

- `docs/project-corpus-diff-runner.md`
- skill: `resolution-explain`
