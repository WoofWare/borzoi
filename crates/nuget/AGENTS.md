# `borzoi-nuget`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

NuGet primitives for the in-house
warm-cache restore (`docs/nuget-restore-plan.md`): the `NuGetVersion` /
`VersionRange` / `NuGetFramework` models, global-packages-folder and
`.nuspec` reading, the conservative offline resolver, and compile-asset
selection (NuGet's content model), and the dependency-graph spec reader
(`dgspec`, `docs/nuget-dgspec-boundary-plan.md`) and its resolver
(`dgspec::resolve_dgspec`), and NuGet's settings as far as the global
packages folder they choose (`settings::global_packages_folder`, which the
LSP's on-demand restore pins its package folder to; graded by
`settings_diff`). Everything either resolves
*identically* to `dotnet restore` or declines. `resolve_dgspec` commits only
for a NuGet on its verified list (`src/dgspec/verified_nuget.txt`), which
`dgspec_resolve_diff` derives from the oracle, so a devshell SDK bump fails
that test until the list is regenerated (the failure prints the command), and
regenerating it is the claim that the differential has graded the new NuGet.
It also takes the environment `restore.rs` spawns with
(`restore::restore_environment`): NuGet reads variables while restoring, and
an oracle child shares the test's environment, so only grading under each
variable (`restore_is_graded_under_every_environment_b1_admits`) and scanning
the verified NuGet for the names it reads makes that dependence visible.
The LSP runs `resolve_dgspec` in shadow on every on-demand restore
(`crates/lsp/src/restore/shadow.rs`): it serves the restore's answer and
logs a B₁ commit that differs from it as an error, so a B₁ bug on a real
project shows up in the server's log.
The other side of the spec, the start of A₁, is
`dgspec::write_restore_graph`. It takes the `_RestoreGraphEntry` items the
restore targets produce and returns the file `WriteRestoreGraphTask` would
save, as text. `restore_items_diff` holds it byte for byte to the task's
own code, through the oracle's `restoreGraphItems` op. Its text is NuGet's
writer output, which `parse_dgspec` then reads, so the writer's sorting,
dropping and grouping are modelled once, as text, and never re-derived as
values. It shares B₁'s verified list.
Self-contained: depends only
on `roxmltree` and `serde`/`serde_json`. It reads a file whole only through
`regular_file`, which declines a path that names no regular file rather than
open it (a FIFO's open waits for a writer); its `clippy.toml` bans the other
opens, and test code reads through `tests/all/common/host_fs.rs`.
Differentially tested against the real NuGet client libraries via
`tools/nuget-oracle` — a test-only JSONL batch oracle in the same mould as
`tools/fcs-dump`; it is never a runtime dependency of the LSP. The oracle
runs the NuGet *of the SDK `dotnet` resolves*, loaded from that SDK's
directory, not a package build: SDKs bundle unpublished release candidates,
so no package version is the NuGet `dotnet restore` runs.
`oracle_identity.rs` pins it.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-nuget`; the repository's root `AGENTS.md` has the pre-push gate.

This crate's CI job also runs ignored sweeps, which `cargo test` skips. Run them before pushing:

```sh
bash tools/ci/corpus-sweeps.sh nuget            # all of them
bash tools/ci/corpus-sweeps.sh --list nuget     # their names, to run one
```

Read first:

- `docs/nuget-restore-plan.md`, `docs/nuget-dgspec-boundary-plan.md`
