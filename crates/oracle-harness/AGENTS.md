# `borzoi-oracle-harness`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

Test-only. `BatchChild`:
a *resident* oracle (`fcs-dump …-batch`, `msbuild-condition-oracle`,
`nuget-oracle`) driven as a lock-step request/response loop, so .NET startup is
paid once per test binary rather than once per case. A wedged or crashed oracle
is killed, respawned and the request retried, then panics — bounded and loud
beats silent and forever. Builds on `borzoi-spawn`. Also `manifest`: the
exact per-item pin a deterministic corpus gate compares its run against (a
sorted line per item, a line diff on any movement, `BORZOI_UPDATE_MANIFESTS=1`
to regenerate) — the replacement for one-sided count ratchets — and
`corpus_key`, the host-independent spelling of a corpus file and position in
an entry (Nix's macOS `~nix~case~hack~` suffix decoded). And `nuget_oracle`,
the `tools/nuget-oracle` driver, which lives here because both
`borzoi-nuget`'s differentials and the LSP's restore-graph oracle drive it.
And `xml_pump`: every short element path of an XML input repeated thousands
of levels deep, run on a 2 MiB stack. `roxmltree` (≥ 0.21.2) parses
iteratively, so a deep file overflows only through a walk of ours that
recurses per element; `borzoi-msbuild`'s `xml_nesting_pump` and
`borzoi-nuget`'s `dgspec::xml_nesting_pump` hold every reader of untrusted
XML to that without naming the recursive paths. A new reader belongs in one.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-oracle-harness`; the repository's root `AGENTS.md` has the pre-push gate.
