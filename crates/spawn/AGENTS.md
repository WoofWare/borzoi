# `borzoi-spawn`

Paths that start `docs/`, `tools/`, `crates/` or `nix/` are from the repository root; the others are from this crate's directory.

The one place in the workspace a child
process is spawned: the process-global spawn lock (macOS leaks raw pipe
descriptors between concurrent spawns, which hangs the reader of an *exited*
child — see the crate docs), and `BoundedCommand`, which runs a child under a
deadline with its stdin streamed and both output pipes drained. Everything that
shells out goes through it — the LSP library, every test harness, the oracle
drivers — because a per-crate lock is not an exclusion. `clippy.toml` bans
direct `Command::{spawn,status,output}` to enforce that. No dependencies.

## Working here

Iterate with `nix develop -c cargo test -p borzoi-spawn`; the repository's root `AGENTS.md` has the pre-push gate.
