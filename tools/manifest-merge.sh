#!/usr/bin/env bash
# Git merge driver for the exact manifests (`borzoi_oracle_harness::manifest`):
# merges them as keyed line sets, so two branches that moved different items
# merge without regenerating, and fails when both moved the same item
# differently. `.gitattributes` names the keyed manifests it serves; enable it
# once per clone with
#
#   git config merge.borzoi-manifest.driver 'bash tools/manifest-merge.sh %O %A %B %P'
#
# Git runs it from the top of the worktree being merged into, so it builds the
# driver that worktree checks out. CI's gates stay the judge of the merged
# manifest: a clean merge here says only that no item moved two ways.
#
# The devshell points cargo at an offline registry vendored from one
# `Cargo.lock`, and records that lock's hash in `BORZOI_CARGO_LOCK_SHA256`. The
# shell git inherits may have been entered on another revision or in another
# worktree, and its registry then lacks crates this lock names. So the ambient
# cargo is used only when the hashes match; otherwise `nix develop` enters this
# worktree's devshell.
set -euo pipefail

sha256() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | cut -d' ' -f1
    else
        shasum -a 256 "$1" | cut -d' ' -f1
    fi
}

cmd=(cargo run --quiet --release --locked -p borzoi-oracle-harness --bin manifest-merge -- "$@")
if command -v cargo >/dev/null 2>&1 &&
    [[ -n "${BORZOI_CARGO_LOCK_SHA256:-}" ]] &&
    [[ "$BORZOI_CARGO_LOCK_SHA256" == "$(sha256 Cargo.lock)" ]]; then
    exec "${cmd[@]}"
else
    exec nix develop --command "${cmd[@]}"
fi
