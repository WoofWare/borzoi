#!/usr/bin/env bash
# Record a baseline revision's walk over the points that
# `path_fixup_expansion_diff`'s fixed seed generates, into
# crates/msbuild/tests/manifests/path_fixup_baseline.txt.
#
# Usage: bash tools/path-fixup-baseline.sh <baseline-revision>
#
# The fixed-seed sweep holds the walk under test to that file: a claim the
# baseline made rightly, or declined, must not be one the walk under test
# makes wrongly. Rerun it whenever the generator moves (the sweep says so),
# with the revision the branch builds on (its merge base with main).
#
# Run it outside `nix develop`: it enters the devshell itself.
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <baseline-revision>" >&2
  exit 2
fi
root=$(git rev-parse --show-toplevel)
rev=$(git -C "$root" rev-parse --verify "$1^{commit}")
work=$(mktemp -d)
dump="$work/dump"
base="$work/base"
mkdir "$dump"
cleanup() {
  git -C "$root" worktree remove --force "$base" 2>/dev/null || true
  rm -rf "$work"
}
trap cleanup EXIT

echo "dumping the fixed seed's points" >&2
(cd "$root" && BORZOI_PATH_FIXUP_DUMP="$dump" nix develop -c \
  cargo test -p borzoi-msbuild --test path_fixup_expansion_diff \
  fixed_seed_sweep_regresses_nothing_main_answers -- --exact --nocapture) >"$work/dump.log" 2>&1 || {
  # The sweep fails on a stale baseline after it has dumped every point;
  # anything else is a failure of its own.
  if ! grep -q "the baseline does not hold" "$work/dump.log"; then
    cat "$work/dump.log" >&2
    exit 1
  fi
}

echo "walking them at $rev" >&2
git -C "$root" worktree add --detach "$base" "$rev" >/dev/null
cp "$root/crates/msbuild/tests/path_fixup_baseline.rs" "$base/crates/msbuild/tests/"
(cd "$base" && BORZOI_PATH_FIXUP_DUMP="$dump" CARGO_INCREMENTAL=0 \
  CARGO_TARGET_DIR="${BORZOI_BASELINE_TARGET_DIR:-$work/target}" nix develop -c \
  cargo test -p borzoi-msbuild --test path_fixup_baseline -- --ignored --exact record_baseline) \
  >"$work/base.log" 2>&1 || {
  cat "$work/base.log" >&2
  exit 1
}

out="$root/crates/msbuild/tests/manifests/path_fixup_baseline.txt"
{
  echo "# The walk at $rev over path_fixup_expansion_diff's fixed-seed points:"
  echo "# case, FNV-1a of its text (root spelt {ROOT}), each mode's claim."
  echo "# Regenerate: bash tools/path-fixup-baseline.sh $rev"
  cat "$dump/baseline.txt"
} >"$out"
echo "wrote $out" >&2
