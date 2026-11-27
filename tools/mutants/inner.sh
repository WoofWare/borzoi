#!/usr/bin/env bash
#
# Runs cargo-mutants over one set of `tools/mutants/sets.tsv` and leaves its
# `mutants.out`, the `--list` output it graded (`listed.txt`) and a
# `run-info.tsv` in OUT_DIR:
#
#   inner.sh SET OUT_DIR
#
# It runs only inside a sandbox `canary.sh` allows: `tools/mutants/run.sh`'s
# container, which calls it with the devshell's environment in
# `$BORZOI_MUTANTS_DEV_ENV`, or a CI job (`tools/ci/mutants.sh`), which calls
# it under `nix develop`. It is not meant to be run by hand; `run.sh` and
# `tools/ci/mutants.sh` turn its output into the set's manifest.
#
# Exit status:
#   0   the run completed (survivors are the manifest's business, not this
#       script's)
#   2   usage: an unknown set, or a malformed `sets.tsv`
#   94  the unmutated baseline failed, so no mutant was graded
#   95  the set's globs name no mutant
#   97  refused: not in a sandbox (`canary.sh`)
#   1   anything else cargo-mutants reported
#
# `BORZOI_MUTANTS_JOBS` (default 2) is cargo-mutants' `--jobs`.
set -euo pipefail
unset CDPATH

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"

# shellcheck source=tools/mutants/canary.sh
source "$here/canary.sh"
mutants_canary_check inner.sh

if [[ $# -ne 2 ]]; then
  echo "usage: inner.sh SET OUT_DIR" >&2
  exit 2
fi
set_name="$1"
out_dir="$2"

# shellcheck source=tools/mutants/sets.sh
source "$here/sets.sh"
mutants_set_load "$repo/tools/mutants/sets.tsv" "$set_name" || exit 2

if [[ -n "${BORZOI_MUTANTS_DEV_ENV:-}" ]]; then
  # `nix print-dev-env`'s output: it sets PATH and the rest, then runs the
  # devshell's shellHook. It is not written for `set -eu`.
  set +eu
  # shellcheck disable=SC1090
  source "$BORZOI_MUTANTS_DEV_ENV"
  set -eu
fi
command -v cargo-mutants >/dev/null || {
  echo "inner.sh: cargo-mutants is not on PATH; run under the devshell" >&2
  exit 1
}

# cargo-mutants copies the tree and builds each copy in its own target dir; a
# target dir from the environment would be shared by all of them.
unset CARGO_TARGET_DIR CARGO_BUILD_TARGET_DIR
# The suite under test must be the suite a check runs: under
# `BORZOI_UPDATE_MANIFESTS` the package's own exact-manifest tests would rewrite
# their manifests rather than compare them. Only the set's own manifest step,
# after this script, honours it.
unset BORZOI_UPDATE_MANIFESTS
# proptest seeds from the OS by default, which would let one mutant be caught
# on one run and missed on the next. A fixed seed makes the verdicts a
# function of the tree.
export PROPTEST_RNG_SEED=0

args=(--no-shuffle --package "$MUTANTS_SET_PACKAGE")
for glob in "${MUTANTS_SET_GLOBS[@]}"; do
  args+=(--file "$glob")
done
# After cargo-mutants' own `--`, the arguments of `cargo test`: `--tests`
# leaves out doctests, which rustdoc runs without the cargo runner and so
# without the canary; after cargo's `--`, the skips go to each test binary.
test_args=(--tests)
if [[ ${#MUTANTS_SET_SKIPS[@]} -gt 0 ]]; then
  test_args+=(--)
  for skip in "${MUTANTS_SET_SKIPS[@]}"; do
    test_args+=(--skip "$skip")
  done
fi

cd "$repo"
mkdir -p "$out_dir"

cargo mutants "${args[@]}" --list >"$out_dir/listed.txt"
count="$(grep -c . "$out_dir/listed.txt" || true)"
if [[ "$count" -eq 0 ]]; then
  echo "inner.sh: set $set_name names no mutant (package $MUTANTS_SET_PACKAGE, files ${MUTANTS_SET_GLOBS[*]})" >&2
  exit 95
fi

{
  printf 'set\t%s\n' "$set_name"
  printf 'commit\t%s\n' "${BORZOI_MUTANTS_COMMIT:?BORZOI_MUTANTS_COMMIT names the commit measured}"
  printf 'package\t%s\n' "$MUTANTS_SET_PACKAGE"
  printf 'files\t%s\n' "${MUTANTS_SET_GLOBS[*]}"
  for i in "${!MUTANTS_SET_SKIPS[@]}"; do
    printf 'skip\t%s\t%s\n' "${MUTANTS_SET_SKIPS[$i]}" "${MUTANTS_SET_SKIP_REASONS[$i]}"
  done
} >"$out_dir/run-info.tsv"

status=0
cargo mutants "${args[@]}" \
  --jobs "${BORZOI_MUTANTS_JOBS:-2}" \
  --output "$out_dir" \
  -- "${test_args[@]}" || status=$?

case "$status" in
  # 2: some mutants were missed; 3: some timed out. Both are verdicts.
  0 | 2 | 3) exit 0 ;;
  4)
    echo "inner.sh: the unmutated baseline failed for set $set_name; no mutant was graded" >&2
    exit 94
    ;;
  *)
    echo "inner.sh: cargo-mutants exited $status" >&2
    exit 1
    ;;
esac
