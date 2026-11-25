#!/usr/bin/env bash
# CI's mutation stage: runs one set of `tools/mutants/sets.tsv` on the runner
# and checks its exact manifest (`tools/mutants/manifests/<set>.txt`).
#
#   tools/ci/mutants.sh SET
#   tools/ci/mutants.sh --list     the sets, one per line (the job's matrix)
#
# The runner is the sandbox here: an ephemeral GitHub-hosted VM in a job of its
# own, which bounds the run's memory, and `timeout-minutes` with the `timeout`
# below bound its time. That job's environment sets `BORZOI_MUTANTS_CI_JOB=true`
# and no other job's does; `tools/mutants/canary.sh` refuses the run anywhere
# else, a self-hosted runner included. On a Mac,
# run `tools/mutants/run.sh SET` instead, which runs the same `inner.sh` in a
# Linux container.
#
# Run it outside `nix develop`: each step enters the devshell itself.
# `BORZOI_MUTANTS_TIMEOUT` (default 5h) bounds the cargo-mutants run, and
# `BORZOI_MUTANTS_JOBS` (default 2) is its `--jobs`. The run's output stays
# under `$RUNNER_TEMP/mutants/SET` for the job to upload.
set -euo pipefail
unset CDPATH
# Git's repository-local variables would point `git rev-parse HEAD` below at
# another repository.
# shellcheck disable=SC2046
unset $(git rev-parse --local-env-vars)

repo="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo"

# shellcheck source=tools/mutants/sets.sh
source tools/mutants/sets.sh

if [[ "${1:-}" == --list ]]; then
  mutants_set_names tools/mutants/sets.tsv || exit 2
  exit 0
fi
if [[ $# -ne 1 ]]; then
  echo "usage: tools/ci/mutants.sh SET | --list" >&2
  exit 2
fi
set_name="$1"
mutants_set_load tools/mutants/sets.tsv "$set_name" || exit 2
# Refuse anywhere but CI's mutation job before touching an earlier run's
# output; `inner.sh` checks again inside the devshell.
# shellcheck source=tools/mutants/canary.sh
source tools/mutants/canary.sh
mutants_canary_check tools/ci/mutants.sh

out="${RUNNER_TEMP:-${TMPDIR:-/tmp}}/mutants/$set_name"
rm -rf "$out"
mkdir -p "$out"
commit="$(git rev-parse HEAD)"

BORZOI_MUTANTS_COMMIT="$commit" timeout --kill-after=60 "${BORZOI_MUTANTS_TIMEOUT:-5h}" \
  nix develop --command bash tools/mutants/inner.sh "$set_name" "$out/run"
nix develop --command cargo run --quiet -p borzoi-oracle-harness --bin mutants-manifest -- \
  "$set_name" "$out" "$repo"
