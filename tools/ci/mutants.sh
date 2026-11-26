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
# `BORZOI_MUTANTS_JOBS` (default 2) is its `--jobs`.
#
# The run writes under `$RUNNER_TEMP/mutants-work/SET`, where mutant code can
# leave anything. What the manifest step reads is staged out of it into
# `$RUNNER_TEMP/mutants/SET`, made fresh after the run: the run's three
# artifacts and cargo-mutants' logs, each copied only if it is a regular file
# inside the work directory, the artifacts whole up to 64 MiB and each log's
# first MiB. The job uploads nothing the run wrote; a failure is reproduced
# with `tools/mutants/run.sh SET`.
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
  names="$(mutants_set_names tools/mutants/sets.tsv)" || exit 2
  if [[ -z "$names" ]]; then
    echo "tools/ci/mutants.sh: sets.tsv declares no set" >&2
    exit 2
  fi
  printf '%s\n' "$names"
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

base="${RUNNER_TEMP:-${TMPDIR:-/tmp}}"
work="$base/mutants-work/$set_name"
out="$base/mutants/$set_name"
rm -rf "$work" "$out"
mkdir -p "$work"
work="$(cd "$work" && pwd -P)"
commit="$(git rev-parse HEAD)"

status=0
BORZOI_MUTANTS_COMMIT="$commit" timeout --kill-after=60 "${BORZOI_MUTANTS_TIMEOUT:-5h}" \
  nix develop --command bash tools/mutants/inner.sh "$set_name" "$work/run" || status=$?

# The upload directory is made only now the run is over, and fresh: anything a
# mutant left at its path is gone, and only staged files go in.
rm -rf "$out"
mkdir -p "$out/run/mutants.out/log"

# shellcheck source=tools/mutants/stage.sh
source tools/mutants/stage.sh
for rel in run-info.tsv listed.txt mutants.out/outcomes.json; do
  mutants_stage "$work" "$work/run/$rel" "$out/run/$rel" $((64 << 20)) whole
done
shopt -s nullglob
for log in "$work"/run/mutants.out/log/*.log; do
  mutants_stage "$work" "$log" "$out/run/mutants.out/log/$(basename "$log")" $((1 << 20))
done
shopt -u nullglob

if [[ $status -ne 0 ]]; then
  echo "tools/ci/mutants.sh: the run exited $status" >&2
  exit "$status"
fi
nix develop --command cargo run --quiet -p borzoi-oracle-harness --bin mutants-manifest -- \
  "$set_name" "$out" "$repo"
