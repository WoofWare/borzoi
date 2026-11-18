#!/usr/bin/env bash
# The not-built census (`crates/corpus-diff/src/not_built.rs`): every project
# in the pinned corpus's repositories that references an F# project, put
# through the LSP's runtime path with its references unbuilt and graded
# against FCS with each reference passed from source. A measurement, not a
# gate: it prints the numbers and fails only if it cannot run.
#
#   tools/not-built-census.sh [PARENT]
#
# The pinned corpus's repositories must already be materialised in the shared
# cache, `${BORZOI_PROJECT_CORPUS_CACHE:-~/.cache/borzoi/project-corpus}/v2`
# (`bash tools/ci/project-corpus-gate.sh` does it). The census clones each
# pinned repository out of that cache at its pinned revision
# (`nix/project-corpus.json`) into a fresh directory of its own under PARENT
# (the system temporary directory by default), so nothing that directory
# already holds is touched, the cache's working trees are never read, and an
# unbuilt checkout is what is measured. It then restores every project of
# those repositories from nuget.org into that directory's own packages
# folder; the shared cache is never written. Which projects are dependents is
# decided by evaluation, in the census itself.
#
# Run it outside `nix develop`: it enters the devshell itself.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cache="${BORZOI_PROJECT_CORPUS_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/borzoi/project-corpus}/v2/project-corpus"
parent="${1:-${TMPDIR:-/tmp}}"
mkdir -p "$parent"
work="$(mktemp -d "$parent/not-built-census.XXXXXX")"
work="$(cd "$work" && pwd -P)"
echo "census directory: $work"

target="${CARGO_TARGET_DIR:-$repo/target}"
(cd "$repo" && nix develop --command cargo build --locked -p borzoi-stats)
plan="$work/plan.tsv"
(cd "$repo" && "$target/debug/borzoi-stats" corpus --pins nix/project-corpus.json --emit plan) >"$plan"

while IFS=$'\t' read -r repository revision _project; do
  dest="$work/corpus/$repository"
  [ -e "$dest" ] && continue
  if [ ! -d "$cache/$repository/.git" ]; then
    echo "$repository is not materialised in $cache; run tools/ci/project-corpus-gate.sh first" >&2
    exit 1
  fi
  mkdir -p "$(dirname "$dest")"
  git clone --quiet --no-checkout "$cache/$repository" "$dest"
  git -C "$dest" checkout --quiet --detach "$revision"
  test "$(git -C "$dest" rev-parse HEAD)" = "$revision"
done <"$plan"

# Every project, so the census can evaluate each one and decide by its
# compile graph whether it is a dependent. A project that fails to restore
# is reported by the census rather than stopping it.
while IFS= read -r project; do
  nix develop "$repo" --command env \
    RestoreSources=https://api.nuget.org/v3/index.json \
    NUGET_PACKAGES="$work/packages" \
    dotnet restore "$project" || echo "restore failed: $project" >&2
done < <(find "$work/corpus" -name '*.fsproj' -not -path '*/.git/*' | sort)

cd "$repo"
nix develop --command env \
  BORZOI_NOT_BUILT_ROOT="$work/corpus" \
  cargo test --profile gate -p borzoi-corpus-diff --test project_resolution not_built_census \
  -- --ignored --nocapture
