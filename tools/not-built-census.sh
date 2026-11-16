#!/usr/bin/env bash
# The not-built census (`crates/corpus-diff/src/not_built.rs`): every project
# in the pinned corpus's repositories that references an F# project, put
# through the LSP's runtime path with its references unbuilt and graded
# against FCS with each reference passed from source. A measurement, not a
# gate: it prints the numbers and fails only if it cannot run.
#
#   tools/not-built-census.sh [WORKDIR]
#
# The pinned corpus's checkouts must already be materialised in the shared
# cache, `${BORZOI_PROJECT_CORPUS_CACHE:-~/.cache/borzoi/project-corpus}/v2`
# (`bash tools/ci/project-corpus-gate.sh` does it). The census copies them into
# WORKDIR (a fresh temporary directory by default), deletes any build output so
# every reference is unbuilt, and restores each dependent project from
# nuget.org into WORKDIR's own packages folder. It never writes the shared
# cache: restoring a dependent restores its references too, which would
# rewrite assets files other runs are reading.
#
# Run it outside `nix develop`: it enters the devshell itself.
set -euo pipefail

repo="$(cd "$(dirname "$0")/.." && pwd)"
cache="${BORZOI_PROJECT_CORPUS_CACHE:-$HOME/.cache/borzoi/project-corpus}/v2/project-corpus"
work="${1:-$(mktemp -d)}"
mkdir -p "$work"
work="$(cd "$work" && pwd -P)"

if [ ! -d "$cache" ]; then
  echo "no materialised corpus at $cache; run tools/ci/project-corpus-gate.sh first" >&2
  exit 1
fi

rm -rf "$work/corpus"
mkdir -p "$work/corpus"
cp -R "$cache/." "$work/corpus/"
find "$work/corpus" -type d \( -name bin -o -name obj \) -prune -exec rm -rf {} +

# A dependent is any project that references an F# project.
dependents=()
while IFS= read -r project; do
  if grep -Eq '<ProjectReference[^>]*\.fsproj' "$project"; then
    dependents+=("$project")
  fi
done < <(find "$work/corpus" -name '*.fsproj' -not -path '*/.git/*' | sort)
echo "dependent projects: ${#dependents[@]}"

for project in "${dependents[@]}"; do
  nix develop "$repo" --command env \
    RestoreSources=https://api.nuget.org/v3/index.json \
    NUGET_PACKAGES="$work/packages" \
    dotnet restore "$project"
done

list="$(IFS=:; echo "${dependents[*]}")"
cd "$repo"
nix develop --command env \
  BORZOI_NOT_BUILT_PROJECT_LIST="$list" \
  cargo test -p borzoi-corpus-diff --test project_resolution not_built_census \
  -- --ignored --nocapture
