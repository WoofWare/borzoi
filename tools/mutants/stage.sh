# shellcheck shell=bash
#
# Copies the artifacts a mutation run left out of the directory it wrote into
# a directory that holds only bounded regular files, so a run that went wrong
# (left an artifact missing, truncated or huge) is refused cleanly. Sourced by
# `tools/ci/mutants.sh`.

# mutants_stage WORK SRC DEST LIMIT [whole]
#
# Copies SRC to DEST if SRC is a regular file whose real path lies inside the
# directory WORK (itself a real path): the whole file when it is at most LIMIT
# bytes, and otherwise its first LIMIT bytes, or, with `whole`, nothing. Says
# on stderr why it skipped a file that exists; a missing SRC is skipped
# quietly. Always returns 0: staging is best effort, and the manifest step
# judges what arrived.
mutants_stage() {
  local work="$1" src="$2" dest="$3" limit="$4" mode="${5:-}" real
  [[ -e "$src" || -L "$src" ]] || return 0
  # `realpath` and `wc` as both GNU and BSD spell them: SRC is absolute.
  if ! real="$(realpath "$src" 2>/dev/null)" || [[ "$real" != "$work"/* ]]; then
    echo "stage.sh: $src leads outside $work; not staged" >&2
    return 0
  fi
  if [[ ! -f "$real" ]]; then
    echo "stage.sh: $src is not a regular file; not staged" >&2
    return 0
  fi
  if [[ $mode == whole && "$(wc -c <"$real")" -gt $limit ]]; then
    echo "stage.sh: $src is over $limit bytes; not staged" >&2
    return 0
  fi
  head -c "$limit" -- "$real" >"$dest"
  return 0
}
