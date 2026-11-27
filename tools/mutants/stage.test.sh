#!/usr/bin/env bash
#
# Tests for `stage.sh`: what it copies out of a mutation run's directory, and
# what it refuses.

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
fails=0

assert_eq() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf 'ok   - %s\n' "$1"
  else
    printf 'FAIL - %s\n    expected: [%s]\n    actual:   [%s]\n' "$1" "$2" "$3"
    fails=$((fails + 1))
  fi
}

# shellcheck source=tools/mutants/stage.sh
source "$here/stage.sh"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/work/run" "$tmp/out" "$tmp/outside"
work="$(cd "$tmp/work" && pwd -P)"
printf 'secret' >"$tmp/outside/secret"
printf 'fine' >"$work/run/ok"
printf '0123456789' >"$work/run/ten"
ln -s "$tmp/outside/secret" "$work/run/link-out"
ln -s "$work/run/ok" "$work/run/link-in"
ln -s "$tmp/outside" "$work/run/dir-out"
mkfifo "$work/run/fifo"
mkdir "$work/run/dir"

staged() { # src dest limit [whole]
  rm -f "$tmp/out/dest"
  mutants_stage "$work" "$1" "$tmp/out/dest" "$2" "${3:-}" 2>/dev/null
  if [[ -f "$tmp/out/dest" ]]; then cat "$tmp/out/dest"; else printf '<none>'; fi
}

assert_eq "a regular file is copied" fine "$(staged "$work/run/ok" 100)"
assert_eq "a file over the limit is cut to it" 01234 "$(staged "$work/run/ten" 5)"
assert_eq "with whole, a file over the limit is not copied" '<none>' "$(staged "$work/run/ten" 5 whole)"
assert_eq "with whole, a file within the limit is copied" 0123456789 "$(staged "$work/run/ten" 10 whole)"
assert_eq "a link out of the run is not followed" '<none>' "$(staged "$work/run/link-out" 100)"
assert_eq "a path through a linked directory is not followed" '<none>' "$(staged "$work/run/dir-out/secret" 100)"
assert_eq "a FIFO is not read" '<none>' "$(staged "$work/run/fifo" 100)"
assert_eq "a directory is not copied" '<none>' "$(staged "$work/run/dir" 100)"
assert_eq "a missing file is skipped" '<none>' "$(staged "$work/run/absent" 100)"
# A link that stays inside the run names a file the run wrote anyway.
assert_eq "a link within the run is copied" fine "$(staged "$work/run/link-in" 100)"

if [[ $fails -ne 0 ]]; then
  echo "$fails failure(s)"
  exit 1
fi
echo "all passed"
