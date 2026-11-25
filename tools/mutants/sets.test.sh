#!/usr/bin/env bash
#
# Tests for `sets.sh`, the reader of `tools/mutants/sets.tsv`: what it loads,
# what it refuses, and that the checked-in table loads whole.

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

# shellcheck source=tools/mutants/sets.sh
source "$here/sets.sh"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
T=$'\t'

{
  printf '# a comment\n\n'
  printf 'set%sa%spkg-a%ssrc/x.rs src/y/*.rs\n' "$T" "$T" "$T"
  printf 'set%sb%spkg-b%ssrc/z.rs\n' "$T" "$T" "$T"
  printf 'skip%sa%snet_%sreaches nuget.org\n' "$T" "$T" "$T"
  printf 'skip%sa%sslow::%sover the time bound\n' "$T" "$T" "$T"
} >"$tmp/good.tsv"

mutants_set_load "$tmp/good.tsv" a
assert_eq "loads a set" 0 "$?"
assert_eq "its package" pkg-a "$MUTANTS_SET_PACKAGE"
assert_eq "its globs" "src/x.rs src/y/*.rs" "${MUTANTS_SET_GLOBS[*]}"
assert_eq "its skips" "net_ slow::" "${MUTANTS_SET_SKIPS[*]}"
assert_eq "their reasons" "reaches nuget.org|over the time bound" \
  "$(IFS='|'; echo "${MUTANTS_SET_SKIP_REASONS[*]}")"

mutants_set_load "$tmp/good.tsv" b
assert_eq "another set's skips are not this one's" 0 "${#MUTANTS_SET_SKIPS[@]}"
assert_eq "lists the sets in order" "a b" "$(mutants_set_names "$tmp/good.tsv" | tr '\n' ' ' | sed 's/ $//')"

refuses() { # name file set
  mutants_set_load "$2" "$3" 2>/dev/null
  assert_eq "refuses: $1" 1 "$?"
}
refuses "an unknown set" "$tmp/good.tsv" c
cp "$tmp/good.tsv" "$tmp/twice.tsv"
printf 'set%sa%spkg%ssrc/w.rs\n' "$T" "$T" "$T" >>"$tmp/twice.tsv"
refuses "a set declared twice" "$tmp/twice.tsv" a
cp "$tmp/good.tsv" "$tmp/orphan.tsv"
printf 'skip%sc%sx%swhy\n' "$T" "$T" "$T" >>"$tmp/orphan.tsv"
refuses "a skip of an undeclared set" "$tmp/orphan.tsv" a
cp "$tmp/good.tsv" "$tmp/reasonless.tsv"
printf 'skip%sa%sx\n' "$T" "$T" >>"$tmp/reasonless.tsv"
refuses "a skip with no reason" "$tmp/reasonless.tsv" a
printf 'set%sa%spkg\n' "$T" "$T" >"$tmp/noglobs.tsv"
refuses "a set with no files" "$tmp/noglobs.tsv" a
printf 'sett%sa%spkg%sx.rs\n' "$T" "$T" "$T" >"$tmp/kind.tsv"
refuses "an unknown record kind" "$tmp/kind.tsv" a

# A table that cannot be read is an error, not an empty one: the CI matrix is
# its list.
mutants_set_names "$tmp/absent.tsv" >"$tmp/names.out" 2>/dev/null
assert_eq "listing an absent table fails" "1 " "$? $(cat "$tmp/names.out")"
refuses "an absent table" "$tmp/absent.tsv" a

# A set's name is one plain path component: it names a manifest file and a CI
# output directory that is deleted before each run.
for bad in ../a a/b . .. -a A "a b" "a.b"; do
  cp "$tmp/good.tsv" "$tmp/badname.tsv"
  printf 'set%s%s%spkg%sx.rs\n' "$T" "$bad" "$T" "$T" >>"$tmp/badname.tsv"
  refuses "the set name '$bad'" "$tmp/badname.tsv" a
  mutants_set_names "$tmp/badname.tsv" >"$tmp/names.out" 2>/dev/null
  assert_eq "listing refuses the set name '$bad'" "1 " "$? $(cat "$tmp/names.out")"
done

# A last record with no line break after it is still a set, both to load and to
# list (the CI matrix is the list).
printf 'set%sa%spkg%sx.rs\nset%sb%spkg%sy.rs' "$T" "$T" "$T" "$T" "$T" "$T" >"$tmp/unterminated.tsv"
assert_eq "an unterminated last set is listed" "a b" \
  "$(mutants_set_names "$tmp/unterminated.tsv" | tr '\n' ' ' | sed 's/ $//')"
mutants_set_load "$tmp/unterminated.tsv" b
assert_eq "an unterminated last set loads" "pkg y.rs" "$MUTANTS_SET_PACKAGE ${MUTANTS_SET_GLOBS[*]}"

# Two tabs in a row are an empty field, not one separator.
printf 'set%sa%s%spkg%sx.rs\n' "$T" "$T" "$T" "$T" >"$tmp/doubled.tsv"
refuses "an empty field" "$tmp/doubled.tsv" a

# The checked-in table: every set loads, and there is at least one. Whether a
# set's files name any mutant is cargo-mutants' question, by its own glob
# rules: `inner.sh` refuses a set that names none (exit 95).
names="$(mutants_set_names "$here/sets.tsv")"
assert_eq "sets.tsv declares a set" yes "$([[ -n "$names" ]] && echo yes || echo no)"
while IFS= read -r name; do
  mutants_set_load "$here/sets.tsv" "$name"
  assert_eq "sets.tsv: $name loads" 0 "$?"
done <<<"$names"

if [[ $fails -ne 0 ]]; then
  echo "$fails failure(s)"
  exit 1
fi
echo "all passed"
