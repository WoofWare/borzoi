# shellcheck shell=bash
#
# Reads one set out of `tools/mutants/sets.tsv` (its header has the format).
# Sourced by `inner.sh`, `run.sh` and `tools/ci/mutants.sh`.

# mutants_split_record LINE
#
# Splits a record at each tab into MUTANTS_RECORD, keeping empty fields (a tab
# is whitespace to `read`, which would merge two in a row), as
# `borzoi_oracle_harness::mutants::set_scope` splits it.
mutants_split_record() {
  local rest="$1"
  MUTANTS_RECORD=()
  while [[ "$rest" == *$'\t'* ]]; do
    MUTANTS_RECORD+=("${rest%%$'\t'*}")
    rest="${rest#*$'\t'}"
  done
  MUTANTS_RECORD+=("$rest")
}

# mutants_set_load SETS_TSV NAME
#
# Sets MUTANTS_SET_PACKAGE, MUTANTS_SET_GLOBS (an array), MUTANTS_SET_SKIPS
# (an array of test filters) and MUTANTS_SET_SKIP_REASONS (their reasons, in
# step). Returns 1, saying why on stderr, when NAME is not
# a set or a record is malformed.
mutants_set_load() {
  local tsv="$1" name="$2" kind rest n=0 found=0
  local -a fields
  MUTANTS_SET_PACKAGE=""
  MUTANTS_SET_GLOBS=()
  MUTANTS_SET_SKIPS=()
  MUTANTS_SET_SKIP_REASONS=()
  if [[ ! -f "$tsv" || ! -r "$tsv" ]]; then
    echo "sets.sh: cannot read $tsv" >&2
    return 1
  fi
  while IFS= read -r line || [[ -n "$line" ]]; do
    n=$((n + 1))
    [[ -z "$line" || "$line" == \#* ]] && continue
    mutants_split_record "$line"
    fields=("${MUTANTS_RECORD[@]}")
    kind="${fields[0]}"
    case "$kind" in
      set)
        if [[ ${#fields[@]} -ne 4 || -z "${fields[1]}" || -z "${fields[2]}" ]]; then
          echo "sets.tsv:$n: a set record has 4 fields (a name, a package and files)" >&2
          return 1
        fi
        if ! mutants_set_name_ok "${fields[1]}"; then
          echo "sets.tsv:$n: the set name '${fields[1]}' is not lowercase letters, digits and -" >&2
          return 1
        fi
        if [[ "${fields[1]}" == "$name" ]]; then
          if [[ $found -eq 1 ]]; then
            echo "sets.tsv:$n: set $name is declared twice" >&2
            return 1
          fi
          found=1
          MUTANTS_SET_PACKAGE="${fields[2]}"
          rest="${fields[3]}"
          read -r -a MUTANTS_SET_GLOBS <<<"$rest"
        fi
        ;;
      skip)
        if [[ ${#fields[@]} -ne 4 || -z "${fields[2]}" || -z "${fields[3]}" ]]; then
          echo "sets.tsv:$n: a skip record has 4 fields, the last its reason" >&2
          return 1
        fi
        if [[ "${fields[1]}" == "$name" ]]; then
          MUTANTS_SET_SKIPS+=("${fields[2]}")
          MUTANTS_SET_SKIP_REASONS+=("${fields[3]}")
        fi
        ;;
      *)
        echo "sets.tsv:$n: unknown record kind '$kind'" >&2
        return 1
        ;;
    esac
  done <"$tsv"
  if [[ $found -eq 0 ]]; then
    echo "sets.tsv: no set named '$name'" >&2
    return 1
  fi
  local names skipped
  names="$(mutants_set_names "$tsv")" || return 1
  while IFS= read -r line || [[ -n "$line" ]]; do
    mutants_split_record "$line"
    [[ "${MUTANTS_RECORD[0]:-}" == skip ]] || continue
    skipped="${MUTANTS_RECORD[1]:-}"
    if ! grep -qxF -- "$skipped" <<<"$names"; then
      echo "sets.tsv: a skip record names the undeclared set '$skipped'" >&2
      return 1
    fi
  done <"$tsv"
  if [[ ${#MUTANTS_SET_GLOBS[@]} -eq 0 ]]; then
    echo "sets.tsv: set $name names no files" >&2
    return 1
  fi
}

# mutants_set_name_ok NAME
#
# Whether NAME may name a set: lowercase letters, digits and `-`, starting with
# a letter or digit. A set's name becomes a file name (its manifest) and a
# directory name (its CI output, which is deleted before each run), so it must
# be one plain path component.
mutants_set_name_ok() {
  [[ "$1" =~ ^[a-z0-9][a-z0-9-]*$ ]]
}

# mutants_set_names SETS_TSV
#
# Prints every set's name, one per line, in file order. Returns 1, printing
# nothing, if any set's name is not one `mutants_set_name_ok` accepts.
mutants_set_names() {
  local line out=""
  local -a fields
  if [[ ! -f "$1" || ! -r "$1" ]]; then
    echo "sets.sh: cannot read $1" >&2
    return 1
  fi
  while IFS= read -r line || [[ -n "$line" ]]; do
    mutants_split_record "$line"
    fields=("${MUTANTS_RECORD[@]}")
    [[ "${fields[0]:-}" == set ]] || continue
    if ! mutants_set_name_ok "${fields[1]:-}"; then
      echo "sets.tsv: the set name '${fields[1]:-}' is not lowercase letters, digits and -" >&2
      return 1
    fi
    out+="${fields[1]}"$'\n'
  done <"$1"
  printf '%s' "$out"
}
