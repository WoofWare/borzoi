#!/usr/bin/env bash
#
# Tests for corpus-sweeps.sh: `ci.yml` runs every ignored test through it,
# each step exactly once and from its own crate's job, and each step is a
# command the script knows.
#
# `nix` is replaced by a fake that prints what it was asked to run, so nothing
# here builds or tests anything.

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
ci="$repo/.github/workflows/ci.yml"
script="$here/corpus-sweeps.sh"
fails=0

assert_eq() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf 'ok   - %s\n' "$1"
  else
    printf 'FAIL - %s\n    expected: [%s]\n    actual:   [%s]\n' "$1" "$2" "$3"
    fails=$((fails + 1))
  fi
}

# The CI job that runs a crate's sweeps: the one its change filter gates.
job_of() {
  case "$1" in
    cst) echo test-cst ;;
    msbuild) echo test-msbuild ;;
    nuget) echo test-nuget ;;
    sema) echo test-sema-sweeps ;;
    lsp) echo test-lsp-sweeps ;;
    *) echo "no job for crate '$1'" ;;
  esac
}

# `JOB STEP` for every step a `run: bash tools/ci/corpus-sweeps.sh STEP...`
# line of `ci.yml` runs, in file order. Only that one-line form counts: inside
# a `run: |` block the line could be commented out, guarded or echoed, and
# telling those apart is parsing shell. `stray_mentions` refuses every other
# use of the script, so a step run any other way fails rather than counts.
ci_steps() {
  awk '
    /^  [A-Za-z0-9_-]+:$/ { job = $1; sub(/:$/, "", job) }
    /^ +run: bash tools\/ci\/corpus-sweeps\.sh( [a-z0-9-]+)+$/ {
      n = split($0, words, " ")
      for (i = 4; i <= n; i++) print job, words[i]
    }
  ' "$ci"
}

# `ci.yml`'s lines outside YAML comments, numbered.
code_lines() { grep -n -v '^ *#' "$ci"; }

stray_mentions() {
  code_lines | grep 'corpus-sweeps\.sh' |
    grep -Ev '^[0-9]+: +run: bash tools/ci/corpus-sweeps\.sh( [a-z0-9-]+)+$|^[0-9]+: +run: bash tools/ci/corpus-sweeps\.test\.sh$'
}

expected=""
while read -r crate step; do
  expected+="$(job_of "$crate") $step"$'\n'
done < <(bash "$script" --list)
expected="${expected%$'\n'}"

# Exact and in order: a step CI runs twice, from the wrong job (so under
# another crate's change filter), or never, is drift between the local list
# and the gate.
assert_eq "ci.yml runs every step once, from its crate's job, in list order" \
  "$expected" "$(ci_steps)"

assert_eq "ci.yml uses corpus-sweeps.sh only as a whole one-line run" "" \
  "$(stray_mentions)"

# Libtest runs ignored tests under either flag.
assert_eq "ci.yml runs no ignored test except through corpus-sweeps.sh" "" \
  "$(code_lines | grep -E -- '--ignored|--include-ignored')"

for crate in cst msbuild nuget sema lsp; do
  listed="$(bash "$script" --list "$crate")"
  assert_eq "crate $crate has steps" yes "$([[ -n "$listed" ]] && echo yes)"
done

assert_eq "--list refuses an unknown crate" 2 \
  "$(bash "$script" --list no-such-crate >/dev/null 2>&1; echo $?)"

fake="$(mktemp -d)"
printf '#!/usr/bin/env bash\necho ran\n' >"$fake/nix"
chmod +x "$fake/nix"
assert_eq "an unknown step is refused before any step runs" "2 " \
  "$(out="$(PATH="$fake:$PATH" bash "$script" parser-corpus no-such-step 2>/dev/null)"
    echo "$? $out")"
# A step name is matched literally, not as a pattern.
assert_eq "a step name with a regex metacharacter is refused before any step runs" "2 " \
  "$(out="$(PATH="$fake:$PATH" bash "$script" parser-corpus parser.corpus 2>/dev/null)"
    echo "$? $out")"

# Every listed step has a command, and it is an ignored cargo test.
cat >"$fake/nix" <<'EOF'
#!/usr/bin/env bash
[ "$1 $2" = "develop --command" ] || { echo "fake nix: unexpected $*" >&2; exit 99; }
shift 2
echo "$*"
EOF
chmod +x "$fake/nix"
while read -r _ step; do
  out="$(PATH="$fake:$PATH" bash "$script" "$step" 2>&1)"
  status=$?
  assert_eq "step $step runs an ignored cargo test" "0 yes" \
    "$status $([[ "$out" == "cargo test "*"-- --ignored --nocapture"* ]] && echo yes)"
done < <(bash "$script" --list)

# A crate argument selects exactly that crate's steps; more than one step keeps
# going past a failure and names it.
cat >"$fake/nix" <<'EOF'
#!/usr/bin/env bash
shift 2
echo "$*"
[[ "$*" != *parser_corpus_diff::* ]]
EOF
out="$(PATH="$fake:$PATH" bash "$script" cst 2>&1)"
status=$?
assert_eq "a failing step fails a multi-step run" 1 "$status"
assert_eq "every cst step ran despite the failure" \
  "$(bash "$script" --list cst | wc -l | tr -d ' ')" \
  "$(grep -c '^cargo test ' <<<"$out")"
assert_eq "the failed step is named" 1 \
  "$(grep -c 'failed steps: parser-corpus-diff$' <<<"$out")"
rm -rf "$fake"

if [[ $fails -gt 0 ]]; then
  printf '\n%d test(s) failed\n' "$fails"
  exit 1
fi
printf '\nall tests passed\n'
