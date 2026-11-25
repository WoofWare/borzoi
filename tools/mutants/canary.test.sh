#!/usr/bin/env bash
#
# Tests for the mutation-testing canary (`canary.sh`): its rule over every
# combination of the facts it reads; which environments count as CI's mutation
# job; that the cargo runner and `inner.sh` refuse, end to end, before running
# anything; and that Cargo really runs the canary under `.cargo/mutants.toml`'s
# arguments, as the workspace's rustc wrapper and, when that is overridden, as
# the runner, against a competing runner for the host's triple. Needs `cargo`
# and `rustc` on PATH (the devshell). It holds outside the sandbox and inside
# it alike, as each case clears the markers it does not set.

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
fails=0

assert_eq() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf 'ok   - %s\n' "$1"
  else
    printf 'FAIL - %s\n    expected: [%s]\n    actual:   [%s]\n' "$1" "$2" "$3"
    fails=$((fails + 1))
  fi
}

# shellcheck source=tools/mutants/canary.sh
source "$here/canary.sh"

# The rule, over all 3 × 2 × 2 × 2 fact combinations: allowed exactly when the
# kernel is Linux, the store is not writable, and a sandbox marker is present.
for kernel in Linux Darwin FreeBSD; do
  for store in yes no; do
    for nonce in yes no; do
      for ci in yes no; do
        expected=refuse
        if [[ $kernel == Linux && $store == no && ($nonce == yes || $ci == yes) ]]; then
          expected=allow
        fi
        verdict="$(mutants_canary_decide "$kernel" "$store" "$nonce" "$ci")"
        assert_eq "decide $kernel store-writable=$store nonce=$nonce ci=$ci" \
          "$expected" "${verdict%%:*}"
      done
    done
  done
done

# Runs `mutants_canary_facts` with every marker cleared, then the assignments
# given, and prints its nonce and CI facts.
facts_with() {
  env -u GITHUB_ACTIONS -u CI -u RUNNER_ENVIRONMENT -u BORZOI_MUTANTS_CI_JOB \
    -u BORZOI_MUTANTS_CANARY "$@" bash -c 'source "$1"; mutants_canary_facts' \
    facts "$here/canary.sh" | cut -d' ' -f3,4
}

assert_eq "no marker: neither seen" "no no" "$(facts_with)"

# CI's mutation job is all four variables; each alone short of them is not.
ci_vars=(GITHUB_ACTIONS=true CI=true RUNNER_ENVIRONMENT=github-hosted BORZOI_MUTANTS_CI_JOB=true)
assert_eq "CI's mutation job is seen" "no yes" "$(facts_with "${ci_vars[@]}")"
for i in "${!ci_vars[@]}"; do
  rest=("${ci_vars[@]:0:i}" "${ci_vars[@]:i+1}")
  assert_eq "CI without ${ci_vars[$i]%%=*} is not seen" "no no" "$(facts_with "${rest[@]}")"
done
assert_eq "a self-hosted runner is not CI's mutation job" "no no" \
  "$(facts_with GITHUB_ACTIONS=true CI=true RUNNER_ENVIRONMENT=self-hosted BORZOI_MUTANTS_CI_JOB=true)"

# A nonce in the environment is the canary only when the file holds it. The
# file, where it exists (inside the container), holds 32 random hex digits.
assert_eq "an env nonce the file does not hold is not seen" "no no" \
  "$(facts_with BORZOI_MUTANTS_CANARY=not-the-canary)"

# End to end: a `cargo` shim on PATH records any invocation, and a command the
# runner would start records that too. Neither may run.
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/bin"
cat >"$tmp/bin/cargo" <<EOF
#!/usr/bin/env bash
echo cargo >>"$tmp/ran"
EOF
cp "$tmp/bin/cargo" "$tmp/bin/cargo-mutants"
chmod +x "$tmp/bin/cargo" "$tmp/bin/cargo-mutants"
cat >"$tmp/victim" <<EOF
#!/usr/bin/env bash
echo victim >>"$tmp/ran"
EOF
chmod +x "$tmp/victim"

sandboxless() {
  env -u GITHUB_ACTIONS -u CI -u RUNNER_ENVIRONMENT -u BORZOI_MUTANTS_CI_JOB \
    -u BORZOI_MUTANTS_CANARY -u BORZOI_MUTANTS_DEV_ENV \
    PATH="$tmp/bin:$PATH" "$@"
}

sandboxless bash "$here/canary-runner.sh" "$tmp/victim" 2>"$tmp/runner.err"
assert_eq "canary-runner refuses outside the sandbox" "$BORZOI_MUTANTS_REFUSED" "$?"
assert_eq "canary-runner names the refusal" yes \
  "$(grep -q 'canary-runner: refuse' "$tmp/runner.err" && echo yes || echo no)"

sandboxless bash "$here/inner.sh" nuget-regular-file "$tmp/out" 2>"$tmp/inner.err"
assert_eq "inner.sh refuses outside the sandbox" "$BORZOI_MUTANTS_REFUSED" "$?"
assert_eq "inner.sh names the refusal" yes \
  "$(grep -q 'inner.sh: refuse' "$tmp/inner.err" && echo yes || echo no)"
assert_eq "inner.sh wrote no output" no "$([[ -e "$tmp/out" ]] && echo yes || echo no)"
mkdir -p "$tmp/runner/mutants/nuget-regular-file"
touch "$tmp/runner/mutants/nuget-regular-file/earlier-run"
sandboxless RUNNER_TEMP="$tmp/runner" bash "$repo/tools/ci/mutants.sh" nuget-regular-file \
  2>"$tmp/ci.err"
assert_eq "tools/ci/mutants.sh refuses outside CI's mutation job" "$BORZOI_MUTANTS_REFUSED" "$?"
assert_eq "tools/ci/mutants.sh keeps an earlier run's output when it refuses" yes \
  "$([[ -e "$tmp/runner/mutants/nuget-regular-file/earlier-run" ]] && echo yes || echo no)"
assert_eq "nothing ran" "" "$(cat "$tmp/ran" 2>/dev/null)"

# Cargo's own wrapper and runner selection, under the arguments
# `.cargo/mutants.toml` hands cargo-mutants, with a competing runner for the
# host's triple in the environment (as CI's `CARGO_TARGET_<TRIPLE>_RUNNER` is).
# The canary must refuse as the rustc wrapper, before anything is compiled;
# and, with the wrapper overridden by the one variable that outranks it, as the
# runner, before the test binary starts.
config_args=()
while IFS= read -r arg; do
  config_args+=("$arg")
done < <(sed -n 's/^  "--config", "\(.*\)",$/\1/p' "$repo/.cargo/mutants.toml")
assert_eq "mutants.toml installs the canary as wrapper and runner" yes \
  "$(printf '%s\n' "${config_args[@]}" | grep -q '^build.rustc-workspace-wrapper' &&
    printf '%s\n' "${config_args[@]}" | grep -q 'runner = ' && echo yes || echo no)"
host="$(rustc -vV | sed -n 's/^host: //p')"
host_var="CARGO_TARGET_$(printf '%s' "$host" | tr 'a-z-' 'A-Z_')_RUNNER"
mkdir -p "$tmp/probe/src" "$tmp/probe/tools/mutants"
cp "$here/canary.sh" "$here/canary-runner.sh" "$tmp/probe/tools/mutants/"
cat >"$tmp/probe/Cargo.toml" <<'EOF'
[package]
name = "canary-probe"
version = "0.0.0"
edition = "2021"

[workspace]
EOF
cat >"$tmp/probe/src/lib.rs" <<EOF
#[test]
fn started() {
    std::fs::write("$tmp/probe-started", "").unwrap();
}
EOF
cat >"$tmp/competitor" <<EOF
#!/usr/bin/env bash
echo competitor >>"$tmp/probe-runner"
exec "\$@"
EOF
chmod +x "$tmp/competitor"
cargo_args=()
for arg in "${config_args[@]}"; do
  cargo_args+=(--config "$arg")
done
probe() { # name extra-env...
  local name="$1"
  shift
  rm -rf "$tmp/probe/target" "$tmp/probe-runner" "$tmp/probe-started"
  (
    cd "$tmp/probe" &&
      env -u GITHUB_ACTIONS -u CI -u RUNNER_ENVIRONMENT -u BORZOI_MUTANTS_CI_JOB \
        -u BORZOI_MUTANTS_CANARY -u CARGO_TARGET_DIR -u RUSTC_WORKSPACE_WRAPPER \
        "$host_var=$tmp/competitor" "$@" \
        cargo test --quiet --offline "${cargo_args[@]}" --tests >"$tmp/probe.out" 2>&1
  )
  local status=$?
  assert_eq "$name: the canary refuses" yes \
    "$(grep -q 'canary-runner: refuse' "$tmp/probe.out" && echo yes || echo no)"
  assert_eq "$name: cargo test fails" yes "$([[ $status -ne 0 ]] && echo yes || echo no)"
  assert_eq "$name: the competing runner never ran" no \
    "$([[ -e "$tmp/probe-runner" ]] && echo yes || echo no)"
  assert_eq "$name: the probe's test never started" no \
    "$([[ -e "$tmp/probe-started" ]] && echo yes || echo no)"
}
probe "as the rustc wrapper"
assert_eq "as the rustc wrapper: nothing was compiled" no \
  "$(ls "$tmp"/probe/target/debug/deps/canary_probe-* >/dev/null 2>&1 && echo yes || echo no)"
cat >"$tmp/passthrough" <<'EOF'
#!/usr/bin/env bash
exec "$@"
EOF
chmod +x "$tmp/passthrough"
probe "as the runner" RUSTC_WORKSPACE_WRAPPER="$tmp/passthrough"

if [[ $fails -ne 0 ]]; then
  echo "$fails failure(s)"
  exit 1
fi
echo "all passed"
