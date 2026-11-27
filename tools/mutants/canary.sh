# shellcheck shell=bash
#
# The mutation-testing sandbox canary. Sourced by `canary-runner.sh` (the
# cargo `target.runner` every test binary runs through under cargo-mutants;
# see `.cargo/mutants.toml`) and by `inner.sh` before it starts a run.
#
# A mutated program can do damage by accident: a mutated path computation can
# delete or rewrite whatever the test process can reach. So mutated tests run
# only where that damage is contained, and this file decides whether the
# current process is such a place. It allows a run only when all three hold:
#
#   - the kernel is Linux;
#   - `/nix/store` is not writable by this process;
#   - the process is in a sandbox the repo's launchers made: either
#       - `tools/mutants/run.sh`'s container, which mounts a canary file at
#         `$BORZOI_MUTANTS_CANARY_PATH` holding a random nonce and passes the
#         same nonce as `BORZOI_MUTANTS_CANARY`; or
#       - CI's mutation job: a GitHub-hosted runner (`GITHUB_ACTIONS=true`,
#         `CI=true`, `RUNNER_ENVIRONMENT=github-hosted`), an ephemeral VM,
#         in the job whose environment sets `BORZOI_MUTANTS_CI_JOB=true`, which
#         no other job does (`tools/ci/mutants.sh`). A self-hosted runner, or
#         any other job, is refused.
#
# The canary prevents *accidental* runs, not malicious ones: anything that sets
# those four variables on a Linux host whose store it cannot write gets past
# it. Doctests are not covered either: rustdoc runs them without the
# cargo runner, so `inner.sh` passes `--tests`, which leaves them out of every
# mutation run.

# The path `run.sh` mounts the canary file at inside the container.
BORZOI_MUTANTS_CANARY_PATH=/run/borzoi-mutants/canary

# The exit status a refusal ends with, distinct from a test failure (101) and
# from cargo-mutants' own statuses (0–4, 70).
BORZOI_MUTANTS_REFUSED=97

# mutants_canary_decide KERNEL STORE_WRITABLE NONCE_MATCHES CI
#
# The rule itself, over facts `mutants_canary_facts` gathers: KERNEL is
# `uname -s`, and the other three are `yes` or `no`. Prints `allow` or
# `refuse: <reason>`. Pure, so `canary.test.sh` can hold it to its table.
mutants_canary_decide() {
  local kernel="$1" store_writable="$2" nonce_matches="$3" ci="$4"
  if [[ "$kernel" != Linux ]]; then
    printf 'refuse: kernel is %s, not Linux\n' "$kernel"
  elif [[ "$store_writable" != no ]]; then
    printf 'refuse: /nix/store is writable\n'
  elif [[ "$nonce_matches" != yes && "$ci" != yes ]]; then
    printf 'refuse: neither the container canary nor a CI runner is present\n'
  else
    printf 'allow\n'
  fi
}

# mutants_canary_facts
#
# Prints the four facts `mutants_canary_decide` takes, space-separated.
mutants_canary_facts() {
  local kernel store_writable=no nonce_matches=no ci=no
  kernel="$(uname -s)"
  # `test -w` is access(2), which answers EROFS for a read-only mount even to
  # root, and EACCES for a store owned by another user. A missing store is not
  # writable either.
  if [[ -w /nix/store ]]; then
    store_writable=yes
  fi
  if [[ -n "${BORZOI_MUTANTS_CANARY:-}" && -f "$BORZOI_MUTANTS_CANARY_PATH" ]] \
    && [[ "$(cat "$BORZOI_MUTANTS_CANARY_PATH")" == "$BORZOI_MUTANTS_CANARY" ]]; then
    nonce_matches=yes
  fi
  if [[ "${GITHUB_ACTIONS:-}" == true && "${CI:-}" == true \
    && "${RUNNER_ENVIRONMENT:-}" == github-hosted \
    && "${BORZOI_MUTANTS_CI_JOB:-}" == true ]]; then
    ci=yes
  fi
  printf '%s %s %s %s\n' "$kernel" "$store_writable" "$nonce_matches" "$ci"
}

# mutants_canary_check WHO
#
# Returns 0 when the run is allowed; otherwise prints why to stderr, naming
# WHO refused, and exits with `$BORZOI_MUTANTS_REFUSED`.
mutants_canary_check() {
  local who="$1" verdict
  # shellcheck disable=SC2046
  verdict="$(mutants_canary_decide $(mutants_canary_facts))"
  if [[ "$verdict" != allow ]]; then
    printf '%s: %s. Mutation tests run only inside tools/mutants/run.sh'"'"'s container or a CI runner.\n' \
      "$who" "$verdict" >&2
    exit "$BORZOI_MUTANTS_REFUSED"
  fi
}
