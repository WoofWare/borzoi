#!/usr/bin/env bash
#
# The workspace's rustc wrapper and every test binary's runner in a mutation
# run (`.cargo/mutants.toml`): cargo runs `canary-runner.sh rustc ARGS...` and
# `canary-runner.sh BINARY ARGS...`. It runs the command only where `canary.sh`
# allows, and otherwise exits `$BORZOI_MUTANTS_REFUSED` without starting it, so
# a bare `cargo mutants` on a developer's machine compiles no mutant, fails its
# unmutated baseline and runs none.
set -euo pipefail

# shellcheck source=tools/mutants/canary.sh
source "$(dirname "${BASH_SOURCE[0]}")/canary.sh"
mutants_canary_check canary-runner
exec "$@"
