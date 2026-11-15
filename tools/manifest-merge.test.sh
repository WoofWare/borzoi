#!/usr/bin/env bash
#
# Tests for manifest-merge.sh: the ambient cargo builds the driver only when
# the devshell it came from vendored this worktree's `Cargo.lock`; any other
# shell enters this worktree's devshell through `nix develop`. Each case runs
# the real script in a scratch directory holding a `Cargo.lock`, with `cargo`
# and `nix` replaced by fakes that record how they were called. A last case,
# where `nix` is available, checks the real devshell's hash against the
# script's for this repository's lock.

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/.." && pwd)"
script="$here/manifest-merge.sh"
bash_bin="$(command -v bash)"
fails=0

assert_eq() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf 'ok   - %s\n' "$1"
  else
    printf 'FAIL - %s\n    expected: [%s]\n    actual:   [%s]\n' "$1" "$2" "$3"
    fails=$((fails + 1))
  fi
}

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

work="$tmp/work"
mkdir -p "$work"
printf '# a lock\n' >"$work/Cargo.lock"
lock_hash="$(cd "$work" && { sha256sum Cargo.lock 2>/dev/null || shasum -a 256 Cargo.lock; } | cut -d' ' -f1)"

# A PATH holding only what the script may call, the fakes among them.
fake_path() { # dir with-cargo
  local d="$1"
  mkdir -p "$d"
  for tool in sha256sum shasum cut; do
    if command -v "$tool" >/dev/null 2>&1; then
      ln -sf "$(command -v "$tool")" "$d/$tool"
    fi
  done
  printf '#!%s\necho "nix $*"\n' "$bash_bin" >"$d/nix"
  chmod +x "$d/nix"
  if [[ "$2" == yes ]]; then
    printf '#!%s\necho "cargo $*"\n' "$bash_bin" >"$d/cargo"
    chmod +x "$d/cargo"
  fi
}
fake_path "$tmp/with-cargo" yes
fake_path "$tmp/without-cargo" no

run() { # path hash-or-empty
  (
    cd "$work" || exit 1
    if [[ -n "$2" ]]; then
      PATH="$1" BORZOI_CARGO_LOCK_SHA256="$2" "$bash_bin" "$script" O A B P
    else
      env -u BORZOI_CARGO_LOCK_SHA256 PATH="$1" "$bash_bin" "$script" O A B P
    fi
  )
}

driver='run --quiet --release --locked -p borzoi-oracle-harness --bin manifest-merge -- O A B P'

assert_eq "a devshell that vendored this lock builds with its cargo" \
  "cargo $driver" "$(run "$tmp/with-cargo" "$lock_hash")"
assert_eq "a devshell that vendored another lock enters this one" \
  "nix develop --command cargo $driver" "$(run "$tmp/with-cargo" 0000)"
assert_eq "a cargo outside any devshell is not used" \
  "nix develop --command cargo $driver" "$(run "$tmp/with-cargo" "")"
assert_eq "no cargo at all enters the devshell" \
  "nix develop --command cargo $driver" "$(run "$tmp/without-cargo" "")"

# The devshell's hash is the one the script computes, for the real lock.
if command -v nix >/dev/null 2>&1; then
  devshell_hash="$(cd "$repo" && nix develop --command bash -c 'printf %s "$BORZOI_CARGO_LOCK_SHA256"' 2>/dev/null)"
  real_hash="$(cd "$repo" && { sha256sum Cargo.lock 2>/dev/null || shasum -a 256 Cargo.lock; } | cut -d' ' -f1)"
  assert_eq "the devshell records the hash of the lock it vendored" \
    "$real_hash" "$devshell_hash"
else
  printf 'skip - the devshell hash check needs nix\n'
fi

if ((fails > 0)); then
  printf '%d failed\n' "$fails"
  exit 1
fi
printf 'all passed\n'
