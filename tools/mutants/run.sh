#!/usr/bin/env bash
#
# Runs one mutation set (`tools/mutants/sets.tsv`) on this Mac inside a Linux
# VM under Apple's `container`, then checks the set's exact manifest
# (`tools/mutants/manifests/<set>.txt`) against the run:
#
#   tools/mutants/run.sh SET
#   BORZOI_UPDATE_MANIFESTS=1 tools/mutants/run.sh SET   # regenerate instead
#
# Run it outside `nix develop`; it enters the devshell for the manifest step.
#
# What it measures: the commit at HEAD, exported with `git archive`. It
# refuses a tree with uncommitted changes to tracked files, and writes the
# manifest only if the checkout is still that commit, clean, when the run ends.
#
# The sandbox, in containers on one image (nixos/nix, pinned by digest):
#
#   provision  networked, with the Linux Nix store volume (`borzoi-mutants-nix`,
#              seeded once from the image's /nix) writable. It realises the
#              flake's devshell for the exported tree and writes the shell's
#              environment (`nix print-dev-env`) to the run's directory. This is
#              the only step that touches the network or writes the store.
#   run        `--network none`; the store volume mounted read-only (no daemon,
#              no socket: the host's store is Darwin's and is never mounted);
#              the exported tree and the devshell's environment read-only; a
#              fresh scratch volume of bounded size at /work for HOME, TMPDIR,
#              every build and cargo-mutants' output; an unprivileged user
#              (uid 1000), so file permissions bind the tests as they do on a
#              developer's machine and in CI; and the canary (`canary.sh`) at
#              /run/borzoi-mutants, read-only. It can write no host path.
#              Memory and CPUs are capped by the VM's size.
#   export     no network, no mutant: copies the run's three artifacts out of
#              the scratch volume to the host, each only if it is a regular
#              file under the size `mutants-manifest` accepts.
#
# One deadline bounds every container of a run, provisioning included; at it
# the running container is killed. The run container also enforces what was
# left of it when it started, inside the guest, so it ends on time even if
# this script is killed and cannot stop it. Only the export, which copies three files
# and runs no mutant, has five minutes of its own past it, so a run that timed
# out still leaves its artifacts. One run at a time: the store volume is an
# ext4 image, which two VMs must not mount while either writes it, so a run
# holds a lock in the same namespace as the volume, the `container` volume
# `borzoi-mutants-nix-lock`, and takes it only while no container of an
# earlier run (`borzoi-mutants-*`) remains to mount the store. It releases the
# lock only once its own containers are gone.
#
# A run that fails keeps its scratch volume, cargo-mutants' logs included, and
# says how to read and then delete it.
#
# Environment:
#   BORZOI_MUTANTS_MEMORY   the VM's memory (default 24G)
#   BORZOI_MUTANTS_CPUS     its CPUs (default 8)
#   BORZOI_MUTANTS_JOBS     cargo-mutants' --jobs (default 3)
#   BORZOI_MUTANTS_TIMEOUT  the run's wall-clock bound, in seconds or with an
#                           s, m, h or d suffix (default 12h)
#   BORZOI_MUTANTS_HOME     where runs keep their directories (default
#                           ~/.cache/borzoi/mutants)
#
# Exit status: `inner.sh`'s (94 red baseline, 95 no mutant, 97 refused), 124
# when the run timed out, 1 when the manifest moved, 0 when it did not.
#
# To reclaim the Linux store: `container volume delete borzoi-mutants-nix`.
set -euo pipefail
unset CDPATH
# Git's repository-local variables (GIT_DIR, GIT_INDEX_FILE, …), inherited from
# a hook or a caller, would point every `git -C "$repo"` below at another
# repository.
# shellcheck disable=SC2046
unset $(git rev-parse --local-env-vars)

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/../.." && pwd)"

IMAGE=docker.io/nixos/nix@sha256:f159a58f390677f41e8e900a74b6e2f9c7f27b364122ae6acf7a652ce6c551c0
NIX_VOLUME=borzoi-mutants-nix
LOCK_VOLUME=borzoi-mutants-nix-lock
# Inside the image, before and after the store volume replaces its /nix: the
# volume is seeded from the image's own /nix, so these paths are the same.
BASH_IN_IMAGE=/nix/var/nix/profiles/default/bin/bash
# The largest artifact the export copies, as `mutants-manifest`'s
# `ARTIFACT_LIMIT`.
ARTIFACT_LIMIT=$((64 << 20))

if [[ $# -ne 1 ]]; then
  echo "usage: run.sh SET" >&2
  exit 2
fi
set_name="$1"

# shellcheck source=tools/mutants/sets.sh
source "$here/sets.sh"
mutants_set_load "$repo/tools/mutants/sets.tsv" "$set_name" || exit 2

command -v container >/dev/null || {
  echo "run.sh: Apple's \`container\` is not on PATH" >&2
  exit 1
}

if [[ -n "$(git -C "$repo" status --porcelain --untracked-files=no)" ]]; then
  echo "run.sh: the tree has uncommitted changes to tracked files; commit them first," >&2
  echo "        so the manifest names the source it graded" >&2
  exit 1
fi
commit="$(git -C "$repo" rev-parse HEAD)"

# The deadline, as an epoch second.
budget="${BORZOI_MUTANTS_TIMEOUT:-12h}"
if ! [[ "$budget" =~ ^([0-9]+)([smhd]?)$ ]]; then
  echo "run.sh: BORZOI_MUTANTS_TIMEOUT=$budget is not a duration" >&2
  exit 2
fi
case "${BASH_REMATCH[2]}" in
  m) unit=60 ;;
  h) unit=3600 ;;
  d) unit=86400 ;;
  *) unit=1 ;;
esac
deadline=$(($(date +%s) + 10#${BASH_REMATCH[1]} * unit))

runs="${BORZOI_MUTANTS_HOME:-$HOME/.cache/borzoi/mutants}"
mkdir -p "$runs"
# Absolute: the manifest step runs from the repository root.
runs="$(cd "$runs" && pwd)"

# The containers, of any run, that may mount the store volume. Fails, rather
# than answering none, when `container` cannot list them.
leftover_containers() {
  local all
  all="$(container list --all --quiet)" || return 1
  grep '^borzoi-mutants-' <<<"$all" || true
}
recovery_hint() {
  echo "        Once \`container list --all\` shows no borzoi-mutants-* container (stop and" >&2
  echo "        delete any a killed run left), \`container volume delete $LOCK_VOLUME\`." >&2
}
if ! create_error="$(container volume create -s 1M --label "pid=$$" "$LOCK_VOLUME" 2>&1)"; then
  # The holder's pid is the lock's label. While that process lives, the lock
  # is held, whether or not a container is running at this moment: a run holds
  # it between its containers too.
  if ! lock_info="$(container volume inspect "$LOCK_VOLUME" 2>&1)"; then
    # No lock to inspect: the creation failed for another reason, such as the
    # container service being down.
    echo "run.sh: cannot take the lock volume $LOCK_VOLUME:" >&2
    printf '        %s\n' "$create_error" "$lock_info" >&2
    exit 1
  fi
  holder="$(sed -n 's/.*"pid" : "\([0-9][0-9]*\)".*/\1/p' <<<"$lock_info")"
  if [[ -z "$holder" ]]; then
    echo "run.sh: the lock volume $LOCK_VOLUME is held, but its owner is unreadable;" >&2
    echo "        delete it only once no run.sh is running." >&2
  elif kill -0 "$holder" 2>/dev/null; then
    echo "run.sh: a mutation run (pid $holder) holds the lock volume $LOCK_VOLUME;" >&2
    echo "        wait for it to finish." >&2
  else
    echo "run.sh: the lock volume $LOCK_VOLUME belongs to pid $holder, which has exited." >&2
    recovery_hint
  fi
  exit 1
fi
if ! leftovers="$(leftover_containers)"; then
  container volume delete "$LOCK_VOLUME" >/dev/null 2>&1 || true
  echo "run.sh: cannot list containers, so cannot tell whether one mounts the store" >&2
  exit 1
fi
if [[ -n "$leftovers" ]]; then
  container volume delete "$LOCK_VOLUME" >/dev/null 2>&1 || true
  echo "run.sh: containers of an earlier run remain and may mount the store:" >&2
  printf '        %s\n' $leftovers >&2
  echo "        Stop and delete them, then retry." >&2
  exit 1
fi
container_name=""
work_volume=""
keep_work=no
cleanup() {
  local remaining
  if [[ -n "$container_name" ]]; then
    for c in "$container_name"-seed "$container_name"-provision "$container_name"-prepare \
      "$container_name" "$container_name"-export; do
      container kill "$c" >/dev/null 2>&1 || true
      container delete "$c" >/dev/null 2>&1 || true
    done
  fi
  if [[ -n "$work_volume" && $keep_work == no ]]; then
    container volume delete "$work_volume" >/dev/null 2>&1 || true
  fi
  if ! remaining="$(leftover_containers)"; then
    echo "run.sh: cannot list containers, so the store lock stays." >&2
    recovery_hint
    return
  fi
  if [[ -n "$remaining" ]]; then
    echo "run.sh: could not remove every container of this run, so the store lock stays:" >&2
    printf '        %s\n' $remaining >&2
    recovery_hint
    return
  fi
  # What the containers read is no longer needed once they are gone; the
  # run's artifacts in `out` are, to check it again.
  if [[ -n "${run_dir:-}" ]]; then
    rm -rf "$run_dir/src" "$run_dir/env" "$run_dir/canary"
  fi
  container volume delete "$LOCK_VOLUME" >/dev/null 2>&1 || true
}
trap cleanup EXIT

# Each run's ID is fresh, so its directory, containers and volume are its own:
# `mkdir` claims the directory, and a name already taken is drawn again.
# Container and volume IDs take lowercase letters, digits and `-` only.
while :; do
  run_id="${commit:0:12}-$(od -An -N6 -tx1 /dev/urandom | tr -d ' \n')"
  run_dir="$runs/$run_id-$set_name"
  if mkdir "$run_dir"; then
    break
  elif [[ ! -e "$run_dir" ]]; then
    echo "run.sh: cannot create $run_dir" >&2
    exit 1
  fi
done
mkdir -p "$run_dir/src" "$run_dir/canary" "$run_dir/env" "$run_dir/out"
git -C "$repo" archive --format=tar "$commit" | tar -xf - -C "$run_dir/src"

nonce="$(od -An -N16 -tx1 /dev/urandom | tr -d ' \n')"
printf '%s' "$nonce" >"$run_dir/canary/canary"

work_volume="borzoi-mutants-work-$run_id"
container_name="borzoi-mutants-$run_id"

# bounded COMMAND...: runs COMMAND under what is left of the deadline, and
# returns 124 without running it once none is left.
bounded() {
  local left=$((deadline - $(date +%s)))
  if [[ $left -le 0 ]]; then
    echo "run.sh: the run's deadline ($budget) passed" >&2
    return 124
  fi
  timeout --kill-after=60 "$left" "$@"
}

if ! container volume inspect "$NIX_VOLUME" >/dev/null 2>&1; then
  container volume create -s 300G "$NIX_VOLUME" >/dev/null
fi
echo "run.sh: provisioning the devshell for $commit"
bounded container run --rm --name "$container_name-seed" \
  --memory 8G --cpus 4 \
  --mount "type=volume,source=$NIX_VOLUME,target=/nix-volume" \
  "$IMAGE" "$BASH_IN_IMAGE" -c '
    set -eu
    # The marker is written only once the copy is whole, so a copy cut short
    # is redone rather than taken for a store.
    if [ ! -e /nix-volume/.borzoi-mutants-seeded ]; then
      find /nix-volume -mindepth 1 -maxdepth 1 ! -name lost+found -exec rm -rf {} +
      cp -a /nix/. /nix-volume/
      touch /nix-volume/.borzoi-mutants-seeded
    fi'
bounded container run --rm --name "$container_name-provision" \
  --memory 8G --cpus 4 \
  --mount "type=volume,source=$NIX_VOLUME,target=/nix" \
  --mount "type=bind,source=$run_dir/src,target=/src,readonly" \
  --mount "type=bind,source=$run_dir/env,target=/env" \
  "$IMAGE" "$BASH_IN_IMAGE" -c '
    set -eu
    nix --extra-experimental-features "nix-command flakes" print-dev-env \
      --profile /nix/var/nix/profiles/borzoi-mutants "path:/src" >/env/dev-env.sh.tmp
    mv /env/dev-env.sh.tmp /env/dev-env.sh'

# The run container's user (uid 1000) is not this Mac's, so what it reads must
# be readable whatever the caller's umask made of it.
chmod -R a+rX "$run_dir/src" "$run_dir/canary" "$run_dir/env"

container volume create -s 64G "$work_volume" >/dev/null
bounded container run --rm --name "$container_name-prepare" \
  --network none \
  --mount "type=volume,source=$work_volume,target=/work" \
  "$IMAGE" "$BASH_IN_IMAGE" -c '
    set -eu
    mkdir -p /work/home /work/tmp
    chown -R 1000:1000 /work'
echo "run.sh: running set $set_name in $run_dir"
status=0
guest_left=$((deadline - $(date +%s)))
bounded container run --rm --name "$container_name" \
  --network none \
  --uid 1000 --gid 1000 \
  --memory "${BORZOI_MUTANTS_MEMORY:-24G}" --cpus "${BORZOI_MUTANTS_CPUS:-8}" \
  --mount "type=volume,source=$NIX_VOLUME,target=/nix,readonly" \
  --mount "type=bind,source=$run_dir/src,target=/src,readonly" \
  --mount "type=bind,source=$run_dir/env,target=/env,readonly" \
  --mount "type=bind,source=$run_dir/canary,target=/run/borzoi-mutants,readonly" \
  --mount "type=volume,source=$work_volume,target=/work" \
  --env "BORZOI_MUTANTS_CANARY=$nonce" \
  --env "BORZOI_MUTANTS_DEV_ENV=/env/dev-env.sh" \
  --env "BORZOI_MUTANTS_COMMIT=$commit" \
  --env "BORZOI_MUTANTS_JOBS=${BORZOI_MUTANTS_JOBS:-3}" \
  --env HOME=/work/home \
  --env TMPDIR=/work/tmp \
  --workdir /src \
  "$IMAGE" "$BASH_IN_IMAGE" -c '
    exec timeout --kill-after=30 "$1" bash /src/tools/mutants/inner.sh "$0" /work/out/run' \
  "$set_name" "$guest_left" || status=$?

# keep_scratch: keeps the scratch volume past cleanup and says how to read it.
keep_scratch() {
  keep_work=yes
  echo "run.sh: kept the run's scratch volume, with cargo-mutants' logs, for inspection:" >&2
  echo "        container run --rm -it --mount type=volume,source=$work_volume,target=/work,readonly \\" >&2
  echo "          $IMAGE $BASH_IN_IMAGE   # logs under /work/out/run/mutants.out/log" >&2
  echo "        then: container volume delete $work_volume" >&2
}
if [[ $status -ne 0 ]]; then
  keep_scratch
fi

# The run's VM must be gone before another mounts its volume: a timeout signals
# the `container` CLI, which can die before the guest does. Unless that is
# confirmed, the volume is kept and nothing is exported.
container kill "$container_name" >/dev/null 2>&1 || true
container delete "$container_name" >/dev/null 2>&1 || true
exported=no
if all="$(container list --all --quiet)" && ! grep -qxF -- "$container_name" <<<"$all"; then
  exported=yes
else
  echo "run.sh: cannot confirm the run's container $container_name is gone, so its" >&2
  echo "        volume is not exported" >&2
  if [[ $status -eq 0 ]]; then
    status=1
  fi
  keep_scratch
fi

# The run's artifacts, out of the scratch volume, whatever its status: a red
# baseline's `outcomes.json` says why.
[[ $exported == yes ]] && timeout --kill-after=60 300 container run --rm --name "$container_name-export" \
  --network none \
  --mount "type=volume,source=$work_volume,target=/work,readonly" \
  --mount "type=bind,source=$run_dir/out,target=/out" \
  "$IMAGE" "$BASH_IN_IMAGE" -c '
    set -u
    limit="$0"
    mkdir -p /out/run/mutants.out
    for rel in run-info.tsv listed.txt mutants.out/outcomes.json; do
      src="/work/out/run/$rel"
      # The run wrote this tree: a link anywhere in the path could lead out
      # of the volume, to the host directory mounted beside it.
      if [ -f "$src" ] && [ "$(readlink -f "$src")" = "$src" ] &&
        [ "$(stat -c %s "$src")" -le "$limit" ]; then
        cp "$src" "/out/run/$rel"
      else
        echo "run.sh: $rel is missing, not a regular file, or over $limit bytes" >&2
      fi
    done' \
  "$ARTIFACT_LIMIT" || true

if [[ $status -ne 0 ]]; then
  echo "run.sh: the run exited $status; its artifacts are in $run_dir/out" >&2
  exit "$status"
fi

# The manifest step reads the set and writes its manifest in the live checkout,
# so it must still be the tree the run graded.
cd "$repo"
if [[ "$(git rev-parse HEAD)" != "$commit" ||
  -n "$(git status --porcelain --untracked-files=no)" ]]; then
  echo "run.sh: the checkout has moved off $commit since the run began, so its" >&2
  echo "        manifest is left alone. The run's artifacts are in $run_dir/out;" >&2
  echo "        check them from a clean checkout of $commit with" >&2
  echo "        nix develop -c cargo run -p borzoi-oracle-harness --bin mutants-manifest -- $set_name $run_dir/out \$PWD" >&2
  keep_scratch
  exit 1
fi
status=0
nix develop -c cargo run --quiet -p borzoi-oracle-harness --bin mutants-manifest -- \
  "$set_name" "$run_dir/out" "$repo" || status=$?
if [[ $status -ne 0 ]]; then
  keep_scratch
fi
exit "$status"
