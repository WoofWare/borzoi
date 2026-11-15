#!/bin/zsh
# Runs on the factotum box: remote_gates.sh <dir> <steps...>; writes <dir>.gates/summary.txt
dir=$1; shift
export PATH=/nix/var/nix/profiles/default/bin:$PATH
out=~/$dir.gates
mkdir -p $out
cd ~/$dir
run() {
  local name=$1; shift
  "$@" > $out/$name.log 2>&1
  echo "$name exit=$?" >> $out/summary.txt
}
for step in "$@"; do
  case $step in
    fmt) run fmt nix develop -c cargo fmt --all -- --check ;;
    clippy) run clippy nix develop -c cargo clippy --workspace --all-targets --all-features -- -D warnings ;;
    msbuild) run msbuild nix develop -c cargo test -p borzoi-msbuild ;;
    workspace) run workspace nix develop -c cargo test ;;
    doc) run doc nix develop -c env RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features --document-private-items ;;
    corpus) run corpus nix develop -c cargo test -p borzoi-msbuild --test fsproj_msbuild_corpus_diff -- --ignored ;;
    attribution) run attribution nix develop -c cargo test -p borzoi-msbuild --test sdk_chain_decline_attribution -- --ignored ;;
    projects) run projects bash tools/ci/project-corpus-gate.sh ;;
  esac
done
echo "all done" >> $out/summary.txt
