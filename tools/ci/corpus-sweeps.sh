#!/usr/bin/env bash
# The ignored sweeps each crate's CI job gates on: the corpus differentials,
# the fresh-seed soaks and the other `#[ignore]`d tests that `cargo test` skips.
# This file is the one list of them. CI runs each as
# `corpus-sweeps.sh STEP...` from the job of its crate (so under that crate's
# change filter), and `corpus-sweeps.test.sh` fails if `ci.yml` runs an ignored
# test any other way, or runs a step twice, from another crate's job, or not
# at all.
#
#   corpus-sweeps.sh                every step, in order
#   corpus-sweeps.sh CRATE...       every step of those crates' jobs
#                                   (cst, msbuild, nuget, sema, lsp)
#   corpus-sweeps.sh STEP...        just those steps
#   corpus-sweeps.sh --list [CRATE] the steps as `CRATE STEP`, one per line
#
# Asked for more than one step, the script keeps going after a failure and
# names the failed steps at the end, so one run reports (or, under
# BORZOI_UPDATE_MANIFESTS=1, regenerates) every manifest the steps check.
#
# The whole-project gate is not here: `project-corpus-gate.sh` runs it, as it
# needs the project corpus materialised first.
#
# Run it outside `nix develop`: each step enters the devshell itself.
set -euo pipefail
unset CDPATH

repo="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo"

# `CRATE STEP`, in CI's order within each job. The steps that never ask FCS
# are CPU in our own crate, so most run under the `gate` profile (debug
# assertions kept, optimised); those that drive FCS stay on the dev binary,
# as the oracle is most of their time. The times are a local run's, roughly.
steps=(
  "cst parser-corpus"                # ~30 s
  "cst parser-corpus-diff"           # ~5.5 min
  "cst feature-gates"                # ~2 min
  "cst version-dependence"           # ~3 min
  "cst print-roundtrip"              # ~30 s
  "cst recovery"                     # ~3 min
  "cst decl-sequence-streams"        # ~3 min
  "cst flat-tree"                    # ~2.5 min
  "cst facade-properties"            # ~4 min
  "cst panic-fresh-seed"             # ~10 s
  "cst layout-perturbation"          # ~1.5 min
  "cst utf16-width"                  # ~10 s
  "msbuild msbuild-corpus"           # ~40 s
  "msbuild sdk-chain-attribution"    # ~1 s
  "msbuild rejection-soak"           # ~1.5 min
  "nuget nuget-soak"                 # ~15 s
  "nuget resolver-soak"              # ~50 s
  "sema resolve-corpus"              # ~20 s
  "sema attr-resolution"             # ~25 s
  "sema silent-region"               # ~1.5 min
  "sema auto-open-member"            # ~10 min
  "sema infer-corpus-diff"           # ~30 s
  "sema infer-corpus-dump"           # ~40 s
  "sema infer-incremental"           # ~40 s
  "sema infer-extension-damage"      # ~4 min
  "lsp lsp-parser-corpus"            # ~50 s
  "lsp xml-doc-shipped"              # ~10 s
  "lsp xml-doc-source"               # ~20 s
  "lsp inheritdoc"                   # ~4 min
)

crates=(cst msbuild nuget sema lsp)

package_of() { # crate
  case "$1" in
    lsp) echo borzoi ;;
    *) echo "borzoi-$1" ;;
  esac
}

crate_of() { # step
  local e
  for e in "${steps[@]}"; do [[ "${e#* }" == "$1" ]] && { echo "${e%% *}"; return; }; done
}

# The package is the step's crate's, never the step's own choice: a step that
# named another crate's package would match no test there and pass empty.
pkg=
ignored() { # cargo-test arguments before `--`, without `-p`
  nix develop --command cargo test -p "$pkg" "$@" -- --ignored --nocapture
}
ignored_filters() { # test filters, which then follow `--`
  nix develop --command cargo test -p "$pkg" --test all -- --ignored --nocapture "$@"
}

# Each step is a single command, so its status is the step's.
run_step() { # name
  pkg="$(package_of "$(crate_of "$1")")"
  case "$1" in
    parser-corpus) ignored --profile gate --test all parser_corpus:: ;;
    parser-corpus-diff) ignored --test all parser_corpus_diff:: ;;
    feature-gates) ignored --test all parser_diff_feature_gates:: ;;
    version-dependence) ignored --profile gate --test all version_dependence_census:: ;;
    print-roundtrip) ignored --test all print_roundtrip::corpus:: ;;
    recovery) ignored --profile gate --test all recovery_sweep:: ;;
    decl-sequence-streams)
      ignored --test all \
        parser_diff_decl_sequence_grid::every_declaration_pair_streams
      ;;
    flat-tree) ignored --profile gate --test all flat_tree_reference::corpus ;;
    facade-properties) ignored --profile gate --test all facade_properties::corpus ;;
    panic-fresh-seed) ignored --profile gate --test all parser_panic_sweep::fresh_seed ;;
    layout-perturbation) ignored --profile gate --test all layout_perturbation_sweep:: ;;
    utf16-width) ignored --profile gate --test all utf16_width_invariance::corpus ;;
    msbuild-corpus) ignored --test fsproj_msbuild_corpus_diff ;;
    sdk-chain-attribution) ignored --test sdk_chain_decline_attribution ;;
    rejection-soak) ignored --test rejection_generative_diff ;;
    nuget-soak) ignored --test all soak:: ;;
    resolver-soak) ignored --test all resolver_diff::randomised_soundness_soak ;;
    resolve-corpus) ignored --test all resolve_corpus_diff:: ;;
    attr-resolution) ignored --test all attr_resolution_sweep:: ;;
    silent-region) ignored --test all silent_region_sweep:: ;;
    auto-open-member) ignored --test all auto_open_member_sweep:: ;;
    infer-corpus-diff) ignored --test all infer_corpus_diff:: ;;
    infer-corpus-dump) ignored --test all infer_corpus_dump:: ;;
    infer-incremental)
      ignored --test all \
        infer_incremental_diff::incremental_equals_batch_over_a_corpus_sample
      ;;
    infer-extension-damage) ignored --test all infer_extension_damage_sweep::full_sweep ;;
    lsp-parser-corpus) ignored --test all parser_corpus_sweep:: ;;
    xml-doc-shipped) ignored --test all xml_doc_shipped_sweep:: ;;
    xml-doc-source) ignored --test all xml_doc_source_diff::corpus:: ;;
    inheritdoc)
      # The generated-program module's `deep_*` twins, in the module and its
      # families, are its only ignored tests, so its filter names the module.
      ignored_filters \
        xml_doc_inheritdoc_sweep:: xml_doc_inheritdoc_cref_diff::deep_ \
        xml_doc_inheritdoc_generated_diff:: xml_doc_inheritdoc_metadata_diff::deep_ \
        xml_doc_type_id_diff::deep_
      ;;
    *)
      echo "corpus-sweeps.sh: no step named '$1' in run_step" >&2
      return 2
      ;;
  esac
}

is_crate() { local c; for c in "${crates[@]}"; do [[ "$c" == "$1" ]] && return 0; done; return 1; }
is_step() { local e; for e in "${steps[@]}"; do [[ "${e#* }" == "$1" ]] && return 0; done; return 1; }

list() { # [crate]
  local entry
  for entry in "${steps[@]}"; do
    if [[ $# -eq 0 || "${entry%% *}" == "$1" ]]; then
      printf '%s\n' "$entry"
    fi
  done
}

if [[ "${1:-}" == --list ]]; then
  if [[ $# -gt 2 ]] || { [[ $# -eq 2 ]] && ! is_crate "$2"; }; then
    echo "usage: corpus-sweeps.sh --list [$(IFS='|'; echo "${crates[*]}")]" >&2
    exit 2
  fi
  list "${@:2}"
  exit 0
fi

# Every argument is checked before any step runs, so a typo costs nothing.
selected=()
if [[ $# -eq 0 ]]; then
  for entry in "${steps[@]}"; do selected+=("${entry#* }"); done
else
  for arg in "$@"; do
    if is_crate "$arg"; then
      while IFS= read -r entry; do selected+=("${entry#* }"); done < <(list "$arg")
    elif is_step "$arg"; then
      selected+=("$arg")
    else
      echo "corpus-sweeps.sh: unknown step '$arg' (see --list)" >&2
      exit 2
    fi
  done
fi

if [[ ${#selected[@]} -eq 1 ]]; then
  run_step "${selected[0]}"
  exit
fi

failed=()
for step in "${selected[@]}"; do
  echo "=== corpus-sweeps: $step ==="
  run_step "$step" || failed+=("$step")
done
if [[ ${#failed[@]} -gt 0 ]]; then
  echo "corpus-sweeps: failed steps: ${failed[*]}" >&2
  exit 1
fi
