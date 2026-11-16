//! What a file's inference reads of the files before it
//! (`docs/resolve-what-a-request-reads-plan.md`, Stage 7a).
//!
//! A file's inference reads three facts of the whole prefix (the
//! constructor-like declarations of a name, the unions and records F# seals,
//! whether a type is declared at a path) and the rest per item. Of the
//! per-item reads, only an earlier value's type comes from inferring the
//! earlier file's bodies; the cases, records and types it reads are its
//! declarations. [`whole_prefix_facts_divergence`] holds the whole-prefix
//! facts to a fold over declarations alone, and
//! [`inference_demand_closures`] is then what each file's inference still
//! needs inferred.

use std::collections::BTreeSet;

use crate::hash::HashMap;
use crate::{AssemblyEnv, InferredProject, ItemId, ProjectFile, Resolution, ResolvedProject};

/// Where the whole-prefix facts stop being a fold over declarations: the
/// first file whose declared types, cases, records or constructor names
/// differ between [`crate::infer_project()`]'s fold (`inferred`) and a fold
/// that builds each file's declared facts from its surface walk, which
/// never meets a body, without inferring it, described;
/// `None` when no file's do.
pub fn whole_prefix_facts_divergence(
    files: &[ProjectFile],
    resolved: &ResolvedProject,
    env: &AssemblyEnv,
    inferred: &InferredProject,
) -> Option<String> {
    crate::infer_project::whole_prefix_facts_divergence(files, resolved, env, inferred)
}

/// For each file, the earlier files whose inference its own needs: those
/// declaring an earlier file's value (not a case) that it resolves a use to,
/// and, closed over the same relation, those their own inference needs.
///
/// A file's resolutions name every earlier item it uses, so this is the
/// demand of a full walk of the file. It over-approximates what inference
/// reads, since a use inference does not type still pulls its file in.
pub fn inference_demand_closures(resolved: &ResolvedProject) -> Vec<BTreeSet<usize>> {
    let mut value_file: HashMap<ItemId, usize> = HashMap::default();
    for (file, rf) in resolved.files().iter().enumerate() {
        for export in rf.exports().iter() {
            if export.case_kind().is_none() {
                value_file.insert(export.id(), file);
            }
        }
    }
    let mut closures: Vec<BTreeSet<usize>> = Vec::with_capacity(resolved.len());
    for (file, rf) in resolved.files().iter().enumerate() {
        let mut closure = BTreeSet::new();
        for resolution in rf.resolutions().values() {
            if let Resolution::Item(id) = resolution
                && !rf.owns_item(*id)
                && let Some(&declaring) = value_file.get(id)
                && declaring < file
                && closure.insert(declaring)
            {
                closure.extend(closures[declaring].iter().copied());
            }
        }
        closures.push(closure);
    }
    closures
}
