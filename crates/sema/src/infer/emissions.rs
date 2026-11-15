//! [`Emissions`], in a module of its own so that its fields are reached only
//! through its methods.

use super::Incomplete;
use crate::def::DefId;
use crate::hash::{HashMap, HashSet};
use crate::resolve::Resolution;
use crate::ty::{Ty, TyVid};
use borzoi_cst::syntax::TextRange;

/// A member access's receiver whose type was known at the access
/// ([`Emissions::receiver`]).
#[derive(Debug, Clone, Copy)]
pub(super) struct Receiver {
    /// The dot after the receiver.
    pub(super) dot: TextRange,
    /// The receiver's variable.
    pub(super) var: TyVid,
    /// Its type at the access: ground, so no later unification moves it.
    pub(super) ty: Ty,
}

/// The length of both emission lists, the nodes and the local binders, for
/// a barrier to [discard back to](Emissions::discard_since).
#[derive(Debug, Clone, Copy)]
pub(super) struct EmissionMark {
    exprs: usize,
    locals: usize,
}

/// What the walk emits, for [`super::Gen::finish`] to read: FCS's
/// `tcSink`. The walk only writes it — it appends and discards back to a
/// mark — and nothing it decides reads it:
/// no method here answers a question about what was emitted.
/// [`Self::into_emitted`] gives `finish` what stands.
pub(super) struct Emissions {
    /// `(range, var)` per expression whose type to emit; `range` is the read-off
    /// key (and the same range the resolver keyed the occurrence under).
    exprs: Vec<(TextRange, TyVid)>,
    /// Every expression-level `let` binder [`super::Gen::local_binding`] bound (CE-1).
    /// Unlike a declaration's binder, a local sits *inside* an expression, so
    /// its publication is an emission like a node's: [`super::Gen::finish`] publishes
    /// one only if it is still in [`Self::local_emits`].
    local_defs: HashSet<DefId>,
    /// The local binders to publish, in walk order — the binder-side twin of
    /// [`Self::exprs`], and discarded with it by an emission barrier
    /// ([`Self::discard_since`]).
    local_emits: Vec<DefId>,
    /// Each member access's receiver whose type was known at the access —
    /// never discarded, for
    /// [`InferredFile::receiver_type_at`](super::InferredFile::receiver_type_at).
    receivers: Vec<Receiver>,
    /// Each begun binding's incompleteness reasons, for
    /// [`InferredFile::incompleteness`](super::InferredFile::incompleteness).
    incompleteness: Vec<Vec<Incomplete>>,
    /// Ranges whose emission [`super::Gen::finish`] drops: a `match` scrutinee's own
    /// node, which FCS may cover with a temporary's `let` typed as the whole
    /// match. Filtered at read-off rather than cut from [`Self::exprs`], whose
    /// positions emission marks record.
    ungraded_ranges: HashSet<TextRange>,
    /// Each successfully-woken member access → its resolved identity, keyed by the
    /// member-name use range (Stage 3.3b). Filled by [`super::Gen::wake_member`] on a
    /// single-candidate discharge; read out in [`super::Gen::finish`] into
    /// [`InferredFile::member_resolutions`](super::InferredFile::member_resolutions).
    member_resolutions: HashMap<TextRange, Resolution>,
    /// How many expression levels the walk has open on its recursion now
    /// ([`super::Gen::infer_expr_inner`], [`super::Gen::infer_callee`]), and the most there
    /// have been ([`InferredFile::deepest_expression_walk`](super::InferredFile::deepest_expression_walk)).
    expr_depth: usize,
    deepest_expr_depth: usize,
}

/// What stands of a file's [`Emissions`] once its walk is over
/// ([`Emissions::into_emitted`]).
pub(super) struct Emitted {
    /// The nodes to read back, in walk order: every node no barrier
    /// discarded, but for the ungraded ones.
    pub(super) exprs: Vec<(TextRange, TyVid)>,
    /// Every local binder the walk bound.
    pub(super) local_defs: HashSet<DefId>,
    /// The local binders no barrier discarded.
    pub(super) published_locals: HashSet<DefId>,
    pub(super) receivers: Vec<Receiver>,
    pub(super) incompleteness: Vec<Vec<Incomplete>>,
    pub(super) member_resolutions: HashMap<TextRange, Resolution>,
    pub(super) deepest_expr_depth: usize,
}

impl Emissions {
    pub(super) fn new() -> Self {
        Emissions {
            exprs: Vec::new(),
            local_defs: HashSet::default(),
            local_emits: Vec::new(),
            receivers: Vec::new(),
            incompleteness: Vec::new(),
            ungraded_ranges: HashSet::default(),
            member_resolutions: HashMap::default(),
            expr_depth: 0,
            deepest_expr_depth: 0,
        }
    }

    /// Record the node at `range`, whose type is `v`'s, for read-off.
    pub(super) fn node(&mut self, range: TextRange, v: TyVid) {
        self.exprs.push((range, v));
    }

    /// Record the local binder `def` for publication.
    pub(super) fn local(&mut self, def: DefId) {
        self.local_defs.insert(def);
        self.local_emits.push(def);
    }

    /// Record the receiver before the dot at `dot`: its variable `var` stood
    /// for `ty`, a ground type, at the access.
    pub(super) fn receiver(&mut self, dot: TextRange, var: TyVid, ty: Ty) {
        self.receivers.push(Receiver { dot, var, ty });
    }

    /// Record a walked binding's census entry: why it is incomplete, empty
    /// if it is complete.
    pub(super) fn census(&mut self, reasons: Vec<Incomplete>) {
        self.incompleteness.push(reasons);
    }

    /// Leave ungraded the last node recorded since `mark`, if any.
    pub(super) fn ungrade_last_since(&mut self, mark: EmissionMark) {
        if let Some(&(range, _)) = self.exprs[mark.exprs..].last() {
            self.ungraded_ranges.insert(range);
        }
    }

    /// The current length of both emission lists — the expression nodes and the
    /// local binders — for a barrier to [discard back to](Self::discard_since).
    pub(super) fn mark(&self) -> EmissionMark {
        EmissionMark {
            exprs: self.exprs.len(),
            locals: self.local_emits.len(),
        }
    }

    /// Discard every emission recorded since `mark`: the nodes *and* the local
    /// binders a walk inside a barrier produced. A method call is such a barrier
    /// (FCS keeps nothing inside a call it rejects, so we keep nothing inside any
    /// call); the two lists are cut together so a `let` in a call's argument
    /// cannot publish its binder while the argument's nodes are dropped.
    pub(super) fn discard_since(&mut self, mark: EmissionMark) {
        self.exprs.truncate(mark.exprs);
        self.local_emits.truncate(mark.locals);
    }

    /// Record that the member-name token at `use_range` resolves to `res`.
    pub(super) fn member_resolution(&mut self, use_range: TextRange, res: Resolution) {
        self.member_resolutions.insert(use_range, res);
    }

    /// Count one more expression level open on the walk's recursion
    /// ([`InferredFile::deepest_expression_walk`](super::InferredFile::deepest_expression_walk));
    /// the caller closes it with [`Self::leave_expression`].
    pub(super) fn enter_expression(&mut self) {
        self.expr_depth += 1;
        self.deepest_expr_depth = self.deepest_expr_depth.max(self.expr_depth);
    }

    /// Close the expression level [`Self::enter_expression`] opened.
    pub(super) fn leave_expression(&mut self) {
        self.expr_depth -= 1;
    }

    /// What stands of the walk's emissions: what a barrier or an ungraded
    /// range dropped is gone.
    pub(super) fn into_emitted(self) -> Emitted {
        let published_locals = self.local_emits.iter().copied().collect();
        let exprs = self
            .exprs
            .iter()
            .filter(|&&(range, _)| !self.ungraded_ranges.contains(&range))
            .copied()
            .collect();
        Emitted {
            exprs,
            local_defs: self.local_defs,
            published_locals,
            receivers: self.receivers,
            incompleteness: self.incompleteness,
            member_resolutions: self.member_resolutions,
            deepest_expr_depth: self.deepest_expr_depth,
        }
    }
}
