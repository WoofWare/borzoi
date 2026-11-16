//! The receiver's type at each member access
//! ([`InferredFile::receiver_type_at`]): what FCS knows of the receiver when
//! it looks the member up.
//!
//! FCS looks a member up at its dot, on what it knows of the receiver there;
//! on a receiver it does not know it reports FS0072, whatever a later use
//! makes of it. So the record is taken at the access, from the table as it
//! stands there, and only where the receiver's type is ground: under the
//! faithful prefix and the post-loss rule a ground type in the table is one
//! FCS has too, and no later unification moves it.
//!
//! It is keyed by the dot after the receiver rather than by the member
//! after it: the dot is there for every segment of a chain (`s.Length.` has
//! two receivers), and for an access whose member is not written yet (`s.`),
//! which is when completion asks.

use super::*;
use crate::FcsRange as _;

/// A member access's path and the variables standing for its receivers:
/// `receivers[i]` for what precedes the `i`-th dot of `path`, so there are
/// as many as the path has dots.
pub(super) struct AccessPath<'p> {
    pub(super) path: &'p LongIdent,
    pub(super) receivers: Vec<TyVid>,
}

/// Every dot token directly in `path`, in order.
pub(super) fn path_dots(path: &LongIdent) -> impl Iterator<Item = SyntaxToken> + '_ {
    path.syntax()
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .filter(|t| t.kind() == SyntaxKind::DOT_TOK)
}

/// Whether `path` ends in a dot with no member after it (`s.`, `s.A.`): a
/// recovered access, whose member is not written.
pub(super) fn has_trailing_dot(path: &LongIdent) -> bool {
    path.syntax()
        .last_token()
        .is_some_and(|t| t.kind() == SyntaxKind::DOT_TOK)
}

impl<'a> Gen<'a> {
    /// Record the receiver before each dot of `access`, where its type is
    /// ground now: at the access, before anything after it is walked. Each
    /// caller records once the segments before the dot are resolved, as FCS
    /// has resolved them when it reaches the dot.
    pub(super) fn record_receivers(&mut self, access: AccessPath<'_>) {
        let AccessPath { path, receivers } = access;
        debug_assert_eq!(
            path_dots(path).count(),
            receivers.len(),
            "one receiver per dot of `{}`",
            path.syntax().text()
        );
        for (dot, var) in path_dots(path).zip(receivers) {
            let ty = self.solver.table.resolve(self.solver.tys.var(var));
            if self.solver.tys.is_ground(ty) {
                self.out.receiver(dot.fcs_range(), var, ty);
            }
        }
    }
}
