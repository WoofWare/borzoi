//! FCS's record-label table, as far as the file's own records decide it
//! ([`ResolvedFile::field_label_on_unknown_receiver`](super::ResolvedFile::field_label_on_unknown_receiver)).
//!
//! FCS keeps every record label in scope in one table, `eFieldLabels`, a
//! multimap whose head is the latest addition (`AddRecdField`,
//! NameResolution.fs). A record's labels are added wherever its type enters
//! the environment unqualified (`AddStaticPartsOfTyconRefToNameEnv`): its own
//! declaration, an `open` of its module or namespace, the close of an
//! `[<AutoOpen>]` module holding it, the implicit open of a namespace an
//! earlier file declared it in, a referenced assembly. A
//! `[<RequireQualifiedAccess>]` record adds none, even in its own module.
//! When FCS's member lookup on a receiver it knows nothing about finds
//! nothing, it resolves the label to the table's head
//! (`ResolveExprDotLongIdent`).
//!
//! The walk models the additions the file's own record declarations make:
//! each enters its labels into the container it is declared in. A scope
//! sees its own container's entries and its enclosing containers',
//! innermost first, so a nested module's records shadow the outer ones and
//! leave with it. A label whose latest entry in scope is such a record
//! commits; everything else the table may hold declines:
//!
//! - an `open` after the entry, which may add the label from anywhere
//!   ([`OpenScope::latest_open_pos`](super::open_scope::OpenScope::latest_open_pos));
//! - no entry in the file: the winner is an earlier file's or an assembly's
//!   record, or there is none;
//! - an entry from an earlier block of the same namespace, which the block's
//!   implicit open of its own namespace may outrank with another file's
//!   record;
//! - an entry outside the enclosing namespace, which FCS does not open;
//! - a `rec` module or namespace, where FCS adds every record of the block
//!   ahead of the walk;
//! - an entry that may or may not be there: a record whose
//!   `[<RequireQualifiedAccess>]` is uncertain, or a label it declares twice;
//! - a record with a spread (`{ ...T; F: int }`), which copies labels the walk
//!   does not read, and whose later spread may replace an explicit field of
//!   the same name: every entry it makes declines, and one more, which
//!   answers every label, shadows whatever it outranks;
//! - an entry an `[<AutoOpen>]` module's close (or a possible one) adds to
//!   the enclosing container. FCS adds the module's accessible records there,
//!   its own ahead of its `[<AutoOpen>]` submodules', but which records are
//!   accessible from the enclosing scope (a `private` record, a record in a
//!   `private` submodule) and whether an attribute is FSharp.Core's
//!   `AutoOpen` are each a question of its own; so every entry of the module
//!   is copied as one that declines, which shadows what it outranks and
//!   commits nothing;
//! - a use inside a type's member bodies, where FCS puts the enclosing
//!   record's own labels ahead of the table;
//! - recovered syntax anywhere before the use, which the published accessor
//!   checks: the walk reads nothing of the recovery reading.
//!
//! FCS consults the table only once its member lookup on the receiver has
//! found nothing. A type variable's type hierarchy is `obj`, so a label named
//! after one of `System.Object`'s public members ([`OBJECT_MEMBERS`]) is that
//! member, never a field, and declines; an extension member of the label's
//! name, which the lookup finds too, is the published accessor's own gate.

use crate::hash::{HashMap, HashSet};

use borzoi_cst::syntax::{
    AstNode, NestedModuleDecl, SyntaxToken, TextRange, TypeDefn, TypeDefnRepr,
};

use super::contributors::RequireQualifiedAccess;
use super::model::{FieldLabel, FieldLabelEntry};
use super::state::Resolver;
use crate::def::{DefId, id_text};
use crate::names::PathId;

/// The public members of `System.Object`, which FCS's member lookup finds on
/// a receiver of unknown type before it consults the label table (its
/// protected `Finalize` and `MemberwiseClone` it does not: the label wins
/// there). `ReferenceEquals` is static, and found all the same: FCS reports
/// it as no instance method.
const OBJECT_MEMBERS: [&str; 5] = [
    "Equals",
    "GetHashCode",
    "GetType",
    "ReferenceEquals",
    "ToString",
];

/// One label in one container's part of the table.
#[derive(Debug, Clone)]
struct LabelEntry {
    /// The label, or `None` for an entry that answers every label: a record
    /// spread's, whose copied labels the walk does not read.
    name: Option<String>,
    label: FieldLabel,
    /// Where the label entered this container's scope.
    pos: u32,
    /// Whether FCS certainly adds the label here.
    certain: bool,
}

/// The file's additions to FCS's record-label table, by the container each
/// was made in, in walk order.
#[derive(Debug, Default)]
pub(super) struct LabelTable {
    by_container: HashMap<PathId, Vec<LabelEntry>>,
    /// Every label any entry carries: a use of any other label has no
    /// answer to look for, unless some entry answers every label
    /// ([`Self::any_label`]).
    names: HashSet<String>,
    /// Whether an entry answers every label (a record spread's).
    any_label: bool,
    /// How many type definitions' member bodies the walk is inside.
    in_type_bodies: usize,
}

impl LabelTable {
    fn push(&mut self, container: PathId, entry: LabelEntry) {
        match &entry.name {
            Some(name) => {
                self.names.insert(name.clone());
            }
            None => self.any_label = true,
        }
        self.by_container.entry(container).or_default().push(entry);
    }
}

impl Resolver<'_> {
    /// Enter the labels of `defn`, a type of the group starting at
    /// `group_pos` whose binder is `record`, into the current container, if
    /// it is a record.
    pub(super) fn define_record_labels(
        &mut self,
        defn: &TypeDefn,
        record: DefId,
        arity: usize,
        group_pos: u32,
    ) {
        let Some(TypeDefnRepr::Record(repr)) = defn.repr() else {
            return;
        };
        let certain = match self.require_qualified_access(defn.attributes()) {
            RequireQualifiedAccess::Certain => return,
            RequireQualifiedAccess::CertainlyNot => true,
            RequireQualifiedAccess::Unknown { .. } => false,
        };
        // A spread (`{ ...T; F: int }`) copies `T`'s fields, which the walk
        // does not read: the record may declare any label, and a later spread
        // may replace an explicit field of the same name. So every entry it
        // makes declines, and one more answers every label.
        let spread = repr.spreads().next().map(|(_, s)| s.syntax().text_range());
        let certain = certain && spread.is_none();
        let fields: Vec<(String, TextRange)> = repr
            .fields()
            .filter_map(|f| f.ident())
            .map(|tok| (id_text(&tok).to_string(), tok.text_range()))
            .collect();
        let container = self.lexical.container_path.id();
        for (name, field) in &fields {
            let twice = fields.iter().filter(|(n, _)| n == name).count() > 1;
            self.labels.push(
                container,
                LabelEntry {
                    name: Some(name.clone()),
                    label: FieldLabel {
                        record,
                        arity,
                        field: *field,
                    },
                    pos: group_pos,
                    certain: certain && !twice,
                },
            );
        }
        if let Some(spread) = spread {
            self.labels.push(
                container,
                LabelEntry {
                    name: None,
                    label: FieldLabel {
                        record,
                        arity,
                        field: spread,
                    },
                    pos: group_pos,
                    certain: false,
                },
            );
        }
    }

    /// Before the walk leaves `nm`, whose body's container is `inner`: if it
    /// may be `[<AutoOpen>]`, copy its entries into the enclosing container,
    /// `outer`, as entries that decline (see the [module docs](self)).
    pub(super) fn auto_open_record_labels(
        &mut self,
        nm: &NestedModuleDecl,
        inner: PathId,
        outer: PathId,
    ) {
        if !self.may_auto_open(nm.attributes()) {
            return;
        }
        let pos = u32::from(nm.syntax().text_range().end());
        let copies: Vec<LabelEntry> = self
            .labels
            .by_container
            .get(&inner)
            .into_iter()
            .flatten()
            .map(|e| LabelEntry {
                pos,
                certain: false,
                ..e.clone()
            })
            .collect();
        for entry in copies {
            self.labels.push(outer, entry);
        }
    }

    /// Walk a type definition's member bodies (`walk`), where FCS reads the
    /// enclosing record's labels ahead of the table, so nothing answers.
    pub(super) fn in_type_bodies(&mut self, walk: impl FnOnce(&mut Self)) {
        self.labels.in_type_bodies += 1;
        walk(self);
        self.labels.in_type_bodies -= 1;
    }

    /// Record what the table answers, here, at each of `segments`: labels
    /// after a receiver, whose type the walk does not know.
    pub(super) fn record_field_labels(&mut self, segments: &[SyntaxToken]) {
        for seg in segments {
            let name = id_text(seg);
            if !self.labels.any_label && !self.labels.names.contains(&*name) {
                continue;
            }
            if let Some(label) = self.field_label(&name) {
                self.out.field_labels.insert(
                    seg.text_range(),
                    FieldLabelEntry {
                        name: name.to_string(),
                        label,
                    },
                );
            }
        }
    }

    /// The record field the table's head names for `name` here, when the
    /// file's own additions decide it.
    fn field_label(&self, name: &str) -> Option<FieldLabel> {
        if self.scope.recursive_module_active
            || self.labels.in_type_bodies > 0
            || OBJECT_MEMBERS.contains(&name)
        {
            return None;
        }
        let block_start = self.index.block_starts.last().copied().unwrap_or(0);
        for k in (0..=self.lexical.container_path.len()).rev() {
            let Some(entry) = self
                .labels
                .by_container
                .get(&self.lexical.container_path.prefix_id(k))
                .and_then(|entries| {
                    entries
                        .iter()
                        .rev()
                        .find(|e| e.name.as_deref().is_none_or(|n| n == name))
                })
            else {
                continue;
            };
            let decided = entry.certain
                && k >= self.enclosing_namespace().len()
                && entry.pos >= block_start
                && self.scope.latest_open_pos <= entry.pos;
            return decided.then_some(entry.label);
        }
        None
    }
}
