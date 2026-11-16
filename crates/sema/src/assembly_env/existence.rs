//! The extension gate's existence questions, answered from the referenced
//! assemblies' raw metadata ([`borzoi_assembly::existence`]) and nothing
//! else.
//!
//! Name resolution reads an assembly through the [`Entity`] projection, which
//! filters what a referencing assembly cannot name. A friend assembly
//! (`InternalsVisibleTo`) sees what the filter took away, so a question of
//! existence ("may anything, of any accessibility, sit at this path?") reads
//! the [`ExistenceSet`] instead. It is built from each assembly's
//! [`ExistenceIndex`]: every `TypeDef` row and every entity of the host F#
//! pickle, at every accessibility, which `assembly_entities_diff` holds to FCS
//! and to `System.Reflection.Metadata`. The set's fields are private to this
//! module and it holds no reference to the env, so the open certification,
//! which is handed only an `&ExistenceSet`, cannot reach name resolution's
//! view at all.
//!
//! Names are compared in one canonical spelling per segment: a generic arity
//! suffix (`` `1 ``) and a module's `Module` suffix are stripped, on the
//! index's side and the query's alike. Two names that differ only in those
//! read as one, which can only make the set answer "something may be there"
//! more often.

use crate::hash::{HashMap, HashSet};

use borzoi_assembly::{Entity, EntityKind, ExistenceIndex, PickleLayer, PickledEntityKind};

/// What one referenced assembly contributes to the [`ExistenceSet`].
#[derive(Debug, Clone)]
pub enum ExistenceInput {
    /// The assembly's existence index, read from its metadata.
    Read(ExistenceIndex),
    /// The index could not be read: the assembly may declare anything.
    Unread,
    /// The assembly is synthetic (a test's hand-built entities), and its
    /// entities are everything it declares.
    Synthetic,
}

/// One entity directly inside a namespace or another entity.
#[derive(Debug, Clone)]
struct Child {
    /// The canonical name.
    name: String,
    /// Opening its container lends its own children short names: an
    /// `[<AutoOpen>]` module, or an entity with an attribute whose owner is
    /// unreadable (which may be that marker).
    lends_children: bool,
    /// Opening its container may lend any short name: an `[<AutoOpen>]`
    /// abbreviation, whose target the index does not record.
    lends_anything: bool,
}

/// Everything the referenced assemblies declare, at every accessibility, as
/// the extension gate's existence questions read it.
#[derive(Debug, Clone, Default)]
pub struct ExistenceSet {
    /// Every prefix of every namespace and of every entity's path.
    prefixes: HashSet<Vec<String>>,
    /// Every entity's path (namespace, enclosing entities, name).
    entities: HashSet<Vec<String>>,
    /// The entities directly inside each namespace or entity path.
    children: HashMap<Vec<String>, Vec<Child>>,
    /// The namespaces holding, anywhere in their entity tree, an abbreviation
    /// marked `[<Extension>]` or `[<AutoOpen>]` (at any accessibility): each
    /// brings its target's extensions wherever the namespace is in scope.
    abbreviation_lenders: HashSet<Vec<String>>,
    /// Some assembly's declarations are unknown.
    unknowable: bool,
}

/// `name` in the set's canonical spelling.
fn canonical(name: &str) -> String {
    let bare = name.split('`').next().unwrap_or(name);
    match bare.strip_suffix("Module") {
        Some(stem) if !stem.is_empty() => stem.to_string(),
        _ => bare.to_string(),
    }
}

fn canonical_path(path: &[String]) -> Vec<String> {
    path.iter().map(|s| canonical(s)).collect()
}

impl ExistenceSet {
    /// Add one assembly's contribution.
    pub(crate) fn add(&mut self, input: &ExistenceInput, roots: &[Entity]) {
        match input {
            ExistenceInput::Read(index) => self.add_index(index),
            ExistenceInput::Unread => self.unknowable = true,
            ExistenceInput::Synthetic => {
                for root in roots {
                    self.add_entity(&canonical_path(&root.namespace), root);
                }
            }
        }
    }

    /// Record that some assembly's declarations are unknown.
    pub(crate) fn mark_unknowable(&mut self) {
        self.unknowable = true;
    }

    fn add_path(&mut self, path: Vec<String>, child: Option<Child>) {
        for k in 0..=path.len() {
            self.prefixes.insert(path[..k].to_vec());
        }
        if let Some(child) = child {
            let parent = path[..path.len() - 1].to_vec();
            self.children.entry(parent).or_default().push(child);
            self.entities.insert(path);
        }
    }

    fn add_index(&mut self, index: &ExistenceIndex) {
        for row in &index.il {
            let mut path = canonical_path(&row.namespace);
            path.extend(row.enclosing.iter().map(|s| canonical(s)));
            let name = canonical(&row.name);
            path.push(name.clone());
            let child = Child {
                name,
                lends_children: row.auto_open || row.unreadable_attribute,
                lends_anything: false,
            };
            self.add_path(path, Some(child));
        }
        match &index.pickle {
            PickleLayer::NotFSharp => {}
            PickleLayer::Unreadable(_) => self.unknowable = true,
            PickleLayer::Read(rows) => {
                for row in rows {
                    let namespace = canonical_path(&row.namespace);
                    if row.kind == PickledEntityKind::Namespace {
                        let mut path = namespace;
                        path.push(canonical(&row.logical_name));
                        self.add_path(path, None);
                        continue;
                    }
                    let abbreviation = row.kind == PickledEntityKind::Abbreviation;
                    if abbreviation && (row.extension || row.auto_open) {
                        self.abbreviation_lenders.insert(namespace.clone());
                    }
                    let mut parent = namespace;
                    parent.extend(row.enclosing.iter().map(|s| canonical(s)));
                    for spelling in [&row.logical_name, &row.compiled_name] {
                        let name = canonical(spelling);
                        let mut path = parent.clone();
                        path.push(name.clone());
                        let child = Child {
                            name,
                            lends_children: row.auto_open && !abbreviation,
                            lends_anything: row.auto_open && abbreviation,
                        };
                        self.add_path(path, Some(child));
                    }
                }
            }
        }
    }

    fn add_entity(&mut self, parent: &[String], entity: &Entity) {
        let abbreviation = entity.kind == EntityKind::Abbreviation;
        if abbreviation && (entity.is_extension_container || entity.is_auto_open) {
            self.abbreviation_lenders
                .insert(canonical_path(&entity.namespace));
        }
        let mut spellings = vec![canonical(&entity.name)];
        if let Some(source) = &entity.source_name {
            spellings.push(canonical(source));
        }
        for name in spellings {
            let mut path = parent.to_vec();
            path.push(name.clone());
            let child = Child {
                name,
                lends_children: entity.is_auto_open && !abbreviation,
                lends_anything: entity.is_auto_open && abbreviation,
            };
            self.add_path(path.clone(), Some(child));
            for nested in &entity.nested_types {
                self.add_entity(&path, nested);
            }
        }
    }

    /// Whether the assemblies hold nothing, of any accessibility, at or under
    /// `path`: no namespace at or under it, and no entity whose path it is or
    /// begins. Nothing at `path` means nothing at any extension of it.
    pub(crate) fn holds_nothing_at(&self, path: &[String]) -> bool {
        !self.unknowable && !self.prefixes.contains(&canonical_path(path))
    }

    /// Whether no entity, of any accessibility, sits at any split of `path`:
    /// every prefix of it the assemblies hold is a namespace.
    pub(crate) fn names_namespaces_only(&self, path: &[String]) -> bool {
        let path = canonical_path(path);
        !self.unknowable && (1..=path.len()).all(|k| !self.entities.contains(&path[..k]))
    }

    /// Whether opening `path` may lend `name` as a short name through an
    /// `[<AutoOpen>]` chain, whatever the chain's accessibility: a child
    /// answering to `name` of an auto-open entity directly inside `path`, or
    /// (transitively) inside such an entity; or an auto-open abbreviation
    /// anywhere on such a chain, whose target may hold anything.
    pub(crate) fn lends_a_short_name_under(&self, path: &[String], name: &str) -> bool {
        if self.unknowable {
            return true;
        }
        let name = canonical(name);
        let mut stack: Vec<Vec<String>> = vec![canonical_path(path)];
        let mut seen: HashSet<Vec<String>> = HashSet::default();
        let mut first = true;
        while let Some(container) = stack.pop() {
            if !seen.insert(container.clone()) {
                continue;
            }
            for child in self.children.get(&container).into_iter().flatten() {
                if !first && child.name == name {
                    return true;
                }
                if child.lends_anything {
                    return true;
                }
                if child.lends_children {
                    let mut next = container.clone();
                    next.push(child.name.clone());
                    stack.push(next);
                }
            }
            first = false;
        }
        false
    }

    /// Whether `namespace` holds, anywhere in its entity tree, an
    /// abbreviation marked `[<Extension>]` or `[<AutoOpen>]` at any
    /// accessibility, which brings its target's extensions into scope
    /// wherever the namespace is.
    pub(crate) fn lends_extensions_through_an_abbreviation(&self, namespace: &[String]) -> bool {
        self.unknowable
            || self
                .abbreviation_lenders
                .contains(&canonical_path(namespace))
    }
}

#[cfg(test)]
mod tests {
    use super::{ExistenceInput, ExistenceSet};
    use borzoi_assembly::{
        ExistenceIndex, IlTypeRow, IlVisibility, PickleLayer, PickledEntityKind, PickledEntityRow,
    };

    fn segs(path: &str) -> Vec<String> {
        path.split('.').map(str::to_owned).collect()
    }

    fn il(namespace: &str, enclosing: &[&str], name: &str, auto_open: bool) -> IlTypeRow {
        IlTypeRow {
            namespace: segs(namespace),
            enclosing: enclosing.iter().map(|s| (*s).to_string()).collect(),
            name: name.to_string(),
            visibility: IlVisibility::NotPublic,
            auto_open,
            extension: false,
            unreadable_attribute: false,
        }
    }

    fn pickled(namespace: &str, name: &str, kind: PickledEntityKind) -> PickledEntityRow {
        PickledEntityRow {
            namespace: segs(namespace),
            enclosing: Vec::new(),
            logical_name: name.to_string(),
            compiled_name: name.to_string(),
            kind,
            public: false,
            auto_open: false,
            extension: false,
        }
    }

    /// `A.M` (internal) holds an auto-open `Inner` holding `Hidden`, `A.N`
    /// holds only an internal type, and `B` holds only an internal
    /// `[<Extension>]` abbreviation.
    fn set(inner_auto_open: bool) -> ExistenceSet {
        let mut alias = pickled("B", "Alias", PickledEntityKind::Abbreviation);
        alias.extension = true;
        let index = ExistenceIndex {
            il: vec![
                il("A", &[], "MModule", false),
                il("A", &["MModule"], "Inner", inner_auto_open),
                il("A", &["MModule", "Inner"], "Hidden", false),
                il("A.N", &[], "Only`1", false),
            ],
            pickle: PickleLayer::Read(vec![pickled("", "B", PickledEntityKind::Namespace), alias]),
        };
        let mut set = ExistenceSet::default();
        set.add(&ExistenceInput::Read(index), &[]);
        set
    }

    #[test]
    fn the_set_reads_what_a_path_reaches_whatever_its_accessibility() {
        let whole = set(true);
        for (path, nothing) in [
            ("A", false),
            ("A.M", false),
            ("A.MModule", false),
            ("A.M.Inner.Hidden", false),
            ("A.N", false),
            ("A.N.Only", false),
            ("B", false),
            ("B.Alias", false),
            ("A.M.X", true),
            ("A.N.X", true),
            ("C", true),
        ] {
            assert_eq!(whole.holds_nothing_at(&segs(path)), nothing, "{path}");
        }
        assert!(whole.names_namespaces_only(&segs("A.N")));
        assert!(!whole.names_namespaces_only(&segs("A.M.Inner")));
        assert!(whole.lends_a_short_name_under(&segs("A.M"), "Hidden"));
        assert!(!whole.lends_a_short_name_under(&segs("A.M"), "Inner"));
        assert!(!whole.lends_a_short_name_under(&segs("A"), "Hidden"));
        assert!(!set(false).lends_a_short_name_under(&segs("A.M"), "Hidden"));
        assert!(whole.lends_extensions_through_an_abbreviation(&segs("B")));
        assert!(!whole.lends_extensions_through_an_abbreviation(&segs("A")));
    }

    #[test]
    fn an_unread_assembly_holds_anything() {
        let mut set = set(false);
        set.add(&ExistenceInput::Unread, &[]);
        assert!(!set.holds_nothing_at(&segs("C")));
        assert!(!set.names_namespaces_only(&segs("A.N")));
        assert!(set.lends_a_short_name_under(&segs("A"), "Anything"));
        assert!(set.lends_extensions_through_an_abbreviation(&segs("A")));
    }
}
