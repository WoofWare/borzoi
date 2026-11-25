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

/// What one referenced assembly contributes to the extension gate's existence
/// questions: everything it declares, at every accessibility.
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
    /// The containers holding, anywhere in their entity tree, an abbreviation
    /// marked `[<Extension>]` or `[<AutoOpen>]` (at any accessibility): its
    /// namespace and each enclosing module's path. Each brings its target's
    /// extensions wherever the container is opened.
    abbreviation_lenders: HashSet<Vec<String>>,
    /// Every assembly-level `[<assembly: AutoOpen("…")>]` path, whatever it
    /// names and whether or not name resolution opens it (a namespace another
    /// assembly also declares is contested, and not opened there): each is a
    /// container whose contents answer to short names in every file.
    auto_open_bases: Vec<Vec<String>>,
    /// Every member that may be an extension, by every name a call may spell
    /// it ([`borzoi_assembly::ExtensionRow`]).
    extensions: HashMap<String, Vec<ExtensionSite>>,
    /// Some input was synthetic: its entities, not an index, are the truth,
    /// so the extension query reads them ([`Self::extensions_from_entities`]).
    synthetic: bool,
    /// Some assembly's declarations are unknown.
    unknowable: bool,
}

/// Where one possible extension is declared.
#[derive(Debug, Clone)]
struct ExtensionSite {
    /// The declaring entity's namespace, canonical.
    namespace: Vec<String>,
    /// The namespace followed by the declaring entity and its enclosers.
    container: Vec<String>,
    /// `Some(true)` for an instance extension, `Some(false)` for a static
    /// one, `None` when either.
    instance: Option<bool>,
}

/// The accessor spellings an F# property or event compiles to.
const ACCESSOR_PREFIXES: [&str; 4] = ["get_", "set_", "add_", "remove_"];

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

/// The path an assembly-level `[<AutoOpen("…")>]` argument names: FCS's
/// `splitNamespace`, a plain dotted path (no quoted-identifier escaping at
/// this level), or `None` with an empty segment.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn auto_open_segments(path: &str) -> Option<Vec<String>> {
    let segments: Vec<String> = path.split('.').map(str::to_string).collect();
    (!segments.iter().any(String::is_empty)).then_some(segments)
}

impl ExistenceSet {
    /// Every entity fact the set holds, in a comparable form: what its
    /// entity questions read, and nothing else.
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn facts(&self) -> ExistenceFacts {
        let mut facts = ExistenceFacts {
            unknowable: self.unknowable,
            prefixes: self.prefixes.iter().cloned().collect(),
            entities: self.entities.iter().cloned().collect(),
            abbreviation_lenders: self.abbreviation_lenders.iter().cloned().collect(),
            auto_open_bases: self.auto_open_bases.iter().cloned().collect(),
            ..ExistenceFacts::default()
        };
        for (parent, children) in &self.children {
            for child in children {
                let mut path = parent.clone();
                path.push(child.name.clone());
                if child.lends_children {
                    facts.lends_children.insert(path.clone());
                }
                if child.lends_anything {
                    facts.lends_anything.insert(path);
                }
            }
        }
        facts
    }

    /// Add one assembly's contribution.
    pub(crate) fn add(&mut self, input: &ExistenceInput, roots: &[Entity]) {
        match input {
            ExistenceInput::Read(index) => self.add_index(index),
            ExistenceInput::Unread => self.unknowable = true,
            ExistenceInput::Synthetic => {
                self.synthetic = true;
                for root in roots {
                    let namespace = canonical_path(&root.namespace);
                    self.add_entity(&namespace, &namespace, root);
                }
            }
        }
    }

    /// Record that some assembly's declarations are unknown.
    pub(crate) fn mark_unknowable(&mut self) {
        self.unknowable = true;
    }

    /// Record an assembly-level auto-open path (FSharp.Core's implicit
    /// `Microsoft` included).
    pub(crate) fn add_auto_open_base(&mut self, path: Vec<String>) {
        if !self.auto_open_bases.contains(&path) {
            self.auto_open_bases.push(path);
        }
    }

    /// Every assembly-level auto-open path ([`Self::add_auto_open_base`]).
    pub(crate) fn auto_open_bases(&self) -> &[Vec<String>] {
        &self.auto_open_bases
    }

    fn add_path(&mut self, path: Vec<String>, child: Option<Child>) {
        // Longest first: every prefix of a held path is held, so the first
        // one already present ends the walk, and a wide tree costs one insert
        // per new prefix rather than one per prefix per path.
        for k in (0..=path.len()).rev() {
            if !self.prefixes.insert(path[..k].to_vec()) {
                break;
            }
        }
        if let Some(child) = child {
            let parent = path[..path.len() - 1].to_vec();
            self.children.entry(parent).or_default().push(child);
            self.entities.insert(path);
        }
    }

    fn add_index(&mut self, index: &ExistenceIndex) {
        for row in &index.extensions {
            let namespace = canonical_path(&row.namespace);
            let mut container = namespace.clone();
            container.extend(row.enclosing.iter().map(|s| canonical(s)));
            for name in &row.names {
                self.extensions
                    .entry(name.clone())
                    .or_default()
                    .push(ExtensionSite {
                        namespace: namespace.clone(),
                        container: container.clone(),
                        instance: row.instance,
                    });
            }
        }
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
                    let mut parent = namespace;
                    let namespace_len = parent.len();
                    parent.extend(row.enclosing.iter().map(|s| canonical(s)));
                    if abbreviation && (row.extension || row.auto_open) {
                        for k in namespace_len..=parent.len() {
                            self.abbreviation_lenders.insert(parent[..k].to_vec());
                        }
                    }
                    let mut spellings = vec![canonical(&row.logical_name)];
                    let compiled = canonical(&row.compiled_name);
                    if !spellings.contains(&compiled) {
                        spellings.push(compiled);
                    }
                    for name in spellings {
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

    /// Add `entity`, directly inside `parent`, whose top-level ancestor's
    /// namespace is `namespace` (a nested entity's own is empty).
    fn add_entity(&mut self, namespace: &[String], parent: &[String], entity: &Entity) {
        let abbreviation = entity.kind == EntityKind::Abbreviation;
        if abbreviation && (entity.is_extension_container || entity.is_auto_open) {
            for k in namespace.len()..=parent.len() {
                self.abbreviation_lenders.insert(parent[..k].to_vec());
            }
        }
        // One walk per distinct spelling: a module's metadata and source
        // names (`MModule`, `M`) are one canonical name.
        let mut spellings = vec![canonical(&entity.name)];
        if let Some(source) = &entity.source_name {
            let source = canonical(source);
            if !spellings.contains(&source) {
                spellings.push(source);
            }
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
                self.add_entity(namespace, &path, nested);
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

    /// Whether some input was synthetic, so that its entities answer the
    /// extension query rather than the index.
    pub(crate) fn extensions_from_entities(&self) -> bool {
        self.synthetic
    }

    /// Whether a member that may be an extension of `name` (`is_static`: for
    /// a type-qualified call) is declared anywhere in one of `containers`'
    /// entity trees: a namespace's whole tree, or a module path's subtree.
    /// `name` is also read in each accessor spelling, and without one, since
    /// a call may reach a property or event by either.
    pub(crate) fn extension_named<'c>(
        &self,
        containers: impl IntoIterator<Item = &'c [String]>,
        name: &str,
        is_static: bool,
    ) -> bool {
        if self.unknowable {
            return true;
        }
        let sites = self.sites(name, is_static);
        if sites.is_empty() {
            return false;
        }
        containers.into_iter().any(|container| {
            let container = canonical_path(container);
            sites.iter().any(|site| {
                site.namespace == container
                    || (container.len() > site.namespace.len()
                        && site.container.starts_with(&container))
            })
        })
    }

    /// The declarations of every member that may be an extension of `name`
    /// (`is_static`: for a type-qualified call), read in each accessor
    /// spelling and without one.
    fn sites(&self, name: &str, is_static: bool) -> Vec<&ExtensionSite> {
        let bare = ACCESSOR_PREFIXES
            .iter()
            .find_map(|p| name.strip_prefix(p))
            .unwrap_or(name);
        let mut spellings = vec![name.to_string(), bare.to_string()];
        spellings.extend(ACCESSOR_PREFIXES.iter().map(|p| format!("{p}{bare}")));
        spellings.sort();
        spellings.dedup();
        spellings
            .iter()
            .filter_map(|s| self.extensions.get(s))
            .flatten()
            .filter(|site| site.instance.is_none_or(|instance| instance != is_static))
            .collect()
    }

    /// Whether any referenced assembly may declare an extension of `name`
    /// anywhere: the universe an `open` the gate cannot enumerate draws from.
    /// When it holds none, no `open` can bring one, enumerated or not. An
    /// unknowable or synthetic set, or any abbreviation marked
    /// `[<Extension>]` or `[<AutoOpen>]` (whose target the index does not
    /// record), may hold every name.
    pub(crate) fn extension_named_anywhere(&self, name: &str, is_static: bool) -> bool {
        self.unknowable
            || self.synthetic
            || !self.abbreviation_lenders.is_empty()
            || !self.sites(name, is_static).is_empty()
    }

    /// Whether the container at `namespace` (a namespace, or a module's path)
    /// holds, anywhere in its entity tree, an abbreviation marked
    /// `[<Extension>]` or `[<AutoOpen>]` at any accessibility, which brings
    /// its target's extensions into scope wherever the container is opened.
    pub(crate) fn lends_extensions_through_an_abbreviation(&self, namespace: &[String]) -> bool {
        self.unknowable
            || self
                .abbreviation_lenders
                .contains(&canonical_path(namespace))
    }
}

/// The entity facts an `ExistenceSet` holds (`ExistenceSet::facts`), each a
/// set whose every element only ever makes a question answer "something may
/// be there": one set's facts holding another's means it answers every
/// entity question at least as permissively.
#[cfg(any(test, feature = "test-support"))]
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExistenceFacts {
    pub unknowable: bool,
    /// Every prefix of every namespace and entity path, canonical.
    pub prefixes: std::collections::BTreeSet<Vec<String>>,
    /// Every entity path, canonical.
    pub entities: std::collections::BTreeSet<Vec<String>>,
    /// The entities whose children answer to short names where their
    /// container is opened (an `[<AutoOpen>]` module or type).
    pub lends_children: std::collections::BTreeSet<Vec<String>>,
    /// The entities that may lend any short name (an `[<AutoOpen>]`
    /// abbreviation).
    pub lends_anything: std::collections::BTreeSet<Vec<String>>,
    /// The containers holding an abbreviation marked `[<Extension>]` or
    /// `[<AutoOpen>]`.
    pub abbreviation_lenders: std::collections::BTreeSet<Vec<String>>,
    pub auto_open_bases: std::collections::BTreeSet<Vec<String>>,
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
        let mut nested = pickled("D", "Nested", PickledEntityKind::Abbreviation);
        nested.enclosing = vec!["MModule".to_string()];
        nested.auto_open = true;
        let index = ExistenceIndex {
            il: vec![
                il("A", &[], "MModule", false),
                il("A", &["MModule"], "Inner", inner_auto_open),
                il("A", &["MModule", "Inner"], "Hidden", false),
                il("A.N", &[], "Only`1", false),
            ],
            pickle: PickleLayer::Read(vec![
                pickled("", "B", PickledEntityKind::Namespace),
                alias,
                nested,
            ]),
            extensions: Vec::new(),
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
        assert!(whole.lends_extensions_through_an_abbreviation(&segs("D.M")));
        assert!(whole.lends_extensions_through_an_abbreviation(&segs("D")));
        assert!(!whole.lends_extensions_through_an_abbreviation(&segs("A")));
    }

    /// A synthetic module `N.MModule` (source name `M`) holding a marked
    /// abbreviation: the abbreviation lends at `N` and `N.M`, not at the
    /// root, and the module's two spellings are walked once.
    #[test]
    fn a_synthetic_nested_abbreviation_lends_at_its_own_containers() {
        use crate::assembly_env::from_views_tests::module_entity;
        use borzoi_assembly::EntityKind;

        let mut alias = module_entity("Lib", &[], "Alias");
        alias.kind = EntityKind::Abbreviation;
        alias.is_extension_container = true;
        // A chain of modules each spelled twice alike, ending at the alias.
        let mut inner = alias;
        for depth in (0..24).rev() {
            let mut m = module_entity("Lib", &[], &format!("L{depth}Module"));
            m.source_name = Some(format!("L{depth}"));
            m.nested_types = vec![inner];
            inner = m;
        }
        let mut top = module_entity("Lib", &["N"], "MModule");
        top.source_name = Some("M".to_string());
        top.nested_types = vec![inner];
        let mut set = ExistenceSet::default();
        set.add(&ExistenceInput::Synthetic, &[top]);
        assert!(set.lends_extensions_through_an_abbreviation(&segs("N")));
        assert!(set.lends_extensions_through_an_abbreviation(&segs("N.M")));
        assert!(!set.lends_extensions_through_an_abbreviation(&[]));
        assert!(!set.lends_extensions_through_an_abbreviation(&segs("Other")));
        // One child per entity: each spelled-alike module walked once.
        let children: usize = set.children.values().map(Vec::len).sum();
        assert_eq!(children, 26, "the two spellings were walked separately");
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
