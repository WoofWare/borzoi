//! A referenced F# project's **entity surface**, read from its source
//! ([`source_existence`]): rows in the currency of
//! [`borzoi_assembly::existence`], so open certification can read a project
//! reference as it reads a DLL.
//!
//! The function is pure. Its input is a producer project A as the caller
//! evaluated it ([`Producer`]): A's Compile items, each parsed under A's own
//! defines and language version, and what the caller knows of A's references
//! ([`ProviderReferences`]). Its output ([`SourceExistence`]) is the rows, or
//! `Unread` with the reason A's surface is not read.
//!
//! # The claim
//!
//! When the walk reads A, every entity fact the existence set holds of FCS's
//! signature of A, the set built from these rows also holds. The facts are
//! namespace and entity prefixes, entities, the entities that lend their
//! children or anything, and auto-open bases (`test_support::existence_facts`).
//! Every such question is monotone, so the claim is containment.
//! `source_existence_diff` grades it against FCS's in-memory signature
//! (`fcs-dump`'s `referenced` op) and pins the surplus. The rows carry no
//! extension rows, and fields no entity question reads are constants: an
//! entity's accessibility (`public` is always `true`) and its `[<AutoOpen>]`
//! and `[<Extension>]` flags, which hold only under an attribute, and
//! attributes on entities decline.
//!
//! # The domain
//!
//! The walk reads only the simplest forms, and declines A on anything else:
//!
//! - implementation files, each with a `namespace` or named `module` header;
//! - nested modules, and names not ending in `Module` (FCS may add the
//!   suffix to such a name, which canonical spelling does not strip);
//! - records, unions, classes, structs, interfaces, enums and delegates, and
//!   abbreviations of an FSharp.Core name every file has open or of a
//!   structural type, every head non-dotted;
//! - exceptions;
//! - plain implementation augmentations (`type T with`, no constructor),
//!   which declare no entity;
//! - no attribute on any entity, no standalone attribute declaration, and no
//!   attribute with an explicit target. An untargeted attribute elsewhere (a
//!   `let`, a member, a field, a case) decides no entity fact.
//!
//! # What the walk reads, and how it knows it read all of it
//!
//! Each syntax node the walk interprets is a [`Leaf`], and the walk reads it
//! by classifying it into one [`Form`]: a closed list whose
//! [`Form::verdict`] says whether a producer holding it is read. A classifier
//! accounts for **every child** of its node ([`consumed`]): a child no
//! classifier names (an unexpected token, a node shape the grammar grows) is
//! [`ExistenceUnread::Unreadable`], so a child the walk did not read cannot
//! change the surface unseen. `source_existence_domain` grades every
//! [`Form::ALL`] witness against FCS.
//!
//! # The budget
//!
//! The rows hold paths, and a path is as long as its nesting: rows can take
//! memory quadratic in the input (a type at the bottom of a deep nest, a
//! long dotted namespace's prefixes). So the walk is handed a [`Budget`] and
//! charges it for each row, its count and its bytes, **before** the row is
//! built. Only [`rows::Rows`] builds a row or a scope, and every one of its
//! methods charges first, so no row can be built uncharged. A charge past
//! the budget declines A ([`ExistenceUnread::Budget`]).

// A match over a syntax enum that skips the kinds it does not name is where
// a construct the walk never reads hides: every arm names its kinds, so a
// new one is a compile error until the walk reads it or declines it.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;

#[cfg(any(test, feature = "test-support"))]
use borzoi_assembly::existence::{ExistenceIndex, PickleLayer};
use borzoi_assembly::existence::{PickledEntityKind, PickledEntityRow};
use borzoi_cst::syntax::{
    AstNode, Attribute, AttributeList, ExceptionDefnDecl, Expr, ImplicitCtor, LongIdent,
    MemberDefn, ModuleDecl, ModuleOrNamespace, ModuleOrNamespaceKind, SyntaxKind, SyntaxNode,
    TupleTypeExtensionHead, TyparDecls, Type, TypeDefn, TypeDefnRepr, UnionCase,
};

use crate::def::id_text;
use crate::recovery::SyntaxRecovery;
use crate::resolve::{ProjectFile, SourceFile};

/// A producer project, as the caller evaluated it for the dependant that
/// references it.
#[derive(Debug, Clone, Copy)]
pub struct Producer<'a> {
    /// A's Compile items in Compile order, each parsed under A's defines and
    /// language version.
    pub items: &'a [CompileItem<'a>],
    pub providers: ProviderReferences,
}

/// One item of A's Compile list.
#[derive(Debug, Clone, Copy)]
pub enum CompileItem<'a> {
    /// The item, parsed.
    Parsed(&'a ProjectFile),
    /// The evaluation lists the item but its text could not be read: what it
    /// declares is unknown, never nothing.
    Unreadable(&'a str),
}

/// Whether one of A's references may be a type provider: the caller's to
/// state. A type a provider supplies may be named like anything, an
/// FSharp.Core name opened over included, and a generative one makes FCS
/// read A from its DLL, never its source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProviderReferences {
    /// No reference is a type provider (none carries
    /// `[<TypeProviderAssembly>]`).
    None,
    /// One may be: no named abbreviation target is read.
    Possible,
}

/// The most rows, and the most bytes of rows, a walk may build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Budget {
    /// Rows: namespace rows and entity rows.
    pub rows: usize,
    /// The bytes the rows take: for each row, the row itself, and each name
    /// it holds (its namespace's and enclosers' segments, and its own,
    /// logical and compiled) as a `String` and its text.
    pub bytes: usize,
}

impl Budget {
    /// The budget a consumer reads a producer under: far past real code
    /// (`source_existence_census` reads the pinned corpus within a small
    /// fraction of it), and a few hundred MiB of rows at worst.
    pub const DEFAULT: Budget = Budget {
        rows: 1_000_000,
        bytes: 64 * 1024 * 1024,
    };
}

/// What a walk charged its [`Budget`], when it finished within it: every row
/// it built, and the bytes they hold, a row built twice (a duplicate
/// declaration) counted twice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Charged {
    pub rows: usize,
    pub bytes: usize,
}

/// A charge that did not fit: what had been charged before it, and what it
/// asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BudgetExceeded {
    pub charged_rows: usize,
    pub charged_bytes: usize,
    pub asked_rows: usize,
    pub asked_bytes: usize,
}

/// Why A's entity surface is not read.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExistenceUnread {
    /// A Compile item could not be read.
    UnreadableItem(String),
    /// The parser recovered from the Compile item at this index, or its
    /// errors were not kept.
    Recovered(usize),
    /// The Compile item at this index holds a form the walk declines.
    Declined(usize, Form),
    /// A node of this leaf, in the Compile item at this index, that no
    /// [`Form`] names: a shape outside every form, or a child no classifier
    /// accounts for.
    Unreadable(usize, Leaf),
    /// A named abbreviation target in the Compile item at this index, while
    /// a reference may be a type provider ([`ProviderReferences::Possible`]).
    TypeProvider(usize),
    /// The rows would not fit the [`Budget`].
    Budget(BudgetExceeded),
}

/// A syntax node the walk interprets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Leaf {
    /// A Compile item: an implementation or a signature file.
    File,
    /// A file's `namespace` or `module` header, or its absence.
    FileHeader,
    /// A long identifier the walk reads a name from.
    Name,
    /// `module M = …` in a declaration list.
    NestedModule,
    /// A type definition's head.
    TypeDefinition,
    /// `exception E …`.
    Exception,
    /// An abbreviation's target type.
    AbbreviationTarget,
    /// An attribute list.
    Attribute,
    /// A `#` directive.
    HashDirective,
}

/// Whether a producer holding a form is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The walk reads it, and FCS's facts for it are graded.
    Read,
    /// The walk declines the producer.
    Declined,
}

/// Declare [`Form`], [`Form::ALL`] and each form's leaf, verdict and witness
/// together, so that a form cannot exist without all four.
macro_rules! forms {
    ($($(#[doc = $doc:literal])* $name:ident: $leaf:ident, $verdict:ident, $witness:literal;)*) => {
        /// Every shape a [`Leaf`] is classified into: the closed list of what
        /// the walk reads.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Form {
            $($(#[doc = $doc])* $name,)*
        }

        impl Form {
            /// Every form, in declaration order.
            pub const ALL: &'static [Form] = &[$(Form::$name,)*];

            /// The leaf the form is a shape of.
            pub fn leaf(self) -> Leaf {
                match self {
                    $(Form::$name => Leaf::$leaf,)*
                }
            }

            /// Whether a producer holding the form is read.
            pub fn verdict(self) -> Verdict {
                match self {
                    $(Form::$name => Verdict::$verdict,)*
                }
            }

            /// A producer whose walk classifies the form: the domain grid's
            /// cell for it. A witness of `SignatureFile` is a signature and
            /// its implementation, separated by a line holding `//--`; any
            /// other is one implementation file.
            pub fn witness(self) -> &'static str {
                match self {
                    $(Form::$name => $witness,)*
                }
            }
        }
    };
}

forms! {
    /// An implementation file.
    ImplementationFile: File, Read, "module D\nlet x = 1\n";
    /// A signature file.
    SignatureFile: File, Declined, "module D\nval x: int\n//--\nmodule D\nlet x = 1\n";
    /// `namespace global`.
    GlobalNamespace: FileHeader, Read, "namespace global\ntype T = int\n";
    /// `namespace A.B`.
    Namespace: FileHeader, Read, "namespace A.B\ntype T = int\n";
    /// `module A.M` at the top of a file.
    NamedModule: FileHeader, Read, "module A.M\ntype T = int\n";
    /// A file with no header: its implicit module, named from the file.
    AnonymousModule: FileHeader, Declined, "type T = int\nlet x = 1\n";
    /// A long identifier of plain identifiers.
    PlainName: Name, Read, "module A.B.C\nlet x = 1\n";
    /// A name holding the `global` keyword unquoted, which FCS spells
    /// `` `global` ``, backticks and all.
    GlobalName: Name, Declined, "module D\ntype global = { X: int }\n";
    /// `module M = …`.
    NestedModule: NestedModule, Read, "module Outer\nmodule Inner =\n    let x = 1\n";
    /// `module M = begin end`, a module with no declarations.
    EmptyNestedModule: NestedModule, Read, "module Outer\nmodule Inner = begin end\n";
    /// A module, nested or a header's, whose name ends in `Module`: FCS may
    /// add another `Module`, which canonical spelling does not strip.
    SuffixedModule: NestedModule, Declined, "module Outer\nmodule InnerModule =\n    let x = 1\n";
    /// `type T = …`, no type parameters.
    Type: TypeDefinition, Read, "module D\ntype T = { X: int }\n";
    /// `type T<'a> = …`.
    GenericType: TypeDefinition, Read, "module D\ntype T<'a> = { X: 'a }\n";
    /// `type T with …`: an augmentation, which declares no entity.
    Augmentation: TypeDefinition, Read, "module D\ntype R = { X: int }\ntype R with\n    member r.Y = 1\n";
    /// `type (int * int) with …`.
    TupleAugmentation: TypeDefinition, Declined, "module D\ntype (int * int) with\n    member x.M() = 1\n";
    /// `type T() with …`, which FCS may read as declaring `T`.
    ConstructorAugmentation: TypeDefinition, Declined, "module D\ntype T() with\n    member x.M() = 1\n";
    /// `type X.Y = …` or `type X.Y with …`.
    DottedType: TypeDefinition, Declined, "module D\ntype System.String with\n    member s.M() = 1\n";
    /// `exception E of …`.
    Exception: Exception, Read, "module D\nexception E of string\n";
    /// `exception F = E`.
    ExceptionAbbreviation: Exception, Read, "module D\nexception E of string\nexception F = E\n";
    /// `type A = int`: a name FSharp.Core declares in a namespace every file
    /// has open.
    FSharpCoreTarget: AbbreviationTarget, Read, "module D\ntype A = int\n";
    /// A tuple, function, array, variable or anonymous type.
    StructuralTarget: AbbreviationTarget, Read, "module D\ntype A = int * string\n";
    /// `type X = X`: a union unless `X` is a unit of measure.
    SelfNamedTarget: AbbreviationTarget, Declined, "module D\ntype X = X\n";
    /// `type A = B`, `B` one identifier: a union case when `B` names no type.
    SingleIdentTarget: AbbreviationTarget, Declined, "module D\ntype A = B\n";
    /// Any other named type (qualified, applied).
    NamedTarget: AbbreviationTarget, Declined, "module D\ntype A = System.Collections.Generic.List<int>\n";
    /// A type holding a static argument: a type provider's.
    StaticArgumentTarget: AbbreviationTarget, Declined, "module D\ntype A = Provider<\"x\">\n";
    /// An attribute list on a module, type or exception.
    EntityAttribute: Attribute, Declined, "module D\n[<AutoOpen>]\nmodule M =\n    let x = 1\n";
    /// An attribute list standing alone (`[<A>] do ()`), which FCS may read
    /// as the assembly's.
    StandaloneAttribute: Attribute, Declined, "module D\n[<System.Obsolete>]\ndo ()\n";
    /// An attribute with an explicit target (`[<assembly: A>]`, `[<type: A>]`).
    TargetedAttribute: Attribute, Declined, "module D\nlet [<return: System.Obsolete>] f () = 1\n";
    /// An untargeted attribute list on anything but an entity: a `let`, a
    /// member, a field, a case, a parameter.
    OtherAttribute: Attribute, Read, "module D\n[<System.Obsolete>]\nlet x = 1\n";
    /// A `#` directive.
    HashDirective: HashDirective, Declined, "module D\n#time \"on\"\nlet x = 1\n";
    /// A line directive (`# 3 "f.fs"`, `#line`), which the lexer keeps as
    /// trivia: it moves no entity, but FCS's reading of a producer holding
    /// one is not graded (the oracle refuses it), so the walk does not read
    /// it.
    LineDirective: HashDirective, Declined, "module D\n# 3 \"Other.fs\"\nlet x = 1\n";
}

/// What [`source_existence`] read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceExistence {
    Read(SourceSurface),
    Unread(ExistenceUnread),
}

/// A's entity surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSurface {
    /// The pickle's entity rows, namespaces included, sorted, each once: no
    /// IL layer (FCS reads a project from source with none) and no
    /// extension rows.
    pub entities: Vec<PickledEntityRow>,
    /// What building the rows charged the budget.
    pub charged: Charged,
}

impl SourceSurface {
    /// The rows as an existence index, for the entity questions alone: an
    /// empty IL layer, the entity rows, and no extension rows, though the
    /// producer may declare extensions. So an extension question asked of
    /// it would answer "none" where the walk never looked, and it stays
    /// private to the crate's test support (`test_support::surface_facts`).
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn entity_index(&self) -> ExistenceIndex {
        ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(self.entities.clone()),
            extensions: Vec::new(),
        }
    }
}

/// A's entity surface, read from its source under `budget`. See the module
/// docs.
pub fn source_existence(producer: Producer<'_>, budget: Budget) -> SourceExistence {
    read(producer, budget).0
}

/// [`source_existence`], with every [`Form`] the walk classified before it
/// finished or declined.
pub(crate) fn read(producer: Producer<'_>, budget: Budget) -> (SourceExistence, BTreeSet<Form>) {
    let mut forms = BTreeSet::new();
    let read = match walk_project(producer, budget, &mut forms) {
        Ok(surface) => SourceExistence::Read(surface),
        Err(why) => SourceExistence::Unread(why),
    };
    (read, forms)
}

fn walk_project(
    producer: Producer<'_>,
    budget: Budget,
    forms: &mut BTreeSet<Form>,
) -> Result<SourceSurface, ExistenceUnread> {
    // Every item first: an unreadable or recovered one declines A however
    // the others read.
    let mut files = Vec::with_capacity(producer.items.len());
    for (i, item) in producer.items.iter().enumerate() {
        match item {
            CompileItem::Parsed(pf) => {
                if !matches!(&pf.recovery, SyntaxRecovery::Reported(errors) if errors.is_empty()) {
                    return Err(ExistenceUnread::Recovered(i));
                }
                files.push(*pf);
            }
            CompileItem::Unreadable(path) => {
                return Err(ExistenceUnread::UnreadableItem((*path).to_owned()));
            }
        }
    }
    let mut rows = rows::Rows::new(budget);
    for (i, pf) in files.iter().enumerate() {
        let mut file = FileWalk {
            index: i,
            providers: producer.providers,
            rows: &mut rows,
            forms,
        };
        file.walk(pf)?;
    }
    Ok(rows.finish())
}

/// Whether every child of `node` is accounted for: a node `nodes` accepts, a
/// token whose kind `tokens` accepts, trivia, or a zero-width layout token
/// the lex filter inserted. A classifier calls this over the node it
/// classifies, naming exactly the children it read or knows cannot change
/// the surface, so a child it does not name declines.
fn consumed(
    node: &SyntaxNode,
    nodes: impl Fn(&SyntaxNode) -> bool,
    tokens: impl Fn(SyntaxKind) -> bool,
) -> bool {
    node.children_with_tokens().all(|el| match el.as_node() {
        Some(n) => nodes(n),
        None => el
            .as_token()
            .is_some_and(|t| t.kind().is_trivia() || t.text().is_empty() || tokens(t.kind())),
    })
}

/// A long identifier's names, when it is plain identifiers and dots, or
/// `None` for any other child (`global`, an operator, an active pattern's
/// name).
fn long_ident(li: &LongIdent) -> Option<Vec<String>> {
    if !consumed(
        li.syntax(),
        |_| false,
        |k| matches!(k, SyntaxKind::IDENT_TOK | SyntaxKind::DOT_TOK),
    ) {
        return None;
    }
    let names: Vec<String> = li.idents().map(|t| id_text(&t).into_owned()).collect();
    (!names.is_empty()).then_some(names)
}

/// Whether FCS may add a `Module` suffix to a module named `name` that
/// canonical spelling (which strips one) does not undo: its name already
/// ends in `Module`.
fn suffixable(name: &str) -> bool {
    name.ends_with("Module")
}

/// The type abbreviations and types FSharp.Core declares under a name with
/// no arity suffix in the namespaces every F# file has open
/// (`Microsoft.FSharp.Core`, `Microsoft.FSharp.Collections`,
/// `Microsoft.FSharp.Control`): an abbreviation's single-identifier target
/// spelled as one of these names a type in scope.
pub(crate) const FSHARP_CORE_TYPE_NAMES: &[&str] = &[
    "obj",
    "exn",
    "string",
    "char",
    "bool",
    "unit",
    "decimal",
    "float",
    "float32",
    "single",
    "double",
    "int",
    "uint",
    "int8",
    "uint8",
    "sbyte",
    "byte",
    "int16",
    "uint16",
    "int32",
    "uint32",
    "int64",
    "uint64",
    "nativeint",
    "unativeint",
    "bigint",
    "voidptr",
];

/// The rows and the scopes they sit in: the one place either is built, and
/// every method charges the [`Budget`] before it builds.
mod rows {
    use std::collections::BTreeSet;
    use std::rc::Rc;

    use borzoi_assembly::existence::{PickledEntityKind, PickledEntityRow};

    use super::{Budget, BudgetExceeded, Charged, SourceSurface};

    /// The enclosing modules of a scope, innermost last: shared between every
    /// scope beneath them, so entering a module copies no path.
    struct Encloser {
        name: String,
        parent: Option<Rc<Encloser>>,
    }

    /// What one name costs a row that holds it: its `String` and its text.
    pub(super) fn name_cost(name: &str) -> usize {
        std::mem::size_of::<String>().saturating_add(name.len())
    }

    /// What a row costs before its names: the row itself.
    pub(super) const ROW_COST: usize = std::mem::size_of::<PickledEntityRow>();

    /// The scope a declaration sits in: a namespace and its enclosing
    /// modules, and the cost of all their names, so a row's charge needs no
    /// walk of its path.
    #[derive(Clone)]
    pub(super) struct Scope {
        namespace: Rc<[String]>,
        enclosing: Option<Rc<Encloser>>,
        /// The [`name_cost`] of every namespace segment and encloser name.
        bytes: usize,
    }

    impl Scope {
        /// The enclosing modules' names, outermost first.
        fn enclosing(&self) -> Vec<String> {
            let mut names = Vec::new();
            let mut at = self.enclosing.as_deref();
            while let Some(e) = at {
                names.push(e.name.clone());
                at = e.parent.as_deref();
            }
            names.reverse();
            names
        }
    }

    /// The rows built so far, and what is left of the budget.
    pub(super) struct Rows {
        budget: Budget,
        charged: Charged,
        namespaces: BTreeSet<Vec<String>>,
        entities: Vec<PickledEntityRow>,
    }

    impl Rows {
        pub(super) fn new(budget: Budget) -> Self {
            Rows {
                budget,
                charged: Charged::default(),
                namespaces: BTreeSet::new(),
                entities: Vec::new(),
            }
        }

        /// Charge one row holding names of `names_cost`, or decline.
        fn charge(&mut self, names_cost: usize) -> Result<(), BudgetExceeded> {
            let bytes = ROW_COST.saturating_add(names_cost);
            let rows = self.charged.rows.checked_add(1);
            let total = self.charged.bytes.checked_add(bytes);
            match (rows, total) {
                (Some(rows), Some(total))
                    if rows <= self.budget.rows && total <= self.budget.bytes =>
                {
                    self.charged = Charged { rows, bytes: total };
                    Ok(())
                }
                _ => Err(BudgetExceeded {
                    charged_rows: self.charged.rows,
                    charged_bytes: self.charged.bytes,
                    asked_rows: 1,
                    asked_bytes: bytes,
                }),
            }
        }

        /// The root scope of namespace `ns` (empty for the global namespace),
        /// and a namespace row for each of its prefixes not already held,
        /// each charged before it is built.
        pub(super) fn namespace(&mut self, ns: &[String]) -> Result<Scope, BudgetExceeded> {
            let mut bytes = 0usize;
            for k in 1..=ns.len() {
                let name = name_cost(&ns[k - 1]);
                bytes = bytes.saturating_add(name);
                if self.namespaces.contains(&ns[..k]) {
                    continue;
                }
                // The row's namespace and its two names, logical and
                // compiled: the prefix, and its last segment once more.
                self.charge(bytes.saturating_add(name))?;
                self.namespaces.insert(ns[..k].to_vec());
            }
            // The scope's own copy of the path, the bytes the last row
            // charged.
            Ok(Scope {
                namespace: ns.into(),
                enclosing: None,
                bytes,
            })
        }

        /// An entity named `name` of `kind` in `scope`: its row, charged
        /// before it is built.
        pub(super) fn entity(
            &mut self,
            scope: &Scope,
            name: &str,
            kind: PickledEntityKind,
        ) -> Result<(), BudgetExceeded> {
            // The row's path and its two names, logical and compiled.
            self.charge(
                scope
                    .bytes
                    .saturating_add(name_cost(name).saturating_mul(2)),
            )?;
            self.entities.push(PickledEntityRow {
                namespace: scope.namespace.to_vec(),
                enclosing: scope.enclosing(),
                logical_name: name.to_owned(),
                compiled_name: name.to_owned(),
                kind,
                public: true,
                auto_open: false,
                extension: false,
            });
            Ok(())
        }

        /// A module named `name` in `scope`: its row, and the scope inside
        /// it, which shares the row's charge (one name more than `scope`'s).
        pub(super) fn module(
            &mut self,
            scope: &Scope,
            name: &str,
        ) -> Result<Scope, BudgetExceeded> {
            self.entity(scope, name, PickledEntityKind::Module)?;
            Ok(Scope {
                namespace: Rc::clone(&scope.namespace),
                enclosing: Some(Rc::new(Encloser {
                    name: name.to_owned(),
                    parent: scope.enclosing.clone(),
                })),
                bytes: scope.bytes.saturating_add(name_cost(name)),
            })
        }

        /// The rows, namespaces first, sorted and each once.
        pub(super) fn finish(self) -> SourceSurface {
            let mut entities: Vec<PickledEntityRow> = self
                .namespaces
                .into_iter()
                .map(|mut path| {
                    let name = path.pop().expect("a namespace path is not empty");
                    PickledEntityRow {
                        namespace: path,
                        enclosing: Vec::new(),
                        logical_name: name.clone(),
                        compiled_name: name,
                        kind: PickledEntityKind::Namespace,
                        public: true,
                        auto_open: false,
                        extension: false,
                    }
                })
                .collect();
            entities.extend(self.entities);
            entities.sort();
            entities.dedup();
            SourceSurface {
                entities,
                charged: self.charged,
            }
        }
    }
}

use rows::Scope;

struct FileWalk<'w> {
    index: usize,
    providers: ProviderReferences,
    rows: &'w mut rows::Rows,
    forms: &'w mut BTreeSet<Form>,
}

impl FileWalk<'_> {
    fn unreadable(&self, leaf: Leaf) -> ExistenceUnread {
        ExistenceUnread::Unreadable(self.index, leaf)
    }

    /// Record `form`, and decline if its verdict says so.
    fn form(&mut self, form: Form) -> Result<(), ExistenceUnread> {
        self.forms.insert(form);
        match form.verdict() {
            Verdict::Read => Ok(()),
            Verdict::Declined => Err(ExistenceUnread::Declined(self.index, form)),
        }
    }

    fn walk(&mut self, pf: &ProjectFile) -> Result<(), ExistenceUnread> {
        let file = match &pf.file {
            SourceFile::Impl(f) => {
                self.form(Form::ImplementationFile)?;
                f
            }
            SourceFile::Sig(_) => return self.form(Form::SignatureFile),
        };
        let root = file.syntax();
        // The attributes and directives anywhere in the file, before any
        // row: each is read or declines A, wherever it sits.
        if root
            .descendants_with_tokens()
            .any(|el| el.kind() == SyntaxKind::HASH_LINE)
        {
            self.form(Form::LineDirective)?;
        }
        for node in root.descendants() {
            if node.kind() == SyntaxKind::HASH_DIRECTIVE_DECL {
                self.form(Form::HashDirective)?;
            }
            if let Some(list) = AttributeList::cast(node.clone()) {
                self.attribute_list(&list)?;
            }
        }
        // Every child of the file is a module or namespace.
        if !consumed(root, |n| ModuleOrNamespace::can_cast(n.kind()), |_| false) {
            return Err(self.unreadable(Leaf::File));
        }
        for m in file.modules() {
            // The header: its keyword, access and `rec` tokens, its name and
            // its declarations. An attribute list on it is an entity's.
            if !consumed(
                m.syntax(),
                |n| LongIdent::can_cast(n.kind()) || ModuleDecl::can_cast(n.kind()),
                |k| {
                    matches!(
                        k,
                        SyntaxKind::MODULE_TOK
                            | SyntaxKind::NAMESPACE_TOK
                            | SyntaxKind::ACCESS_TOK
                            | SyntaxKind::REC_TOK
                            | SyntaxKind::GLOBAL_TOK
                            | SyntaxKind::SEMI_TOK
                            | SyntaxKind::SEMISEMI_TOK
                    )
                },
            ) {
                return Err(self.unreadable(Leaf::FileHeader));
            }
            let decls: Vec<ModuleDecl> = m.decls().collect();
            match m.kind() {
                ModuleOrNamespaceKind::GlobalNamespace => {
                    self.form(Form::GlobalNamespace)?;
                    let scope = self.rows.namespace(&[]).map_err(ExistenceUnread::Budget)?;
                    self.decls(scope, decls)?;
                }
                ModuleOrNamespaceKind::DeclaredNamespace => {
                    self.form(Form::Namespace)?;
                    let ns = self.name(m.long_id())?;
                    let scope = self.rows.namespace(&ns).map_err(ExistenceUnread::Budget)?;
                    self.decls(scope, decls)?;
                }
                ModuleOrNamespaceKind::NamedModule => {
                    self.form(Form::NamedModule)?;
                    let segments = self.name(m.long_id())?;
                    let (name, ns) = segments.split_last().expect("a name is not empty");
                    if suffixable(name) {
                        self.form(Form::SuffixedModule)?;
                    }
                    let outer = self.rows.namespace(ns).map_err(ExistenceUnread::Budget)?;
                    let scope = self
                        .rows
                        .module(&outer, name)
                        .map_err(ExistenceUnread::Budget)?;
                    self.decls(scope, decls)?;
                }
                ModuleOrNamespaceKind::Anon => return self.form(Form::AnonymousModule),
            }
        }
        Ok(())
    }

    /// A long identifier's names, its form recorded.
    fn name(&mut self, li: Option<LongIdent>) -> Result<Vec<String>, ExistenceUnread> {
        // The `global` keyword stands as an identifier token, spelled as
        // written; FCS's name for it is quoted.
        if li
            .as_ref()
            .is_some_and(|li| li.idents().any(|t| t.text() == "global"))
        {
            self.form(Form::GlobalName)?;
        }
        let names = li
            .as_ref()
            .and_then(long_ident)
            .ok_or_else(|| self.unreadable(Leaf::Name))?;
        self.form(Form::PlainName)?;
        Ok(names)
    }

    /// An attribute list anywhere in the file, by what carries it: declined
    /// on an entity (a module header, a nested module, a type, an exception
    /// or its case), standing alone, or with a target on any of its
    /// attributes; read on the carriers no entity fact depends on, named one
    /// by one; and unreadable on any other.
    fn attribute_list(&mut self, list: &AttributeList) -> Result<(), ExistenceUnread> {
        let Some(parent) = list.syntax().parent() else {
            return Err(self.unreadable(Leaf::Attribute));
        };
        // The list's brackets, separators and attributes, and each
        // attribute's target, name and argument: a child of either that no
        // classifier names is unreadable, before any verdict is read off
        // the attributes the accessors return.
        let readable = consumed(
            list.syntax(),
            |n| Attribute::can_cast(n.kind()),
            |k| {
                matches!(
                    k,
                    SyntaxKind::LBRACK_LESS_TOK
                        | SyntaxKind::GREATER_RBRACK_TOK
                        | SyntaxKind::SEMI_TOK
                )
            },
        ) && list.attributes().all(|a| {
            consumed(
                a.syntax(),
                |n| {
                    n.kind() == SyntaxKind::ATTRIBUTE_TARGET
                        || LongIdent::can_cast(n.kind())
                        || Expr::can_cast(n.kind())
                },
                |_| false,
            )
        });
        if !readable {
            return Err(self.unreadable(Leaf::Attribute));
        }
        let exception_case = parent.kind() == SyntaxKind::UNION_CASE
            && parent
                .parent()
                .is_some_and(|g| g.kind() == SyntaxKind::EXCEPTION_DEFN);
        let entity = matches!(
            parent.kind(),
            SyntaxKind::MODULE_OR_NAMESPACE
                | SyntaxKind::NESTED_MODULE_DECL
                | SyntaxKind::TYPE_DEFN
                | SyntaxKind::EXCEPTION_DEFN
        );
        let other = matches!(
            parent.kind(),
            SyntaxKind::LET_DECL
                | SyntaxKind::BINDING
                | SyntaxKind::MEMBER_DEFN
                | SyntaxKind::MEMBER_LET_BINDINGS
                | SyntaxKind::GET_SET_ACCESSOR
                | SyntaxKind::VAL_FIELD
                | SyntaxKind::IMPLICIT_CTOR
                | SyntaxKind::RECORD_FIELD_DECL
                | SyntaxKind::UNION_CASE
                | SyntaxKind::ENUM_CASE
                | SyntaxKind::ATTRIB_PAT
                | SyntaxKind::TYPAR_DECL
                | SyntaxKind::EXTERN_DECL
        );
        if entity || exception_case {
            self.form(Form::EntityAttribute)
        } else if parent.kind() == SyntaxKind::ATTRIBUTES_DECL {
            self.form(Form::StandaloneAttribute)
        } else if !other {
            Err(self.unreadable(Leaf::Attribute))
        } else if list.attributes().any(|a| a.target().is_some()) {
            self.form(Form::TargetedAttribute)
        } else {
            self.form(Form::OtherAttribute)
        }
    }

    /// The declaration lists of `scope` and of every module in it, by a
    /// stack of the modules still to read rather than by recursion, so the
    /// walk's stack does not grow with the nesting.
    fn decls(&mut self, scope: Scope, decls: Vec<ModuleDecl>) -> Result<(), ExistenceUnread> {
        let mut pending = vec![(scope, decls)];
        while let Some((scope, decls)) = pending.pop() {
            for d in decls {
                match d {
                    ModuleDecl::NestedModule(m) => {
                        if !consumed(
                            m.syntax(),
                            |n| LongIdent::can_cast(n.kind()) || ModuleDecl::can_cast(n.kind()),
                            |k| {
                                matches!(
                                    k,
                                    SyntaxKind::MODULE_TOK
                                        | SyntaxKind::ACCESS_TOK
                                        | SyntaxKind::REC_TOK
                                        | SyntaxKind::EQUALS_TOK
                                        | SyntaxKind::BEGIN_TOK
                                        | SyntaxKind::END_TOK
                                        | SyntaxKind::SEMI_TOK
                                        | SyntaxKind::SEMISEMI_TOK
                                )
                            },
                        ) {
                            return Err(self.unreadable(Leaf::NestedModule));
                        }
                        let names = self.name(m.long_id())?;
                        let [name] = names.as_slice() else {
                            return Err(self.unreadable(Leaf::NestedModule));
                        };
                        if suffixable(name) {
                            self.form(Form::SuffixedModule)?;
                        }
                        let inner: Vec<ModuleDecl> = m.decls().collect();
                        self.form(if inner.is_empty() {
                            Form::EmptyNestedModule
                        } else {
                            Form::NestedModule
                        })?;
                        let inside = self
                            .rows
                            .module(&scope, name)
                            .map_err(ExistenceUnread::Budget)?;
                        pending.push((inside, inner));
                    }
                    ModuleDecl::Types(t) => {
                        // A group is its definitions, nothing else.
                        if !consumed(t.syntax(), |n| TypeDefn::can_cast(n.kind()), |_| false) {
                            return Err(self.unreadable(Leaf::TypeDefinition));
                        }
                        for defn in t.defns() {
                            self.type_defn(&scope, &defn)?;
                        }
                    }
                    ModuleDecl::Exception(e) => self.exception(&scope, &e)?,
                    // Read where they stand (attributes, directives), or
                    // declaring no entity.
                    ModuleDecl::Let(_)
                    | ModuleDecl::Extern(_)
                    | ModuleDecl::Expr(_)
                    | ModuleDecl::Open(_)
                    | ModuleDecl::ModuleAbbrev(_)
                    | ModuleDecl::Attributes(_)
                    | ModuleDecl::HashDirective(_) => {}
                }
            }
        }
        Ok(())
    }

    fn type_defn(&mut self, scope: &Scope, defn: &TypeDefn) -> Result<(), ExistenceUnread> {
        // The head's keyword, access, name, type parameters, constraints and
        // primary constructor; the representation and members (read only for
        // an abbreviation's target), and `with … end`. An attribute list is
        // an entity's, declined where it was met.
        if !consumed(
            defn.syntax(),
            |n| {
                let k = n.kind();
                LongIdent::can_cast(k)
                    || TyparDecls::can_cast(k)
                    || k == SyntaxKind::TYPAR_CONSTRAINTS
                    || ImplicitCtor::can_cast(k)
                    || TupleTypeExtensionHead::can_cast(k)
                    || TypeDefnRepr::can_cast(k)
                    || MemberDefn::can_cast(k)
            },
            |k| {
                matches!(
                    k,
                    SyntaxKind::TYPE_TOK
                        | SyntaxKind::AND_TOK
                        | SyntaxKind::ACCESS_TOK
                        | SyntaxKind::EQUALS_TOK
                        | SyntaxKind::WITH_TOK
                        | SyntaxKind::END_TOK
                )
            },
        ) {
            return Err(self.unreadable(Leaf::TypeDefinition));
        }
        if defn.tuple_type_head().is_some() {
            return self.form(Form::TupleAugmentation);
        }
        let names = self.name(defn.long_id())?;
        let [name] = names.as_slice() else {
            return self.form(Form::DottedType);
        };
        let augmentation =
            matches!(defn.repr(), Some(TypeDefnRepr::ObjectModel(om)) if om.is_augmentation());
        if augmentation {
            if defn.implicit_ctor().is_some() {
                return self.form(Form::ConstructorAugmentation);
            }
            return self.form(Form::Augmentation);
        }
        let generic = defn
            .typar_decls()
            .is_some_and(|d| d.typars().next().is_some());
        self.form(if generic {
            Form::GenericType
        } else {
            Form::Type
        })?;
        let kind = match defn.repr() {
            Some(TypeDefnRepr::Abbrev(a)) => match a.ty() {
                Some(target) => {
                    self.abbreviation_target(&target, name, generic)?;
                    PickledEntityKind::Abbreviation
                }
                None => return Err(self.unreadable(Leaf::AbbreviationTarget)),
            },
            Some(
                TypeDefnRepr::Record(_)
                | TypeDefnRepr::Union(_)
                | TypeDefnRepr::Enum(_)
                | TypeDefnRepr::ObjectModel(_)
                | TypeDefnRepr::Delegate(_),
            ) => PickledEntityKind::Type,
            // Inline IL is FSharp.Core's alone, and an implementation file's
            // type always has a representation.
            Some(TypeDefnRepr::InlineIl(_)) | None => {
                return Err(self.unreadable(Leaf::TypeDefinition));
            }
        };
        self.rows
            .entity(scope, name, kind)
            .map_err(ExistenceUnread::Budget)
    }

    /// Read `type name = target`: an abbreviation when the target is an
    /// FSharp.Core name every file has open or a structural type, and
    /// declined otherwise (a single identifier may be a union case, any
    /// other named type a provider's).
    fn abbreviation_target(
        &mut self,
        target: &Type,
        name: &str,
        generic: bool,
    ) -> Result<(), ExistenceUnread> {
        let form = target_form(target, name, generic);
        self.form(form)?;
        if form == Form::FSharpCoreTarget && self.providers == ProviderReferences::Possible {
            return Err(ExistenceUnread::TypeProvider(self.index));
        }
        Ok(())
    }

    /// `exception E …`.
    fn exception(&mut self, scope: &Scope, e: &ExceptionDefnDecl) -> Result<(), ExistenceUnread> {
        if !consumed(
            e.syntax(),
            |n| {
                let k = n.kind();
                UnionCase::can_cast(k) || LongIdent::can_cast(k) || MemberDefn::can_cast(k)
            },
            |k| {
                matches!(
                    k,
                    SyntaxKind::EXCEPTION_TOK
                        | SyntaxKind::ACCESS_TOK
                        | SyntaxKind::EQUALS_TOK
                        | SyntaxKind::WITH_TOK
                        | SyntaxKind::END_TOK
                )
            },
        ) {
            return Err(self.unreadable(Leaf::Exception));
        }
        let Some(name) = e.union_case().and_then(|c| c.ident()) else {
            return Err(self.unreadable(Leaf::Exception));
        };
        let name = id_text(&name).into_owned();
        self.form(if e.abbrev_path().is_some() {
            Form::ExceptionAbbreviation
        } else {
            Form::Exception
        })?;
        self.rows
            .entity(scope, &name, PickledEntityKind::Exception)
            .map_err(ExistenceUnread::Budget)
    }
}

/// An abbreviation target's form (`name` the abbreviation's own, `generic`
/// whether it has type parameters).
fn target_form(ty: &Type, name: &str, generic: bool) -> Form {
    // One scan of the whole target, then its parentheses peeled.
    let static_argument = ty.syntax().descendants().any(|n| {
        matches!(
            n.kind(),
            SyntaxKind::STATIC_CONST_TYPE
                | SyntaxKind::STATIC_CONST_EXPR_TYPE
                | SyntaxKind::STATIC_CONST_NAMED_TYPE
                | SyntaxKind::STATIC_CONST_NULL_TYPE
        )
    });
    if static_argument {
        return Form::StaticArgumentTarget;
    }
    let mut ty = ty.clone();
    while let Type::Paren(p) = &ty {
        // The parentheses and the one type inside them, nothing else.
        if !consumed(
            p.syntax(),
            |n| Type::can_cast(n.kind()),
            |k| matches!(k, SyntaxKind::LPAREN_TOK | SyntaxKind::RPAREN_TOK),
        ) {
            return Form::NamedTarget;
        }
        match p.inner() {
            Some(inner) => ty = inner,
            None => return Form::NamedTarget,
        }
    }
    match &ty {
        Type::Paren(_) => unreachable!("every parenthesis is peeled"),
        Type::LongIdent(t) => match t.long_ident().as_ref().and_then(long_ident).as_deref() {
            Some([single]) if single == name && !generic => Form::SelfNamedTarget,
            Some([single]) if FSHARP_CORE_TYPE_NAMES.contains(&single.as_str()) => {
                Form::FSharpCoreTarget
            }
            Some([_]) => Form::SingleIdentTarget,
            Some(_) | None => Form::NamedTarget,
        },
        Type::Tuple(_)
        | Type::Fun(_)
        | Type::Array(_)
        | Type::Var(_)
        | Type::Anon(_)
        | Type::AnonRecd(_) => Form::StructuralTarget,
        Type::App(_)
        | Type::LongIdentApp(_)
        | Type::Hash(_)
        | Type::WithNull(_)
        | Type::Constrained(_)
        | Type::Intersection(_)
        | Type::MeasurePower(_)
        | Type::StaticConst(_)
        | Type::StaticConstExpr(_)
        | Type::StaticConstNamed(_)
        | Type::StaticConstNull(_)
        | Type::SignatureParameter(_) => Form::NamedTarget,
    }
}

#[cfg(test)]
mod tests;
