//! A referenced F# project's **existence surface**, read from its source
//! ([`source_existence`]): the rows its compiled pickle would hold, in the
//! currency of [`borzoi_assembly::existence`], so the extension gate's
//! existence questions read a project reference exactly as they read a DLL.
//!
//! The function is pure. Its input is a producer project A as the caller
//! evaluated it ([`Producer`]): A's Compile items, parsed under A's own
//! defines and language version, and what the caller knows of A's reference
//! environment ([`MarkerRoutes`]). Its output ([`SourceExistence`]) is either
//! the rows, or `Unread` with the reason A's surface cannot be known.
//!
//! # The claim
//!
//! [`SourceSurface::approximations`] names every place the walk had to
//! over-approximate. With none named, [`SourceSurface::index`]'s pickle and
//! extension rows, and [`SourceSurface::assembly_auto_opens`], are exactly
//! those of the CCU FCS builds for A (its in-memory signature, which a
//! dependant reads, and the pickle of the DLL FCS compiles from the same
//! arguments). With some named, every row FCS has is one of ours: the walk
//! emits every reading it cannot rule out, so the rows are a multiset
//! superset. `Unread` claims nothing. `source_existence_diff` holds both.
//!
//! # Attributes
//!
//! Whether an attribute is `[<AutoOpen>]`, `[<Extension>]`, `[<Measure>]`,
//! `[<CompiledName>]`, `[<CompilationRepresentation>]` or
//! `[<TypeProviderAssembly>]` depends on what its name resolves to, and A's
//! references can route any name to any of them (an abbreviation) or away
//! from them (a shadow). The walk does not resolve: the caller states what
//! each written attribute name denotes ([`MarkerRoutes::Certified`]), or
//! nothing at all ([`MarkerRoutes::Unknown`]), in which case every attribute
//! may denote every marker.
//!
//! # The input inventory
//!
//! Every channel through which A's source or evaluation decides its surface
//! is a [`Channel`], and what the walk does with it is
//! [`Channel::treatment`]. The unit test `the_inventory_is_what_the_walk_does`
//! runs one witness per channel and holds the walk to its treatment.

use std::collections::{BTreeMap, BTreeSet};

use borzoi_assembly::existence::{
    ExistenceIndex, ExtensionRow, IndexLayer, PickleLayer, PickledEntityKind, PickledEntityRow,
};
use borzoi_cst::syntax::{
    AstNode, Attribute, AttributeList, Expr, LongIdent, MemberDefn, ModuleDecl,
    ModuleOrNamespace, ModuleOrNamespaceKind, Pat, SigDecl, SyntaxKind, SyntaxNode, SyntaxToken,
    Type, TypeDefn, TypeDefnRepr,
};

use crate::def::id_text;
use crate::recovery::SyntaxRecovery;
use crate::resolve::extension_names::{
    MemberShape, MemberVal, active_pattern_name, member_shape, val_sig_name,
};
use crate::resolve::{ProjectFile, SourceFile, signature_partners};

/// A producer project, as the caller evaluated it for the dependant that
/// references it.
#[derive(Debug, Clone, Copy)]
pub enum Producer<'a> {
    /// A's Compile items in Compile order, each parsed under A's defines and
    /// language version at the producer TFM the dependant is paired with, and
    /// what A's reference environment routes its attribute names to.
    Evaluated {
        items: &'a [CompileItem<'a>],
        routes: &'a MarkerRoutes,
    },
    /// A's fold is refused (an untrusted Compile set, untrusted defines, an
    /// untrusted language version on a file whose parse it decides).
    FoldRefused(&'a str),
    /// The producer TFM the dependant is paired with is not the one A was
    /// evaluated at.
    UnservedTfm(&'a str),
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

/// An attribute a declaration's existence rows depend on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Marker {
    /// `Microsoft.FSharp.Core.AutoOpenAttribute`.
    AutoOpen,
    /// `System.Runtime.CompilerServices.ExtensionAttribute`.
    Extension,
    /// `Microsoft.FSharp.Core.MeasureAttribute`.
    Measure,
    /// `Microsoft.FSharp.Core.CompiledNameAttribute`.
    CompiledName,
    /// `Microsoft.FSharp.Core.CompilationRepresentationAttribute`.
    CompilationRepresentation,
    /// `Microsoft.FSharp.Core.CompilerServices.TypeProviderAssemblyAttribute`.
    TypeProviderAssembly,
}

impl Marker {
    /// Every marker.
    pub const ALL: [Marker; 6] = [
        Marker::AutoOpen,
        Marker::Extension,
        Marker::Measure,
        Marker::CompiledName,
        Marker::CompilationRepresentation,
        Marker::TypeProviderAssembly,
    ];

    /// The marker's full name, its namespace's segments then its type name.
    pub fn full_name(self) -> &'static [&'static str] {
        match self {
            Marker::AutoOpen => &["Microsoft", "FSharp", "Core", "AutoOpenAttribute"],
            Marker::Extension => &["System", "Runtime", "CompilerServices", "ExtensionAttribute"],
            Marker::Measure => &["Microsoft", "FSharp", "Core", "MeasureAttribute"],
            Marker::CompiledName => &["Microsoft", "FSharp", "Core", "CompiledNameAttribute"],
            Marker::CompilationRepresentation => &[
                "Microsoft",
                "FSharp",
                "Core",
                "CompilationRepresentationAttribute",
            ],
            Marker::TypeProviderAssembly => &[
                "Microsoft",
                "FSharp",
                "Core",
                "CompilerServices",
                "TypeProviderAssemblyAttribute",
            ],
        }
    }
}

/// What the caller knows of the attribute names A writes: which markers each
/// denotes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MarkerRoutes {
    /// Nothing: any attribute may denote any marker, since a reference may
    /// declare an abbreviation of a marker under any name, or shadow a
    /// marker's own name. Sound, and the walk names every place it mattered
    /// ([`Approximation::UncertainAttribute`]).
    Unknown,
    /// For each written attribute name (its identifiers, de-quoted, as
    /// written, with or without the `Attribute` suffix exactly as written),
    /// the markers it denotes at **every** site in A that writes it, in A's
    /// environment (A's own declarations and its references). A name whose
    /// sites denote different things (opens can make one written name resolve
    /// differently in two files) must be omitted. An omitted name is read as
    /// under [`MarkerRoutes::Unknown`], so an incomplete certificate is sound
    /// and only loses exactness. An empty set certifies that the name denotes
    /// no marker.
    ///
    /// The certificate also covers the one other fact the walk takes from A's
    /// references: a generic type an augmentation extends (`type
    /// List<'T> with`) has its arity in its logical name (``List`1``), as
    /// every compiler writes it.
    Certified(BTreeMap<Vec<String>, BTreeSet<Marker>>),
}

/// Why A's existence surface cannot be read.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExistenceUnread {
    /// A Compile item could not be read.
    UnreadableItem(String),
    /// A's fold is refused.
    FoldRefused(String),
    /// The producer TFM is not the served one.
    UnservedTfm(String),
    /// The parser recovered from the Compile item at this index, or its
    /// errors were not kept (decision D8: the whole of A is unread).
    Recovered(usize),
    /// A `#r`, `#reference`, `#load`, `#I` or `#include` directive.
    HashReference(usize),
    /// A type provider may be in use (a static argument in an abbreviation's
    /// target), or A may be one (an assembly attribute that may be
    /// `[<TypeProviderAssembly>]`): FCS then reads A's DLL, not its source.
    TypeProvider(usize),
    /// An assembly-level attribute that may be `[<AutoOpen>]` has an argument
    /// the walk cannot read as a string.
    UnreadableAutoOpen(usize),
    /// An attribute that may be `[<CompiledName>]`, on an entity or a
    /// possible extension member, has an argument the walk cannot read as a
    /// string: the compiled name is unknown.
    UnreadableCompiledName(usize),
    /// A possible extension member, or a declaration, whose name the walk
    /// cannot read.
    UnnamedDeclaration(usize),
    /// A headerless file whose implicit module name the walk cannot spell.
    AnonymousModuleName(usize),
}

/// A place the walk emitted more than one reading, or a superset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Approximation {
    /// A `.fsi` and its implementation: the rows are the union of both
    /// (decision D7), where FCS's are the signature's.
    SignaturePair,
    /// An attribute's denotation is not certified, and the rows depend on it.
    UncertainAttribute,
    /// `type A = B` with `B` a single identifier: FCS reads a single-case
    /// union when `B` names no type in scope.
    AbbreviationOrUnion,
    /// An augmentation that may be intrinsic or optional.
    AugmentationKind,
    /// A `[<CompilationRepresentation>]` argument the walk cannot read.
    CompilationRepresentationArgument,
    /// An `[<Extension>]` binding whose pattern is not a single name.
    BindingPattern,
    /// A declaration FCS rejects in its position, read as written.
    RejectedShape,
}

/// What [`source_existence`] read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceExistence {
    Read(SourceSurface),
    Unread(ExistenceUnread),
}

/// A's existence surface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSurface {
    /// An empty `il` layer (FCS reads a project from source with no IL), the
    /// pickle rows, and the pickle's extension rows.
    pub index: ExistenceIndex,
    /// The `[<assembly: AutoOpen("…")>]` paths, in source order, with
    /// repeats: FCS's `GetAutoOpenAttributes`.
    pub assembly_auto_opens: Vec<String>,
    /// Where the rows over-approximate.
    pub approximations: BTreeSet<Approximation>,
}

impl SourceExistence {
    /// The extension gate's input for A.
    pub fn existence_input(&self) -> crate::ExistenceInput {
        match self {
            SourceExistence::Read(s) => crate::ExistenceInput::Read(s.index.clone()),
            SourceExistence::Unread(_) => crate::ExistenceInput::Unread,
        }
    }
}

/// Declares [`Channel`] and [`Channel::ALL`] from one list, so a channel
/// cannot be added to the one without the other.
macro_rules! channels {
    ($($(#[doc = $doc:literal])* $name:ident,)*) => {
        /// One row of the input inventory: a channel through which A's
        /// source, or A's evaluation, can decide A's existence surface.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Channel {
            $($(#[doc = $doc])* $name,)*
        }

        impl Channel {
            /// Every channel, in declaration order.
            pub const ALL: &'static [Channel] = &[$(Channel::$name,)*];
        }
    };
}

channels! {
    /// A Compile item the evaluation lists whose text cannot be read.
    UnreadableItem,
    /// A's fold is refused.
    FoldRefused,
    /// The producer TFM is not the served one.
    UnservedTfm,
    /// A's `DefineConstants`: the caller parses A under A's, not B's.
    Defines,
    /// A's language version: the caller parses A under it.
    LanguageVersion,
    /// Compile items a target adds at execution, and the SDK's generated
    /// `AssemblyInfo.fs`: the caller's Compile set must hold them.
    GeneratedItems,
    /// A file the parser recovered from.
    Recovered,
    /// `#r`, `#load`, `#I` and their kin.
    HashReference,
    /// A `.fsi` and its implementation.
    SignaturePair,
    /// A file with no header: its implicit module, named from the file.
    HeaderlessFile,
    /// A headerless file whose implicit module's name the walk cannot spell.
    AnonymousModuleName,
    /// `namespace`, `namespace rec`, `namespace global`, repeated fragments.
    Namespace,
    /// `module` headers and nested modules, `rec` or not.
    Module,
    /// `module X = Y`, which declares no entity.
    ModuleAbbreviation,
    /// The `Module` suffix a module takes beside a type of its name, or from
    /// `[<CompilationRepresentation(ModuleSuffix)>]`.
    ModuleSuffix,
    /// A `[<CompilationRepresentation>]` argument the walk cannot read.
    CompilationRepresentationArgument,
    /// Class, struct, interface, record, union, enum, delegate.
    TypeDefinition,
    /// A generic type's arity suffix, which units of measure do not count.
    GenericArity,
    /// `type A = T`.
    Abbreviation,
    /// `type A = B` with `B` one identifier that may be a union case.
    AbbreviationOrUnion,
    /// `[<Measure>] type m`.
    Measure,
    /// `exception E`.
    Exception,
    /// Accessibility, combined with the enclosing entities'.
    Accessibility,
    /// A static argument in an abbreviation's target (a type provider).
    TypeProviderUse,
    /// `[<AutoOpen>]` on an entity.
    AutoOpenAttribute,
    /// `[<Extension>]` on an entity or a member.
    ExtensionAttribute,
    /// `[<CompiledName("…")>]` on a type (modules and exceptions ignore it).
    CompiledNameAttribute,
    /// An attribute that may be `[<CompiledName>]` with an argument the walk
    /// cannot read.
    UnreadableCompiledName,
    /// `[<assembly: AutoOpen("…")>]`.
    AssemblyAutoOpen,
    /// An assembly attribute that may be `[<AutoOpen>]` with an argument the
    /// walk cannot read.
    AssemblyAutoOpenUnreadable,
    /// An assembly attribute that may be `[<TypeProviderAssembly>]`.
    TypeProviderAssembly,
    /// An attribute name the certificate does not cover.
    UncertifiedAttribute,
    /// A member of an optional augmentation (`type T with` of a type the
    /// list does not declare).
    OptionalExtensionMember,
    /// An augmentation of a class-like type of the same list: intrinsic.
    IntrinsicAugmentation,
    /// An augmentation whose kind the walk cannot decide.
    AugmentationKind,
    /// A member under `[<Extension>]`, C# style.
    CSharpExtensionMember,
    /// A module `let`, `extern` or signature `val` under `[<Extension>]`.
    ExtensionBinding,
    /// An `[<Extension>]` binding whose pattern is not one name.
    BindingPattern,
    /// The `[<Extension>]` FCS adds to a type or module from its members.
    ImpliedExtensionAttribute,
    /// A member or declaration the walk cannot name.
    UnnamedDeclaration,
    /// A member FCS rejects in an augmentation.
    RejectedShape,
}

impl Channel {
    /// What the walk does with this channel: the inventory.
    pub fn treatment(self) -> Treatment {
        use Approximation as A;
        match self {
            Channel::UnreadableItem
            | Channel::FoldRefused
            | Channel::UnservedTfm
            | Channel::Recovered
            | Channel::HashReference
            | Channel::AnonymousModuleName
            | Channel::TypeProviderUse
            | Channel::UnreadableCompiledName
            | Channel::AssemblyAutoOpenUnreadable
            | Channel::TypeProviderAssembly
            | Channel::UnnamedDeclaration => Treatment::Declined,
            Channel::Defines | Channel::LanguageVersion | Channel::GeneratedItems => {
                Treatment::Caller
            }
            Channel::SignaturePair => Treatment::Approximated(A::SignaturePair),
            Channel::CompilationRepresentationArgument => {
                Treatment::Approximated(A::CompilationRepresentationArgument)
            }
            Channel::AbbreviationOrUnion => Treatment::Approximated(A::AbbreviationOrUnion),
            Channel::UncertifiedAttribute => Treatment::Approximated(A::UncertainAttribute),
            Channel::AugmentationKind => Treatment::Approximated(A::AugmentationKind),
            Channel::BindingPattern => Treatment::Approximated(A::BindingPattern),
            Channel::RejectedShape => Treatment::Approximated(A::RejectedShape),
            Channel::HeaderlessFile
            | Channel::Namespace
            | Channel::Module
            | Channel::ModuleAbbreviation
            | Channel::ModuleSuffix
            | Channel::TypeDefinition
            | Channel::GenericArity
            | Channel::Abbreviation
            | Channel::Measure
            | Channel::Exception
            | Channel::Accessibility
            | Channel::AutoOpenAttribute
            | Channel::ExtensionAttribute
            | Channel::CompiledNameAttribute
            | Channel::AssemblyAutoOpen
            | Channel::OptionalExtensionMember
            | Channel::IntrinsicAugmentation
            | Channel::CSharpExtensionMember
            | Channel::ExtensionBinding
            | Channel::ImpliedExtensionAttribute => Treatment::Modelled,
        }
    }
}

/// What the walk does with a channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Treatment {
    /// Read exactly.
    Modelled,
    /// Read, with the named over-approximation.
    Approximated(Approximation),
    /// A is unread.
    Declined,
    /// The caller's: the input carries it, already applied.
    Caller,
}

/// A's existence surface, read from its source. See the module docs.
pub fn source_existence(producer: Producer<'_>) -> SourceExistence {
    match producer {
        Producer::FoldRefused(why) => {
            SourceExistence::Unread(ExistenceUnread::FoldRefused(why.to_owned()))
        }
        Producer::UnservedTfm(why) => {
            SourceExistence::Unread(ExistenceUnread::UnservedTfm(why.to_owned()))
        }
        Producer::Evaluated { items, routes } => match walk_project(items, routes) {
            Ok(surface) => SourceExistence::Read(surface),
            Err(why) => SourceExistence::Unread(why),
        },
    }
}

fn walk_project(
    items: &[CompileItem<'_>],
    routes: &MarkerRoutes,
) -> Result<SourceSurface, ExistenceUnread> {
    let mut files = Vec::with_capacity(items.len());
    for item in items {
        match item {
            CompileItem::Parsed(pf) => files.push((*pf).clone()),
            CompileItem::Unreadable(path) => {
                return Err(ExistenceUnread::UnreadableItem((*path).to_owned()));
            }
        }
    }
    let partners = signature_partners(&files);
    let mut out = Out::default();
    // Each file's rows, merged per signature pair as a multiset maximum: an
    // entity both sides declare is one entity, an overload declared on both
    // sides is still two.
    let mut pair_rows: BTreeMap<usize, (Vec<PickledEntityRow>, Vec<ExtensionRow>)> =
        BTreeMap::new();
    for (i, pf) in files.iter().enumerate() {
        if !matches!(&pf.recovery, SyntaxRecovery::Reported(errors) if errors.is_empty()) {
            return Err(ExistenceUnread::Recovered(i));
        }
        let root = pf.file.syntax();
        if root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::HASH_DIRECTIVE_DECL)
            .any(|d| brings_in_references(&d))
        {
            return Err(ExistenceUnread::HashReference(i));
        }
        let mut file = FileWalk {
            index: i,
            routes,
            out: Out::default(),
        };
        file.walk(pf)?;
        out.namespaces.extend(file.out.namespaces);
        out.auto_opens.extend(file.out.auto_opens);
        out.approximations.extend(file.out.approximations);
        match partners[i] {
            Some(p) => {
                out.approximations.insert(Approximation::SignaturePair);
                let key = i.min(p);
                let slot = pair_rows.entry(key).or_default();
                slot.0 = multiset_max(std::mem::take(&mut slot.0), file.out.entities);
                slot.1 = multiset_max(std::mem::take(&mut slot.1), file.out.extensions);
            }
            None => {
                out.entities.extend(file.out.entities);
                out.extensions.extend(file.out.extensions);
            }
        }
    }
    for (_, (entities, extensions)) in pair_rows {
        out.entities.extend(entities);
        out.extensions.extend(extensions);
    }
    let mut rows: Vec<PickledEntityRow> = out
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
    rows.extend(out.entities);
    rows.sort();
    let mut extensions = out.extensions;
    extensions.sort();
    Ok(SourceSurface {
        index: ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(rows),
            extensions,
        },
        assembly_auto_opens: out.auto_opens,
        approximations: out.approximations,
    })
}

/// The multiset whose count of each row is the larger of its counts in `a`
/// and `b`.
fn multiset_max<T: Ord + Clone>(a: Vec<T>, b: Vec<T>) -> Vec<T> {
    let count = |v: &[T]| {
        let mut m: BTreeMap<T, usize> = BTreeMap::new();
        for x in v {
            *m.entry(x.clone()).or_default() += 1;
        }
        m
    };
    let (mut ca, cb) = (count(&a), count(&b));
    for (k, n) in cb {
        let e = ca.entry(k).or_default();
        *e = (*e).max(n);
    }
    ca.into_iter()
        .flat_map(|(k, n)| std::iter::repeat_n(k, n))
        .collect()
}

/// Whether a hash directive brings in an assembly or a source file.
fn brings_in_references(directive: &SyntaxNode) -> bool {
    directive
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| t.kind() == SyntaxKind::IDENT_TOK)
        .is_some_and(|t| {
            matches!(
                t.text(),
                "r" | "reference" | "load" | "I" | "i" | "include"
            )
        })
}

#[derive(Default)]
struct Out {
    namespaces: BTreeSet<Vec<String>>,
    entities: Vec<PickledEntityRow>,
    extensions: Vec<ExtensionRow>,
    auto_opens: Vec<String>,
    approximations: BTreeSet<Approximation>,
}

/// Whether something holds: yes, no, or not known.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Maybe {
    No,
    Possibly,
    Yes,
}

impl Maybe {
    fn or(self, other: Maybe) -> Maybe {
        match (self, other) {
            (Maybe::Yes, _) | (_, Maybe::Yes) => Maybe::Yes,
            (Maybe::Possibly, _) | (_, Maybe::Possibly) => Maybe::Possibly,
            _ => Maybe::No,
        }
    }

    /// The readings this leaves open.
    fn readings(self) -> &'static [bool] {
        match self {
            Maybe::No => &[false],
            Maybe::Yes => &[true],
            Maybe::Possibly => &[false, true],
        }
    }
}

/// The written name of `attr`, de-quoted, or `None` for `[<>]`.
fn written_name(attr: &Attribute) -> Option<Vec<String>> {
    let li = attr.type_name()?;
    let segs: Vec<String> = li.idents().map(|t| id_text(&t).into_owned()).collect();
    (!segs.is_empty()).then_some(segs)
}

/// A string literal's value, for the literal forms whose value is their
/// text: a regular string with no escape, a verbatim string, and a
/// triple-quoted one. `None` for anything else.
fn string_literal(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Paren(p) => p.inner().as_ref().and_then(string_literal),
        Expr::Const(c) => {
            let tok = c.literal()?;
            let text = tok.text();
            match tok.kind() {
                SyntaxKind::STRING_LIT => {
                    let inner = text.strip_prefix('"')?.strip_suffix('"')?;
                    (!inner.contains('\\')).then(|| inner.to_owned())
                }
                SyntaxKind::VERBATIM_STRING_LIT => {
                    let inner = text.strip_prefix("@\"")?.strip_suffix('"')?;
                    Some(inner.replace("\"\"", "\""))
                }
                SyntaxKind::TRIPLE_STRING_LIT => {
                    let inner = text.strip_prefix("\"\"\"")?.strip_suffix("\"\"\"")?;
                    Some(inner.to_owned())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// What one attribute's argument says, for the markers that read it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Arg {
    /// No argument (`[<AutoOpen>]`).
    None,
    /// A string literal.
    Literal(String),
    /// Anything else.
    Other,
}

fn arg_of(attr: &Attribute) -> Arg {
    match attr.arg() {
        None => Arg::None,
        Some(Expr::Const(c)) if c.literal().is_some_and(|t| t.text() == "()") => Arg::None,
        Some(e) => match string_literal(&e) {
            Some(s) => Arg::Literal(s),
            None => Arg::Other,
        },
    }
}

/// What a set of attribute lists says about each marker.
struct Marks {
    markers: BTreeMap<Marker, Maybe>,
    /// The compiled names an attribute that may be `[<CompiledName>]` gives,
    /// and whether one must apply (the attribute is certainly the marker).
    compiled_names: Vec<String>,
    compiled_name_certain: bool,
    /// An attribute that may be `[<CompiledName>]` whose argument is no
    /// literal.
    compiled_name_unreadable: bool,
    /// What an attribute that may be `[<CompilationRepresentation>]` says of
    /// the module suffix.
    module_suffix: Maybe,
    /// Some denotation was uncertain and some marker possible because of it.
    uncertain: bool,
}

impl Marks {
    fn get(&self, m: Marker) -> Maybe {
        self.markers.get(&m).copied().unwrap_or(Maybe::No)
    }
}

impl MarkerRoutes {
    /// What the attribute written `name` may denote: `Some(set)` exactly,
    /// `None` when anything.
    fn denotes(&self, name: Option<&[String]>) -> Option<&BTreeSet<Marker>> {
        match (self, name) {
            (MarkerRoutes::Certified(map), Some(name)) => map.get(name),
            _ => None,
        }
    }

    fn marks<'l>(&self, lists: impl IntoIterator<Item = &'l AttributeList>) -> Marks {
        let mut marks = Marks {
            markers: BTreeMap::new(),
            compiled_names: Vec::new(),
            compiled_name_certain: false,
            compiled_name_unreadable: false,
            module_suffix: Maybe::No,
            uncertain: false,
        };
        for list in lists {
            for attr in list.attributes() {
                // An assembly- or module-targeted attribute marks nothing
                // here: the assembly's are read on their own.
                if attr
                    .target()
                    .is_some_and(|t| matches!(t.text(), "assembly" | "module"))
                {
                    continue;
                }
                let name = written_name(&attr);
                let denoted = self.denotes(name.as_deref());
                for m in Marker::ALL {
                    let maybe = match denoted {
                        Some(set) if set.contains(&m) => Maybe::Yes,
                        Some(_) => Maybe::No,
                        None => {
                            marks.uncertain = true;
                            Maybe::Possibly
                        }
                    };
                    if maybe == Maybe::No {
                        continue;
                    }
                    let slot = marks.markers.entry(m).or_insert(Maybe::No);
                    *slot = slot.or(maybe);
                    match m {
                        Marker::CompiledName => match arg_of(&attr) {
                            Arg::Literal(s) => {
                                marks.compiled_names.push(s);
                                marks.compiled_name_certain |= maybe == Maybe::Yes;
                            }
                            // `[<CompiledName>]` with no argument does not
                            // compile; any other attribute with none names
                            // nothing.
                            Arg::None => {}
                            Arg::Other => marks.compiled_name_unreadable = true,
                        },
                        Marker::CompilationRepresentation => {
                            let suffix = module_suffix_arg(&attr);
                            marks.module_suffix = marks.module_suffix.or(match (maybe, suffix)
                            {
                                (_, Maybe::No) => Maybe::No,
                                (Maybe::Yes, s) => s,
                                _ => Maybe::Possibly,
                            });
                        }
                        _ => {}
                    }
                }
            }
        }
        marks
    }
}

/// Whether a `[<CompilationRepresentation(…)>]` argument includes
/// `ModuleSuffix`: `Yes` for a path ending `ModuleSuffix` (or an `|||` of
/// paths, one of which ends so), `No` for paths none of which does, and
/// `Possibly` for anything else.
fn module_suffix_arg(attr: &Attribute) -> Maybe {
    let Some(arg) = attr.arg() else {
        return Maybe::No;
    };
    let tokens: Vec<SyntaxToken> = arg
        .syntax()
        .descendants_with_tokens()
        .filter_map(|el| el.into_token())
        .filter(|t| !t.kind().is_trivia())
        .collect();
    let mut suffix = false;
    for (i, t) in tokens.iter().enumerate() {
        match t.kind() {
            SyntaxKind::IDENT_TOK if t.text() == "|||" => {}
            SyntaxKind::IDENT_TOK => {
                // The last segment of a dotted path names the flag.
                let last = tokens
                    .get(i + 1)
                    .is_none_or(|n| n.kind() != SyntaxKind::DOT_TOK);
                suffix |= last && id_text(t) == "ModuleSuffix";
            }
            SyntaxKind::DOT_TOK | SyntaxKind::LPAREN_TOK | SyntaxKind::RPAREN_TOK => {}
            _ if t.text() == "|||" => {}
            _ => return Maybe::Possibly,
        }
    }
    if suffix { Maybe::Yes } else { Maybe::No }
}

/// The scope a declaration sits in.
#[derive(Debug, Clone)]
struct Scope {
    namespace: Vec<String>,
    /// The enclosing modules' and types' logical names, outermost first.
    enclosing: Vec<String>,
    /// Whether every enclosing entity is public: FCS combines an entity's
    /// own accessibility with its parent's.
    public: bool,
}

impl Scope {
    /// Directly in namespace `namespace`.
    fn root(namespace: Vec<String>) -> Scope {
        Scope {
            namespace,
            enclosing: Vec::new(),
            public: true,
        }
    }

    /// Inside the entity `name` of this scope, whose own accessibility is
    /// public when `public`.
    fn inner(&self, name: &str, public: bool) -> Scope {
        let mut enclosing = self.enclosing.clone();
        enclosing.push(name.to_owned());
        Scope {
            namespace: self.namespace.clone(),
            enclosing,
            public: self.public && public,
        }
    }
}

/// One type definition's facts the module-suffix and augmentation rules
/// read.
#[derive(Debug, Clone)]
struct LocalType {
    /// The name as written (no arity).
    name: String,
    arity: usize,
    /// Its position in the declaration list.
    position: usize,
    kind: LocalKind,
}

/// What an augmentation of a local type needs to know of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalKind {
    /// A class, struct, record or union: augmenting it in its own
    /// declaration list is intrinsic.
    ClassLike,
    /// An interface, delegate, enum or abbreviation: augmenting it is
    /// optional.
    NotClassLike,
    /// The walk cannot tell.
    Unknown,
}

struct FileWalk<'r> {
    index: usize,
    routes: &'r MarkerRoutes,
    out: Out,
}

/// A declaration list being walked: impl decls or sig decls.
enum Decls {
    Impl(Vec<ModuleDecl>),
    Sig(Vec<SigDecl>),
}

impl FileWalk<'_> {
    fn walk(&mut self, pf: &ProjectFile) -> Result<(), ExistenceUnread> {
        let root = pf.file.syntax();
        self.assembly_attributes(root)?;
        let modules: Vec<ModuleOrNamespace> = match &pf.file {
            SourceFile::Impl(f) => f.modules().collect(),
            SourceFile::Sig(f) => f.modules().collect(),
        };
        let is_sig = matches!(pf.file, SourceFile::Sig(_));
        for m in modules {
            let decls = if is_sig {
                Decls::Sig(m.sig_decls().collect())
            } else {
                Decls::Impl(m.decls().collect())
            };
            match m.kind() {
                ModuleOrNamespaceKind::GlobalNamespace => {
                    self.decls(&Scope::root(Vec::new()), &decls, m.is_rec(), false, &[])?;
                }
                ModuleOrNamespaceKind::DeclaredNamespace => {
                    let ns = long_id_segments(m.long_id())
                        .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                    self.namespace(&ns);
                    self.decls(&Scope::root(ns), &decls, m.is_rec(), false, &[])?;
                }
                ModuleOrNamespaceKind::NamedModule | ModuleOrNamespaceKind::Anon => {
                    let (segments, attrs, header): (Vec<String>, Vec<AttributeList>, bool) =
                        if m.kind() == ModuleOrNamespaceKind::Anon {
                            let segs = pf
                                .qnof
                                .anonymous_module_segments()
                                .ok_or(ExistenceUnread::AnonymousModuleName(self.index))?;
                            (segs, Vec::new(), false)
                        } else {
                            (
                                long_id_segments(m.long_id())
                                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?,
                                m.attributes().collect(),
                                true,
                            )
                        };
                    let (name, ns) = segments.split_last().expect("segments are not empty");
                    self.namespace(ns);
                    let scope = Scope::root(ns.to_vec());
                    let public = !header || !header_access_restricts(m.syntax());
                    // A top-level module's name meets no type of its
                    // declaration list (its namespace's other files are
                    // other lists), so only an attribute adds the suffix.
                    self.module(
                        &scope,
                        name,
                        &attrs,
                        public,
                        Maybe::No,
                        &decls,
                        m.is_rec(),
                        &[],
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Record namespace `ns` and its prefixes.
    fn namespace(&mut self, ns: &[String]) {
        for k in 1..=ns.len() {
            self.out.namespaces.insert(ns[..k].to_vec());
        }
    }

    /// Every assembly-level attribute of the file: an `[<AutoOpen>]` path,
    /// or a reason A is unread.
    fn assembly_attributes(&mut self, root: &SyntaxNode) -> Result<(), ExistenceUnread> {
        for list in root.descendants().filter_map(AttributeList::cast) {
            for attr in list.attributes() {
                if !attr.target().is_some_and(|t| t.text() == "assembly") {
                    continue;
                }
                let name = written_name(&attr);
                let denoted = self.routes.denotes(name.as_deref());
                let may = |m: Marker| match denoted {
                    Some(set) if set.contains(&m) => Maybe::Yes,
                    Some(_) => Maybe::No,
                    None => Maybe::Possibly,
                };
                if may(Marker::TypeProviderAssembly) != Maybe::No {
                    return Err(ExistenceUnread::TypeProvider(self.index));
                }
                match (may(Marker::AutoOpen), arg_of(&attr)) {
                    (Maybe::No, _) | (_, Arg::None) => {}
                    (Maybe::Yes, Arg::Literal(path)) => self.out.auto_opens.push(path),
                    (Maybe::Possibly, Arg::Literal(path)) => {
                        self.out.auto_opens.push(path);
                        self.out
                            .approximations
                            .insert(Approximation::UncertainAttribute);
                    }
                    (_, Arg::Other) => return Err(ExistenceUnread::UnreadableAutoOpen(self.index)),
                }
            }
        }
        Ok(())
    }

    /// The type definitions of a declaration list, by position.
    fn local_types(&self, decls: &Decls) -> Vec<(LocalType, Maybe)> {
        let mut out = Vec::new();
        let push = |position: usize, defn: &TypeDefn, out: &mut Vec<(LocalType, Maybe)>| {
            if is_augmentation(defn) {
                return;
            }
            let Some(name) = defn
                .long_id()
                .and_then(|li| li.idents().last())
                .map(|t| id_text(&t).into_owned())
            else {
                return;
            };
            let typars: Vec<_> = defn
                .typar_decls()
                .map(|d| d.typars().collect())
                .unwrap_or_default();
            // Whether every type parameter is a measure (vacuously, none):
            // FCS's `TyparsAllHaveMeasureDeclEarlyCheck`, which decides
            // whether the name meets a module of the same name.
            let mut all_measure = Maybe::Yes;
            for t in &typars {
                let lists: Vec<AttributeList> = t.attributes().collect();
                let m = self.routes.marks(&lists).get(Marker::Measure);
                all_measure = match (all_measure, m) {
                    (Maybe::No, _) | (_, Maybe::No) => Maybe::No,
                    (Maybe::Yes, Maybe::Yes) => Maybe::Yes,
                    _ => Maybe::Possibly,
                };
            }
            out.push((
                LocalType {
                    name,
                    arity: typars.len(),
                    position,
                    kind: local_kind(defn),
                },
                all_measure,
            ));
        };
        match decls {
            Decls::Impl(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    if let ModuleDecl::Types(t) = d {
                        for defn in t.defns() {
                            push(i, &defn, &mut out);
                        }
                    }
                }
            }
            Decls::Sig(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    if let SigDecl::Types(t) = d {
                        for defn in t.defns() {
                            push(i, &defn, &mut out);
                        }
                    }
                }
            }
        }
        out
    }

    /// Whether a module named `name` in `decls`' list meets a type of its
    /// name there (FCS's `typeNames`), so it takes the `Module` suffix.
    fn meets_type(locals: &[(LocalType, Maybe)], name: &str, is_sig: bool) -> Maybe {
        let mut meets = Maybe::No;
        for (t, all_measure) in locals {
            if t.name != name {
                continue;
            }
            // A signature counts a type only with no type parameters.
            let counted = if is_sig {
                if t.arity == 0 { Maybe::Yes } else { Maybe::No }
            } else {
                *all_measure
            };
            meets = meets.or(counted);
        }
        meets
    }

    /// The declaration list `decls` in `scope`, a module's when `in_module`
    /// (else a namespace's); `outer` names every type the enclosing lists
    /// declare before it.
    fn decls(
        &mut self,
        scope: &Scope,
        decls: &Decls,
        is_rec: bool,
        in_module: bool,
        outer: &[String],
    ) -> Result<(), ExistenceUnread> {
        let locals = self.local_types(decls);
        let is_sig = matches!(decls, Decls::Sig(_));
        // Every `open`'s position, which may move what a later augmentation's
        // name resolves to.
        let opens: Vec<usize> = match decls {
            Decls::Impl(ds) => ds
                .iter()
                .enumerate()
                .filter(|(_, d)| matches!(d, ModuleDecl::Open(_)))
                .map(|(i, _)| i)
                .collect(),
            Decls::Sig(ds) => ds
                .iter()
                .enumerate()
                .filter(|(_, d)| matches!(d, SigDecl::Open(_)))
                .map(|(i, _)| i)
                .collect(),
        };
        // A module's list FCS checks as one recursive group counts its
        // exceptions among the names a module's suffix meets
        // (`TypeNamesInMutRecDecls`); a namespace's list never does, `rec`
        // or not (`TypeNamesInNonMutRecDecls`).
        let exceptions: Vec<String> = match decls {
            Decls::Impl(ds) if is_rec && in_module => ds
                .iter()
                .filter_map(|d| match d {
                    ModuleDecl::Exception(e) => e.union_case().and_then(|c| c.ident()),
                    _ => None,
                })
                .map(|t| id_text(&t).into_owned())
                .collect(),
            Decls::Sig(ds) if is_rec && in_module => ds
                .iter()
                .filter_map(|d| match d {
                    SigDecl::Exception(e) => e.union_case().and_then(|c| c.ident()),
                    _ => None,
                })
                .map(|t| id_text(&t).into_owned())
                .collect(),
            _ => Vec::new(),
        };
        let ctx = ListCtx {
            locals: &locals,
            opens: &opens,
            is_rec,
            outer,
            exceptions: &exceptions,
        };
        match decls {
            Decls::Impl(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    self.impl_decl(scope, d, i, &ctx)?;
                }
            }
            Decls::Sig(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    self.sig_decl(scope, d, i, &ctx)?;
                }
            }
        }
        let _ = is_sig;
        Ok(())
    }

    fn impl_decl(
        &mut self,
        scope: &Scope,
        d: &ModuleDecl,
        position: usize,
        ctx: &ListCtx<'_>,
    ) -> Result<(), ExistenceUnread> {
        match d {
            ModuleDecl::NestedModule(m) => {
                let name = long_id_segments(m.long_id())
                    .and_then(|s| s.last().cloned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = m.attributes().collect();
                let meets = Self::meets_type(ctx.locals, &name, false)
                    .or(ctx.meets_exception(&name));
                let public = !header_access_restricts(m.syntax());
                self.module(
                    scope,
                    &name,
                    &attrs,
                    public,
                    meets,
                    &Decls::Impl(m.decls().collect()),
                    m.is_rec() || ctx.is_rec,
                    &ctx.visible_at(position),
                )
            }
            ModuleDecl::Types(t) => {
                let defns: Vec<TypeDefn> = t.defns().collect();
                // The first definition carries the group's leading attributes.
                for defn in &defns {
                    self.type_defn(scope, defn, position, ctx)?;
                }
                Ok(())
            }
            ModuleDecl::Exception(e) => {
                let name = e
                    .union_case()
                    .and_then(|c| c.ident())
                    .map(|t| id_text(&t).into_owned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = e.attributes().collect();
                let marks = self.routes.marks(&attrs);
                let public = !exception_access_restricts(e.syntax());
                let members: Vec<MemberDefn> = e.members().collect();
                let implied = self.members(&scope.inner(&name, public), &members, None)?;
                self.entity(
                    scope,
                    std::slice::from_ref(&name),
                    &[PickledEntityKind::Exception],
                    public,
                    &marks,
                    implied,
                    false,
                )
            }
            ModuleDecl::Let(l) => {
                let lists: Vec<AttributeList> = l.attributes().collect();
                for (k, b) in l.bindings().enumerate() {
                    let mut own: Vec<AttributeList> = b.attributes().collect();
                    if k == 0 {
                        own.extend(lists.iter().cloned());
                    }
                    self.binding_extension(scope, &own, b.pat())?;
                }
                Ok(())
            }
            ModuleDecl::Extern(x) => {
                let lists: Vec<AttributeList> = x.attributes().collect();
                let marks = self.routes.marks(&lists);
                if marks.get(Marker::Extension) == Maybe::No {
                    return Ok(());
                }
                let name = x
                    .name()
                    .and_then(|li| li.idents().last())
                    .map(|t| id_text(&t).into_owned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                self.csharp_row(scope, &name, &marks)
            }
            ModuleDecl::Expr(_)
            | ModuleDecl::Open(_)
            | ModuleDecl::ModuleAbbrev(_)
            | ModuleDecl::Attributes(_)
            | ModuleDecl::HashDirective(_) => Ok(()),
        }
    }

    fn sig_decl(
        &mut self,
        scope: &Scope,
        d: &SigDecl,
        position: usize,
        ctx: &ListCtx<'_>,
    ) -> Result<(), ExistenceUnread> {
        match d {
            SigDecl::NestedModule(m) => {
                let name = long_id_segments(m.long_id())
                    .and_then(|s| s.last().cloned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = m.attributes().collect();
                let meets = Self::meets_type(ctx.locals, &name, true)
                    .or(ctx.meets_exception(&name));
                let public = !header_access_restricts(m.syntax());
                self.module(
                    scope,
                    &name,
                    &attrs,
                    public,
                    meets,
                    &Decls::Sig(m.sig_decls().collect()),
                    m.is_rec() || ctx.is_rec,
                    &ctx.visible_at(position),
                )
            }
            SigDecl::Types(t) => {
                for defn in t.defns() {
                    self.type_defn(scope, &defn, position, ctx)?;
                }
                Ok(())
            }
            SigDecl::Exception(e) => {
                let name = e
                    .union_case()
                    .and_then(|c| c.ident())
                    .map(|t| id_text(&t).into_owned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = e.attributes().collect();
                let marks = self.routes.marks(&attrs);
                let public = !exception_access_restricts(e.syntax());
                self.entity(
                    scope,
                    std::slice::from_ref(&name),
                    &[PickledEntityKind::Exception],
                    public,
                    &marks,
                    Maybe::No,
                    false,
                )
            }
            SigDecl::Val(v) => {
                let lists: Vec<AttributeList> = v.attributes().collect();
                let marks = self.routes.marks(&lists);
                if marks.get(Marker::Extension) == Maybe::No {
                    return Ok(());
                }
                let name = v
                    .val_sig()
                    .and_then(|s| val_sig_name(&s))
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                self.csharp_row(scope, &name, &marks)
            }
            SigDecl::Open(_) | SigDecl::ModuleAbbrev(_) | SigDecl::HashDirective(_) => Ok(()),
        }
    }

    /// A module entity, and its contents.
    #[allow(clippy::too_many_arguments)]
    fn module(
        &mut self,
        scope: &Scope,
        name: &str,
        attrs: &[AttributeList],
        public: bool,
        meets_type: Maybe,
        decls: &Decls,
        is_rec: bool,
        outer: &[String],
    ) -> Result<(), ExistenceUnread> {
        let marks = self.routes.marks(attrs);
        if marks.uncertain && marks.module_suffix != Maybe::No {
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
        let suffix = meets_type.or(marks.module_suffix);
        if suffix == Maybe::Possibly && marks.module_suffix == Maybe::Possibly && !marks.uncertain {
            self.out
                .approximations
                .insert(Approximation::CompilationRepresentationArgument);
        }
        // FCS marks a module `[<Extension>]` when one of its own non-`rec`
        // `let`s (an `extern` among them) is, in a module that is not `rec`.
        let implied = if is_rec {
            Maybe::No
        } else {
            self.implied_by_lets(decls)
        };
        // The suffix is part of the module's logical name, and so of every
        // path under it: each reading walks the contents once.
        for &suffixed in suffix.readings() {
            let logical = if suffixed {
                format!("{name}Module")
            } else {
                name.to_owned()
            };
            self.decls(&scope.inner(&logical, public), decls, is_rec, true, outer)?;
            // `[<CompiledName>]` does not rename a module.
            self.entity(
                scope,
                &[logical.clone()],
                &[PickledEntityKind::Module],
                public,
                &marks,
                implied,
                false,
            )?;
        }
        Ok(())
    }

    /// Whether a non-`rec` `let` or an `extern` directly in `decls` may carry
    /// `[<Extension>]`.
    fn implied_by_lets(&self, decls: &Decls) -> Maybe {
        let Decls::Impl(ds) = decls else {
            return Maybe::No;
        };
        let mut implied = Maybe::No;
        for d in ds {
            let lists: Vec<AttributeList> = match d {
                ModuleDecl::Let(l) if !l.is_rec() => {
                    let mut lists: Vec<AttributeList> = l.attributes().collect();
                    for b in l.bindings() {
                        lists.extend(b.attributes());
                    }
                    lists
                }
                ModuleDecl::Extern(x) => x.attributes().collect(),
                _ => continue,
            };
            implied = implied.or(self.routes.marks(&lists).get(Marker::Extension));
        }
        implied
    }

    /// Emit an entity's rows: one per reading of what is uncertain. Its
    /// logical name has a reading per element of `logicals`, and its
    /// compiled name is its logical name unless `honours_compiled_name` and
    /// an attribute may be `[<CompiledName>]`.
    #[allow(clippy::too_many_arguments)]
    fn entity(
        &mut self,
        scope: &Scope,
        logicals: &[String],
        kinds: &[PickledEntityKind],
        public: bool,
        marks: &Marks,
        implied_extension: Maybe,
        honours_compiled_name: bool,
    ) -> Result<(), ExistenceUnread> {
        if honours_compiled_name && marks.compiled_name_unreadable {
            return Err(ExistenceUnread::UnreadableCompiledName(self.index));
        }
        let auto_open = marks.get(Marker::AutoOpen);
        let extension = marks.get(Marker::Extension).or(implied_extension);
        for logical in logicals {
            let mut compiled: BTreeSet<String> = BTreeSet::new();
            if !(honours_compiled_name && marks.compiled_name_certain) {
                compiled.insert(logical.clone());
            }
            if honours_compiled_name {
                compiled.extend(marks.compiled_names.iter().cloned());
            }
            let readings = kinds.len()
                * compiled.len()
                * auto_open.readings().len()
                * extension.readings().len();
            if readings > 1 && marks.uncertain {
                self.out
                    .approximations
                    .insert(Approximation::UncertainAttribute);
            }
            for &kind in kinds {
                for c in &compiled {
                    for &ao in auto_open.readings() {
                        for &ext in extension.readings() {
                            self.out.entities.push(PickledEntityRow {
                                namespace: scope.namespace.clone(),
                                enclosing: scope.enclosing.clone(),
                                logical_name: logical.clone(),
                                compiled_name: c.clone(),
                                kind,
                                public: public && scope.public,
                                auto_open: ao,
                                extension: ext,
                            });
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The logical names a type definition named `name` may have: its name,
    /// with the count of its type parameters that are not units of measure
    /// as an arity suffix when there are any. A parameter that may be a
    /// measure gives both readings.
    fn type_logicals(&mut self, name: &str, defn: &TypeDefn) -> Vec<String> {
        let mut counts: BTreeSet<usize> = BTreeSet::from([0]);
        for t in defn.typar_decls().iter().flat_map(|d| d.typars()) {
            let lists: Vec<AttributeList> = t.attributes().collect();
            let marks = self.routes.marks(&lists);
            let measure = marks.get(Marker::Measure);
            if measure == Maybe::Possibly && marks.uncertain {
                self.out
                    .approximations
                    .insert(Approximation::UncertainAttribute);
            }
            counts = counts
                .into_iter()
                .flat_map(|n| measure.readings().iter().map(move |&m| n + usize::from(!m)))
                .collect();
        }
        counts
            .into_iter()
            .map(|n| {
                if n == 0 {
                    name.to_owned()
                } else {
                    format!("{name}`{n}")
                }
            })
            .collect()
    }

    fn type_defn(
        &mut self,
        scope: &Scope,
        defn: &TypeDefn,
        position: usize,
        ctx: &ListCtx<'_>,
    ) -> Result<(), ExistenceUnread> {
        if is_augmentation(defn) {
            return self.augmentation(scope, defn, position, ctx);
        }
        let name = defn
            .long_id()
            .and_then(|li| li.idents().last())
            .map(|t| id_text(&t).into_owned())
            .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
        let logicals = self.type_logicals(&name, defn);
        let attrs: Vec<AttributeList> = defn.attributes().collect();
        let marks = self.routes.marks(&attrs);
        let measure = marks.get(Marker::Measure);
        let kinds: Vec<PickledEntityKind> = match defn.repr() {
            Some(TypeDefnRepr::Abbrev(a)) => {
                let target = a.ty();
                if target.as_ref().is_some_and(has_static_argument) {
                    return Err(ExistenceUnread::TypeProvider(self.index));
                }
                // FCS reads `type A = B`, `B` one identifier, as a union with
                // case `B` when `B` is `A` or names no type in scope (and `A`
                // is no measure). `B` names a type in scope, whatever else
                // is in scope, when FSharp.Core declares it (it is open in
                // every file) or a type of this file declares it where it is
                // visible. For any other `B` FCS may take the union reading,
                // a check that then fails included, so both readings stand.
                let visible = ctx.visible_at(position);
                match target.as_ref().and_then(abbrev_single_ident) {
                    Some(t) if measure == Maybe::No && t == name => vec![PickledEntityKind::Type],
                    Some(t)
                        if FSHARP_CORE_TYPE_NAMES.contains(&t.as_str())
                            || visible.contains(&t) =>
                    {
                        vec![PickledEntityKind::Abbreviation]
                    }
                    Some(_) if measure != Maybe::Yes => {
                        self.out
                            .approximations
                            .insert(Approximation::AbbreviationOrUnion);
                        vec![PickledEntityKind::Abbreviation, PickledEntityKind::Type]
                    }
                    _ => vec![PickledEntityKind::Abbreviation],
                }
            }
            _ => measure
                .readings()
                .iter()
                .map(|&m| {
                    if m {
                        PickledEntityKind::Measure
                    } else {
                        PickledEntityKind::Type
                    }
                })
                .collect(),
        };
        let public = !header_access_restricts(defn.syntax());
        // The type's own members, which are C#-style extensions when marked.
        let mut members: Vec<MemberDefn> = defn.members().collect();
        if let Some(TypeDefnRepr::ObjectModel(om)) = defn.repr() {
            members.extend(om.members());
        }
        let mut implied = Maybe::No;
        for logical in &logicals {
            implied = implied.or(self.members(&scope.inner(logical, public), &members, None)?);
        }
        self.entity(scope, &logicals, &kinds, public, &marks, implied, true)
    }
    /// The extension rows of members `members` of a type (or of an
    /// augmentation, `augmented`: the extended type's logical-name
    /// spellings): an optional extension's every member, and any member that
    /// may carry `[<Extension>]`. Returns whether some member may carry
    /// `[<Extension>]` (FCS then marks the type).
    fn members(
        &mut self,
        scope: &Scope,
        members: &[MemberDefn],
        augmented: Option<&[String]>,
    ) -> Result<Maybe, ExistenceUnread> {
        let mut implied = Maybe::No;
        for m in members {
            let (lists, shape) = member_shape(m);
            let marks = self.routes.marks(&lists);
            let marked = marks.get(Marker::Extension);
            implied = implied.or(marked);
            if augmented.is_none() && marked == Maybe::No {
                continue;
            }
            if marks.uncertain && marked == Maybe::Possibly && augmented.is_none() {
                self.out
                    .approximations
                    .insert(Approximation::UncertainAttribute);
            }
            if marks.compiled_name_unreadable {
                return Err(ExistenceUnread::UnreadableCompiledName(self.index));
            }
            let vals = match shape {
                MemberShape::NoVal => continue,
                MemberShape::Inherit => {
                    if augmented.is_some() {
                        self.out.approximations.insert(Approximation::RejectedShape);
                    }
                    continue;
                }
                MemberShape::Unnamed => return Err(ExistenceUnread::UnnamedDeclaration(self.index)),
                MemberShape::Named { vals, rejected, .. } => {
                    // An abstract slot or a `val` field FCS rejects in an
                    // augmentation: its rows are read as written.
                    if rejected && augmented.is_some() {
                        self.out.approximations.insert(Approximation::RejectedShape);
                    }
                    vals
                }
            };
            for v in vals {
                match augmented {
                    Some(type_names) => {
                        // An optional extension: compiled `T.name[.Static]`.
                        let mut compiled: BTreeSet<String> = BTreeSet::new();
                        if !marks.compiled_name_certain {
                            for t in type_names {
                                let mut c = format!("{t}.{}", v.logical);
                                if v.is_static {
                                    c.push_str(".Static");
                                }
                                compiled.insert(c);
                            }
                        }
                        compiled.extend(marks.compiled_names.iter().cloned());
                        if compiled.len() > 1 {
                            self.out
                                .approximations
                                .insert(Approximation::UncertainAttribute);
                        }
                        for c in compiled {
                            self.out.extensions.push(ExtensionRow {
                                layer: IndexLayer::Pickle,
                                namespace: scope.namespace.clone(),
                                enclosing: scope.enclosing.clone(),
                                names: val_names(&v.logical, v.accessor, Some(&c)),
                                instance: Some(!v.is_static),
                            });
                        }
                    }
                    None => self.csharp_val(scope, &v, &marks),
                }
            }
        }
        Ok(implied)
    }

    /// A C#-style extension row for a member val `v` of a type.
    fn csharp_val(&mut self, scope: &Scope, v: &MemberVal, marks: &Marks) {
        let compiled: Vec<Option<&String>> = if marks.compiled_names.is_empty() {
            vec![None]
        } else if marks.compiled_name_certain {
            marks.compiled_names.iter().map(Some).collect()
        } else {
            std::iter::once(None)
                .chain(marks.compiled_names.iter().map(Some))
                .collect()
        };
        for c in compiled {
            self.out.extensions.push(ExtensionRow {
                layer: IndexLayer::Pickle,
                namespace: scope.namespace.clone(),
                enclosing: scope.enclosing.clone(),
                names: val_names(&v.logical, v.accessor, c.map(String::as_str)),
                instance: None,
            });
        }
    }

    /// A C#-style extension row for a module value `name`.
    fn csharp_row(
        &mut self,
        scope: &Scope,
        name: &str,
        marks: &Marks,
    ) -> Result<(), ExistenceUnread> {
        if marks.compiled_name_unreadable {
            return Err(ExistenceUnread::UnreadableCompiledName(self.index));
        }
        if marks.uncertain && marks.get(Marker::Extension) == Maybe::Possibly {
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
        let v = MemberVal {
            logical: name.to_owned(),
            accessor: None,
            is_static: true,
        };
        self.csharp_val(scope, &v, marks);
        Ok(())
    }

    /// A module `let` binding under `lists`: a C#-style row per bound value
    /// when it may carry `[<Extension>]`.
    fn binding_extension(
        &mut self,
        scope: &Scope,
        lists: &[AttributeList],
        pat: Option<Pat>,
    ) -> Result<(), ExistenceUnread> {
        let marks = self.routes.marks(lists);
        if marks.get(Marker::Extension) == Maybe::No {
            return Ok(());
        }
        match pat.as_ref().and_then(binding_name) {
            Some(name) => self.csharp_row(scope, &name, &marks),
            None => {
                // A pattern binding names several values, each carrying the
                // attribute; read every name the pattern spells.
                let names: Vec<String> = pat
                    .iter()
                    .flat_map(|p| p.syntax().descendants_with_tokens())
                    .filter_map(|el| el.into_token())
                    .filter(|t| t.kind() == SyntaxKind::IDENT_TOK)
                    .map(|t| id_text(&t).into_owned())
                    .collect();
                if names.is_empty() {
                    return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                }
                self.out.approximations.insert(Approximation::BindingPattern);
                for n in names {
                    self.csharp_row(scope, &n, &marks)?;
                }
                Ok(())
            }
        }
    }

    /// A `type T with …` augmentation's extension rows.
    fn augmentation(
        &mut self,
        scope: &Scope,
        defn: &TypeDefn,
        position: usize,
        ctx: &ListCtx<'_>,
    ) -> Result<(), ExistenceUnread> {
        let mut members: Vec<MemberDefn> = defn.members().collect();
        if let Some(TypeDefnRepr::ObjectModel(om)) = defn.repr() {
            members.extend(om.members());
        }
        let arity = defn.typar_decls().map_or(0, |d| d.typars().count());
        let head: Option<Vec<String>> = defn
            .long_id()
            .map(|li| li.idents().map(|t| id_text(&t).into_owned()).collect());
        let Some(head) = head.filter(|h| !h.is_empty()) else {
            // A tuple type extension (`type (int * int) with`).
            self.out.approximations.insert(Approximation::RejectedShape);
            return self
                .members(scope, &members, Some(&["Tuple".to_owned()]))
                .map(|_| ());
        };
        let last = head.last().expect("not empty").clone();
        // A qualified head names a type of this list only through a path to
        // the list's own container.
        let qualifier = &head[..head.len() - 1];
        let container: Vec<&String> = scope.namespace.iter().chain(&scope.enclosing).collect();
        let intrinsic = if qualifier.is_empty() {
            intrinsic_in(ctx, &last, arity, position)
        } else if qualifier.len() <= container.len()
            && container[container.len() - qualifier.len()..]
                .iter()
                .zip(qualifier)
                .all(|(a, b)| *a == b)
        {
            Maybe::Possibly
        } else {
            Maybe::No
        };
        if intrinsic == Maybe::Possibly {
            self.out
                .approximations
                .insert(Approximation::AugmentationKind);
        }
        if intrinsic == Maybe::Yes {
            // An intrinsic augmentation's members are the type's own: only a
            // marked one is an extension, as a C#-style member of the type.
            let local = if arity == 0 {
                last.clone()
            } else {
                format!("{last}`{arity}")
            };
            self.members(&scope.inner(&local, true), &members, None)?;
            return Ok(());
        }
        if intrinsic == Maybe::Possibly {
            let local = if arity == 0 {
                last.clone()
            } else {
                format!("{last}`{arity}")
            };
            self.members(&scope.inner(&local, true), &members, None)?;
        }
        // The extended type's logical name: its written name with its
        // arity, as every compiler writes it (the certificate's to vouch
        // for); without one, the bare name too.
        let mut type_names = vec![if arity == 0 {
            last.clone()
        } else {
            format!("{last}`{arity}")
        }];
        if arity > 0 && matches!(self.routes, MarkerRoutes::Unknown) {
            type_names.push(last.clone());
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
        self.members(scope, &members, Some(&type_names))?;
        Ok(())
    }
}

/// The declaration list an augmentation sits in.
struct ListCtx<'a> {
    locals: &'a [(LocalType, Maybe)],
    opens: &'a [usize],
    is_rec: bool,
    /// The types the enclosing lists declare before this one.
    outer: &'a [String],
    /// The exceptions a module's suffix meets in this list.
    exceptions: &'a [String],
}

impl ListCtx<'_> {
    /// Whether a module named `name` meets an exception of this list.
    fn meets_exception(&self, name: &str) -> Maybe {
        if self.exceptions.iter().any(|e| e == name) {
            Maybe::Yes
        } else {
            Maybe::No
        }
    }

    /// The names of the types visible, by the lexical scope alone, at
    /// `position` of the list: the enclosing lists' earlier ones, and this
    /// list's up to and including `position`'s own group (all of them, in a
    /// recursive list).
    fn visible_at(&self, position: usize) -> Vec<String> {
        self.outer
            .iter()
            .cloned()
            .chain(
                self.locals
                    .iter()
                    .filter(|(t, _)| self.is_rec || t.position <= position)
                    .map(|(t, _)| t.name.clone()),
            )
            .collect()
    }
}

/// Whether an augmentation of `name` with `arity` type parameters at
/// `position` of a declaration list is intrinsic: the name resolves to a type
/// of the same list (FCS's `isInSameModuleOrNamespace`) that is not an
/// interface, delegate, enum or abbreviation.
fn intrinsic_in(ctx: &ListCtx<'_>, name: &str, arity: usize, position: usize) -> Maybe {
    // The latest earlier definition (any, in a recursive list) of that name
    // and arity: the one the name resolves to.
    let found = ctx
        .locals
        .iter()
        .map(|(t, _)| t)
        .filter(|t| t.name == name && t.arity == arity)
        .filter(|t| ctx.is_rec || t.position <= position)
        .max_by_key(|t| t.position);
    let Some(t) = found else {
        return Maybe::No;
    };
    // An `open` after the type may bring another of its name.
    if ctx
        .opens
        .iter()
        .any(|&o| (o > t.position && o < position) || (ctx.is_rec && o != position))
    {
        return Maybe::Possibly;
    }
    match t.kind {
        LocalKind::ClassLike => Maybe::Yes,
        LocalKind::NotClassLike => Maybe::No,
        LocalKind::Unknown => Maybe::Possibly,
    }
}

/// What augmenting `defn` in its own list makes of the members.
fn local_kind(defn: &TypeDefn) -> LocalKind {
    match defn.repr() {
        Some(TypeDefnRepr::Record(_)) | Some(TypeDefnRepr::Union(_)) => LocalKind::ClassLike,
        Some(TypeDefnRepr::Enum(_))
        | Some(TypeDefnRepr::Delegate(_))
        | Some(TypeDefnRepr::Abbrev(_)) => LocalKind::NotClassLike,
        Some(TypeDefnRepr::ObjectModel(om)) => {
            if om.is_interface() {
                LocalKind::NotClassLike
            } else if om.is_class() || om.is_struct() || defn.implicit_ctor().is_some() {
                LocalKind::ClassLike
            } else {
                let members: Vec<MemberDefn> = om.members().collect();
                if members.is_empty() {
                    LocalKind::Unknown
                } else if members
                    .iter()
                    .all(|m| matches!(m, MemberDefn::AbstractSlot(s) if !s.is_static()))
                {
                    LocalKind::NotClassLike
                } else if members
                    .iter()
                    .any(|m| matches!(m, MemberDefn::AbstractSlot(_) | MemberDefn::Inherit(_)))
                {
                    LocalKind::Unknown
                } else {
                    LocalKind::ClassLike
                }
            }
        }
        Some(TypeDefnRepr::InlineIl(_)) | None => LocalKind::Unknown,
    }
}

fn is_augmentation(defn: &TypeDefn) -> bool {
    matches!(defn.repr(), Some(TypeDefnRepr::ObjectModel(om)) if om.is_augmentation())
        || defn.tuple_type_head().is_some()
}

/// Whether `module`'s, a type's or a nested module's header carries an
/// access modifier other than `public` before its name. One after the name
/// FCS discards.
fn header_access_restricts(node: &SyntaxNode) -> bool {
    for el in node.children_with_tokens() {
        match el {
            borzoi_cst::syntax::NodeOrToken::Node(n) if n.kind() == SyntaxKind::LONG_IDENT => {
                return false;
            }
            borzoi_cst::syntax::NodeOrToken::Token(t) if t.kind() == SyntaxKind::ACCESS_TOK => {
                return t.text() != "public";
            }
            _ => {}
        }
    }
    false
}

/// Whether an exception definition's case carries an access modifier other
/// than `public` (`exception internal E`).
fn exception_access_restricts(node: &SyntaxNode) -> bool {
    node.descendants_with_tokens()
        .filter_map(|el| el.into_token())
        .take_while(|t| t.kind() != SyntaxKind::IDENT_TOK)
        .find(|t| t.kind() == SyntaxKind::ACCESS_TOK)
        .is_some_and(|t| t.text() != "public")
}

fn long_id_segments(li: Option<LongIdent>) -> Option<Vec<String>> {
    let segs: Vec<String> = li?.idents().map(|t| id_text(&t).into_owned()).collect();
    (!segs.is_empty()).then_some(segs)
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

/// The single identifier an abbreviation's target names, parentheses
/// stripped: the shape FCS may read as a union case.
fn abbrev_single_ident(ty: &Type) -> Option<String> {
    match ty {
        Type::Paren(p) => p.inner().as_ref().and_then(abbrev_single_ident),
        Type::LongIdent(t) => {
            let li = t.long_ident()?;
            let mut idents = li.idents();
            let first = idents.next()?;
            idents
                .next()
                .is_none()
                .then(|| id_text(&first).into_owned())
        }
        _ => None,
    }
}

/// Whether a type holds a static argument (a type provider's): a constant
/// in type-argument position.
fn has_static_argument(ty: &Type) -> bool {
    ty.syntax().descendants().any(|n| {
        matches!(
            n.kind(),
            SyntaxKind::STATIC_CONST_TYPE
                | SyntaxKind::STATIC_CONST_EXPR_TYPE
                | SyntaxKind::STATIC_CONST_NAMED_TYPE
                | SyntaxKind::STATIC_CONST_NULL_TYPE
        )
    })
}

/// A module `let` binding's single name: `let f …`, `let x`, `let (|A|_|) …`,
/// an operator, under parentheses or a type annotation.
fn binding_name(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Named(n) => n.ident().map(|t| id_text(&t).into_owned()),
        Pat::LongIdent(l) => {
            if let Some(ap) = l.active_pat_name() {
                return Some(active_pattern_name(&ap));
            }
            let li = l.head()?;
            let mut idents = li.idents();
            let first = idents.next()?;
            idents
                .next()
                .is_none()
                .then(|| id_text(&first).into_owned())
        }
        Pat::Paren(p) => p.inner().as_ref().and_then(binding_name),
        Pat::Typed(t) => t.pat().as_ref().and_then(binding_name),
        Pat::Attrib(a) => a.pat().as_ref().and_then(binding_name),
        _ => None,
    }
}

/// Every name a call may spell a val by, as the pickle's extension rows list
/// them: its logical name, its compiled name, and for a property accessor
/// the property's name and the accessor's.
fn val_names(logical: &str, accessor: Option<&str>, compiled: Option<&str>) -> Vec<String> {
    let mut names = vec![logical.to_owned()];
    if let Some(c) = compiled {
        names.push(c.to_owned());
    }
    if let Some(prefix) = accessor {
        match logical.strip_prefix(prefix) {
            Some(bare) => names.push(bare.to_owned()),
            None => names.push(format!("{prefix}{logical}")),
        }
    }
    names.sort();
    names.dedup();
    names
}

/// Certify `routes` from spelling: each written name in `files` denotes
/// the marker whose type name it spells (with or without the `Attribute`
/// suffix) under a qualifier that is a suffix of that marker's namespace
/// path, and nothing else. A name some type of A's own is declared as is
/// omitted, so it reads as under [`MarkerRoutes::Unknown`].
///
/// This is the certificate exactly when A's references neither alias nor
/// shadow a marker in a scope A opens: a caller that knows that (a test
/// whose references it wrote) may use it; any other caller must resolve.
pub fn certify_by_spelling(files: &[&ProjectFile]) -> MarkerRoutes {
    let mut declared: BTreeSet<String> = BTreeSet::new();
    let mut written: BTreeSet<Vec<String>> = BTreeSet::new();
    for pf in files {
        let root = pf.file.syntax();
        for defn in root.descendants().filter_map(TypeDefn::cast) {
            if let Some(t) = defn.long_id().and_then(|li| li.idents().last()) {
                declared.insert(id_text(&t).into_owned());
            }
        }
        for e in root
            .descendants()
            .filter_map(borzoi_cst::syntax::ExceptionDefnDecl::cast)
        {
            if let Some(t) = e.union_case().and_then(|c| c.ident()) {
                declared.insert(id_text(&t).into_owned());
            }
        }
        for list in root.descendants().filter_map(AttributeList::cast) {
            for attr in list.attributes() {
                if let Some(name) = written_name(&attr) {
                    written.insert(name);
                }
            }
        }
    }
    let mut map = BTreeMap::new();
    for name in written {
        let (last, qualifier) = name.split_last().expect("written names are not empty");
        let stem = last.strip_suffix("Attribute").unwrap_or(last);
        if declared.contains(stem) || declared.contains(&format!("{stem}Attribute")) {
            continue;
        }
        let mut set = BTreeSet::new();
        for m in Marker::ALL {
            let full = m.full_name();
            let (type_name, ns) = full.split_last().expect("a full name is not empty");
            let spelled = last == type_name || format!("{last}Attribute") == *type_name;
            let qualified = qualifier.len() <= ns.len()
                && ns[ns.len() - qualifier.len()..]
                    .iter()
                    .zip(qualifier)
                    .all(|(a, b)| a == b);
            if spelled && qualified {
                set.insert(m);
            }
        }
        map.insert(name, set);
    }
    MarkerRoutes::Certified(map)
}

#[cfg(test)]
mod tests;
