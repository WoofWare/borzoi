//! A referenced F# project's **entity surface**, read from its source
//! ([`source_existence`]): rows in the currency of
//! [`borzoi_assembly::existence`], so open certification reads a project
//! reference as it reads a DLL.
//!
//! The function is pure. Its input is a producer project A as the caller
//! evaluated it ([`Producer`]): A's Compile items, parsed under A's own
//! defines and language version, and what the caller knows of A's reference
//! environment ([`MarkerRoutes`], [`ProviderReferences`]). Its output
//! ([`SourceExistence`]) is either the rows, or `Unread` with the reason A's
//! surface cannot be known.
//!
//! # The claim, by half
//!
//! The [`crate::assembly_env::existence`] set answers two families of
//! questions, and a source producer feeds each from a different reading.
//!
//! - **The entity half** (this module): what open certification asks, from
//!   an entity's namespace, enclosers and names (each **canonical**: a generic
//!   arity suffix and one trailing `Module` stripped), whether it is a
//!   namespace or an abbreviation, its `[<AutoOpen>]` flag, and the
//!   assembly-level `[<AutoOpen("…")>]` paths. Every such question is
//!   monotone, so the claim is **containment** on those facts: every one the
//!   set holds of FCS's CCU for A (its in-memory signature, and the pickle of
//!   the DLL FCS compiles from it) it also holds of these rows.
//!   `source_existence_diff` grades that on the set's own facts
//!   (`test_support::existence_facts`), and pins the surplus.
//! - **The extension half** is not read here. FCS binds a call to an
//!   extension by its logical name (`MethInfo.LogicalName`, `infos.fs`), so
//!   the gate reads A's `ExtensionNames`, the currency it already reads for
//!   B's own files, and the claim is the gate grid's certain-implies-exact,
//!   graded with A as a referenced project. These rows carry no extension
//!   rows ([`SourceSurface`] has no field for them) and no `[<Extension>]`
//!   flag.
//!
//! Fields no entity question reads are constants: an entity's accessibility
//! (`public` is always `true`), its kind beyond namespace and abbreviation,
//! and the `[<Extension>]` flag. **A later stage that reads more of a source
//! producer (stage 2a's shells read accessibility and kinds) must derive
//! those fields itself, with its own exactness claim and grading.**
//!
//! # What the walk reads, and how it knows it read all of it
//!
//! Each syntax node the walk interprets is a [`Leaf`], and the walk reads it
//! by classifying it into one [`Form`]: a closed list, whose
//! [`Form::verdict`] says whether a producer holding it is read. A
//! classifier accounts for **every child** of its node ([`consumed`]): a
//! child no classifier names (an unexpected token, a node shape the grammar
//! grows) is [`ExistenceUnread::Unreadable`], so a child the walk did not
//! read cannot change the surface unseen. `source_existence_domain` grades
//! every [`Form::ALL`] witness against FCS.
//!
//! Three readings scan raw syntax kinds rather than a typed child
//! ([`RAW_SCANS`]); each has its own grid cell.
//!
//! # Spellings the walk derives
//!
//! Every name the walk emits is written in A's source, but for these:
//!
//! - **A module's `Module` suffix** (`ComputeModuleOrNamespaceKind` and
//!   `AdjustModuleName`, `CheckDeclarations.fs:2731-2738`): a nested module
//!   takes it under `[<CompilationRepresentation(ModuleSuffix)>]` or beside a
//!   type of its name in its own declaration list (`TypeNamesInNonMutRecDecls`
//!   and kin, `CheckDeclarations.fs:2773-2809`); a top-level module only under
//!   the attribute (FCS reads `module A.M` as a namespace holding one module,
//!   `CheckDeclarations.fs:5903-5917`). Canonical spelling strips one
//!   `Module`, so the suffix moves a fact only on a name already ending in
//!   `Module`, where the walk decides it exactly or declines
//!   ([`ExistenceUnread::ModuleSuffix`]).
//! - **A type's `[<CompiledName>]`**: the literal, beside the logical name.
//!   One the walk cannot read declines.
//! - **Generic arity on an entity's name** (``Map`2``): erased by canonical
//!   spelling, so none is emitted.
//!
//! # Attributes
//!
//! Whether an attribute is `[<AutoOpen>]`, `[<Measure>]`, `[<CompiledName>]`,
//! `[<CompilationRepresentation>]` or `[<TypeProviderAssembly>]` depends on
//! what its name resolves to, and A's references can route any name to any of
//! them (an abbreviation) or away from them (a shadow). The walk does not
//! resolve: the caller states what each written name denotes
//! ([`MarkerRoutes::Certified`], by the full name of the type it resolves
//! to), or nothing at all ([`MarkerRoutes::Unknown`]), in which case every
//! attribute may denote every marker.
//!
//! # The input bound
//!
//! Before it walks, the walk bounds its input ([`MAX_NAME_BYTES`],
//! [`MAX_DEPTH`], [`MAX_DECLARATIONS`]) and declines past it
//! ([`ExistenceUnread::TooManyReadings`]). Inside the bound every row is one
//! declaration's, and its path at most [`MAX_DEPTH`] names of at most
//! [`MAX_NAME_BYTES`]: the memory the rows take is bounded by the input, with
//! no metering to forget.
//!
//! # The input inventory
//!
//! Every channel through which A's source or evaluation decides its surface
//! is a [`Channel`], and what the walk does with it is
//! [`Channel::treatment`]. The unit test `the_inventory_is_what_the_walk_does`
//! runs one witness per channel and holds the walk to its treatment.

// A match over a syntax enum that skips the kinds it does not name is where
// a construct the walk never reads hides: every arm names its kinds, so a
// new one is a compile error until the walk reads it or declines it.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use borzoi_assembly::existence::{
    ExistenceIndex, PickleLayer, PickledEntityKind, PickledEntityRow,
};
use borzoi_cst::syntax::{
    AstNode, Attribute, AttributeList, ExceptionDefnDecl, Expr, ImplicitCtor, LongIdent,
    MemberDefn, ModuleDecl, ModuleOrNamespace, ModuleOrNamespaceKind, SigDecl, SyntaxKind,
    SyntaxNode, TupleTypeExtensionHead, TyparDecls, Type, TypeDefn, TypeDefnRepr, UnionCase,
};

use crate::def::id_text;
use crate::recovery::SyntaxRecovery;
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
        providers: ProviderReferences,
    },
    /// A's fold is refused (an untrusted Compile set, untrusted defines, an
    /// untrusted language version on a file whose parse it decides).
    FoldRefused(&'a str),
    /// The producer TFM the dependant is paired with is not the one A was
    /// evaluated at.
    UnservedTfm(&'a str),
}

/// Whether one of A's references may be a type provider: the caller's to
/// state, as it states [`MarkerRoutes`]. A generative provider applied to a
/// literal-bound identifier (`type T = Gen<N>`) parses as an ordinary type
/// application, and FCS then reads A from its DLL, never its source; only
/// A's references tell the two apart.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProviderReferences {
    /// No reference is a type provider (none carries
    /// `[<TypeProviderAssembly>]`): a type application is never one.
    None,
    /// One may be: an abbreviation of any named type may be a generative
    /// provider's.
    Possible,
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

/// An attribute the entity rows depend on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Marker {
    /// `Microsoft.FSharp.Core.AutoOpenAttribute`.
    AutoOpen,
    /// `Microsoft.FSharp.Core.MeasureAttribute`: decides whether
    /// `type X = X` is an abbreviation.
    Measure,
    /// `Microsoft.FSharp.Core.CompiledNameAttribute`, on a type.
    CompiledName,
    /// `Microsoft.FSharp.Core.CompilationRepresentationAttribute`, whose
    /// `ModuleSuffix` flag suffixes a module.
    CompilationRepresentation,
    /// `Microsoft.FSharp.Core.CompilerServices.TypeProviderAssemblyAttribute`.
    TypeProviderAssembly,
}

impl Marker {
    /// Every marker.
    pub const ALL: [Marker; 5] = [
        Marker::AutoOpen,
        Marker::Measure,
        Marker::CompiledName,
        Marker::CompilationRepresentation,
        Marker::TypeProviderAssembly,
    ];

    /// The marker's full name, its namespace's segments then its type name.
    pub fn full_name(self) -> &'static [&'static str] {
        match self {
            Marker::AutoOpen => &["Microsoft", "FSharp", "Core", "AutoOpenAttribute"],
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
    /// the markers it denotes: a marker exactly when, at **every** site in A
    /// that writes it, the name resolves to a type whose full name is the
    /// marker's ([`Marker::full_name`]), in any assembly, A's own included.
    /// This is path identity, as the DLL reader compares an attribute's type
    /// (`pickled_rows::carries`), not the identity of one tycon. A name that
    /// resolves to no type, or to types of different full names at
    /// different sites, must be omitted. An omitted name is read as under
    /// [`MarkerRoutes::Unknown`], so an incomplete certificate is sound and
    /// only widens the surplus. An empty set certifies that the name
    /// denotes no marker.
    Certified(BTreeMap<Vec<String>, BTreeSet<Marker>>),
}

/// Why A's entity surface cannot be read.
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
    /// target, or with [`ProviderReferences::Possible`] any named type
    /// there), or A may be one (an assembly attribute that may be
    /// `[<TypeProviderAssembly>]`): FCS then reads A's DLL, not its source.
    TypeProvider(usize),
    /// An assembly-level attribute that may be `[<AutoOpen>]` has an argument
    /// the walk cannot read as a string.
    UnreadableAutoOpen(usize),
    /// An attribute that may be `[<CompiledName>]` on a type has an argument
    /// the walk cannot read as a string.
    UnreadableCompiledName(usize),
    /// A headerless file whose implicit module name the walk cannot spell.
    AnonymousModuleName(usize),
    /// A module whose name ends in `Module` under an attribute that may
    /// suffix it, or beside a type of its name that may count: whether FCS
    /// spells it `…ModuleModule` is unknown.
    ModuleSuffix(usize),
    /// The input exceeds the walk's bound ([`MAX_NAME_BYTES`],
    /// [`MAX_DEPTH`], [`MAX_DECLARATIONS`]).
    TooManyReadings,
    /// A node of this leaf the walk cannot classify: a shape outside every
    /// [`Form`], or a child no classifier accounts for.
    Unreadable(usize, Leaf),
}

/// A syntax node the walk interprets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Leaf {
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
    /// An attribute: its target, name and argument.
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

            /// Whether a producer holding the form is read, with no
            /// reference a type provider.
            pub fn verdict(self) -> Verdict {
                match self {
                    $(Form::$name => Verdict::$verdict,)*
                }
            }

            /// A producer (one implementation file) whose walk classifies
            /// the form: the domain grid's cell for it.
            pub fn witness(self) -> &'static str {
                match self {
                    $(Form::$name => $witness,)*
                }
            }
        }
    };
}

forms! {
    /// `namespace global`.
    GlobalNamespace: FileHeader, Read, "namespace global\ntype T = int\n";
    /// `namespace A.B`.
    Namespace: FileHeader, Read, "namespace A.B\ntype T = int\n";
    /// `module A.M` at the top of a file.
    NamedModule: FileHeader, Read, "module A.M\ntype T = int\n";
    /// A file with no header: its implicit module, named from the file.
    AnonymousModule: FileHeader, Read, "type T = int\nlet x = 1\n";
    /// A long identifier of plain identifiers.
    PlainName: Name, Read, "module A.B.C\nlet x = 1\n";
    /// A long identifier rooted at `global.` (an attribute's name).
    RootedName: Name, Read, "module D\n[<global.Microsoft.FSharp.Core.AutoOpen>]\nmodule M =\n    let x = 1\n";
    /// `module M = …`.
    NestedModule: NestedModule, Read, "module Outer\nmodule Inner =\n    let x = 1\n";
    /// `module M = begin end`, a module with no declarations.
    EmptyNestedModule: NestedModule, Read, "module Outer\nmodule Inner = begin end\n";
    /// `type T = …`, no type parameters.
    Type: TypeDefinition, Read, "module D\ntype T = { X: int }\n";
    /// `type T<'a> = …`.
    GenericType: TypeDefinition, Read, "module D\ntype T<'a> = { X: 'a }\n";
    /// `type T with …`: an augmentation, which declares no entity.
    Augmentation: TypeDefinition, Read, "module D\ntype R = { X: int }\ntype R with\n    member r.Y = 1\n";
    /// `type (int * int) with …`, which declares no entity.
    TupleAugmentation: TypeDefinition, Read, "module D\ntype (int * int) with\n    member x.M() = 1\n";
    /// `type X.Y = …`: FCS rejects it (FS0925) and recovers it as `X`.
    DottedType: TypeDefinition, Declined, "module D\ntype X.Y = { N: int }\n";
    /// `exception E of …`.
    Exception: Exception, Read, "module D\nexception E of string\n";
    /// `exception F = E`.
    ExceptionAbbreviation: Exception, Read, "module D\nexception E of string\nexception F = E\n";
    /// `type X = X`: a union unless `X` is a unit of measure.
    SelfNamedTarget: AbbreviationTarget, Read, "module D\ntype X = X\n";
    /// `type A = int`: a name FSharp.Core declares in a namespace every file
    /// has open.
    FSharpCoreTarget: AbbreviationTarget, Read, "module D\ntype A = int\n";
    /// `type A = B`, `B` one identifier: a union case when `B` names no type.
    SingleIdentTarget: AbbreviationTarget, Read, "module D\ntype A = B\n";
    /// A tuple, function, array, variable or anonymous type: no provider's.
    StructuralTarget: AbbreviationTarget, Read, "module D\ntype A = int * string\n";
    /// Any other named type (qualified, applied).
    NamedTarget: AbbreviationTarget, Read, "module D\ntype A = System.Collections.Generic.List<int>\n";
    /// A type holding a static argument: a type provider's.
    StaticArgumentTarget: AbbreviationTarget, Declined, "module D\ntype A = Provider<\"x\">\n";
    /// `[<A>]`.
    AttributeNoArgument: Attribute, Read, "module D\n[<AutoOpen>]\nmodule M =\n    let x = 1\n";
    /// `[<A()>]`.
    AttributeUnitArgument: Attribute, Read, "module D\n[<AutoOpen()>]\nmodule M =\n    let x = 1\n";
    /// `[<A("…")>]`, a regular string with no escape.
    AttributeStringArgument: Attribute, Read, "module D\n[<CompiledName(\"R\")>]\ntype T = { X: int }\n";
    /// `[<A(@"…")>]`.
    AttributeVerbatimArgument: Attribute, Read, "module D\n[<CompiledName(@\"R\")>]\ntype T = { X: int }\n";
    /// `[<A("""…""")>]`.
    AttributeTripleQuotedArgument: Attribute, Read, "module D\n[<CompiledName(\"\"\"R\"\"\")>]\ntype T = { X: int }\n";
    /// `[<A(B.C)>]`, a long identifier: a flags value.
    AttributeLongIdentArgument: Attribute, Read, "module D\n[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\nmodule M =\n    let x = 1\n";
    /// Any other argument.
    AttributeOtherArgument: Attribute, Read, "module D\n[<System.Obsolete(\"a\" + \"b\")>]\ntype T = { X: int }\n";
    /// `[<assembly: A>]`.
    AssemblyTarget: Attribute, Read, "module D\n[<assembly: AutoOpen(\"D\")>]\ndo ()\n";
    /// `[<module: A>]`, `[<type: A>]`, `[<return: A>]` and FCS's other
    /// carrier targets.
    CarrierTarget: Attribute, Read, "module D\n[<type: CompiledName(\"R\")>]\ntype T = { X: int }\n";
    /// `#r`, `#reference`, `#load`, `#I`, `#include`: code the check reads
    /// from elsewhere.
    ReferenceDirective: HashDirective, Declined, "module D\n#r \"x.dll\"\nlet x = 1\n";
    /// Any other directive (`#time`, `#help`, …). `#nowarn` is trivia to
    /// the parser, never a declaration.
    OtherDirective: HashDirective, Read, "module D\n#time \"on\"\nlet x = 1\n";
}

/// The readings that scan raw syntax kinds rather than read a typed child,
/// each with the grid cell that witnesses it.
pub const RAW_SCANS: &[(&str, &str)] = &[
    (
        "HASH_DIRECTIVE_DECL anywhere in a file: a directive in any module declines A",
        "hash_reference_nested",
    ),
    (
        "a directive's first IDENT_TOK, de-quoted: the directive's name",
        "quoted_load_directive",
    ),
    (
        "every ATTRIBUTE_LIST, and whether an ATTRIBUTES_DECL holds it: \
         the attributes FCS may read as assembly-level",
        "standalone_assembly_attribute",
    ),
];

/// A place the walk emitted facts FCS's CCU may not hold: where the surplus
/// comes from.
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
    /// The pickle's entity rows, namespaces included: no IL layer (FCS reads
    /// a project from source with none) and no extension rows (the gate
    /// reads A's `ExtensionNames`).
    pub entities: Vec<PickledEntityRow>,
    /// The paths an assembly-level `[<AutoOpen("…")>]` may name: FCS's
    /// `GetAutoOpenAttributes`, or more.
    pub assembly_auto_opens: Vec<String>,
    /// Where the rows may hold more than FCS's.
    pub approximations: BTreeSet<Approximation>,
}

impl SourceSurface {
    /// The rows as an existence index: an empty IL layer, the entity rows,
    /// and no extension rows.
    pub fn index(&self) -> ExistenceIndex {
        ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(self.entities.clone()),
            extensions: Vec::new(),
        }
    }
}

impl SourceExistence {
    /// The existence set's input for A's entity half.
    pub fn existence_input(&self) -> crate::ExistenceInput {
        match self {
            SourceExistence::Read(s) => crate::ExistenceInput::Read(s.index()),
            SourceExistence::Unread(_) => crate::ExistenceInput::Unread,
        }
    }
}

/// Declare [`Channel`] and [`Channel::ALL`] together, so that a channel
/// cannot be added to the one without the other.
macro_rules! channels {
    ($($(#[doc = $doc:literal])* $name:ident,)*) => {
        /// One row of the input inventory: a channel through which A's
        /// source, or A's evaluation, can decide A's entity surface.
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
    /// The `Module` suffix FCS adds to a module beside a type of its name,
    /// or under `[<CompilationRepresentation(ModuleSuffix)>]`.
    ModuleSuffix,
    /// A suffix the walk cannot decide on a name ending in `Module`.
    UncertainModuleSuffix,
    /// Class, struct, interface, record, union, enum, delegate, measure.
    TypeDefinition,
    /// `type A = T`.
    Abbreviation,
    /// `type A = B` with `B` one identifier that may be a union case.
    AbbreviationOrUnion,
    /// `exception E`.
    Exception,
    /// A static argument in an abbreviation's target (a type provider).
    TypeProviderUse,
    /// `[<AutoOpen>]` on an entity.
    AutoOpenAttribute,
    /// `[<CompiledName("…")>]` on a type (modules and exceptions ignore it).
    CompiledNameAttribute,
    /// An attribute's explicit target: an entity keeps every attribute of
    /// its lists, whatever the target.
    AttributeTarget,
    /// An attribute that may be `[<CompiledName>]` with an argument the walk
    /// cannot read.
    UnreadableCompiledName,
    /// An assembly-level `[<AutoOpen("…")>]`: one with an `assembly:`
    /// target, or any in a standalone attribute declaration (`[<A>] do ()`),
    /// which FCS reads as assembly-level when the attribute allows it.
    AssemblyAutoOpen,
    /// An assembly attribute that may be `[<AutoOpen>]` with an argument the
    /// walk cannot read.
    AssemblyAutoOpenUnreadable,
    /// An assembly attribute that may be `[<TypeProviderAssembly>]`.
    TypeProviderAssembly,
    /// An attribute name the certificate does not cover.
    UncertifiedAttribute,
    /// A node shape outside every [`Form`], or a child no classifier reads.
    Unreadable,
    /// An input past the walk's bound.
    InputBound,
    /// Extension members, under any attribute and in any shape: A's
    /// `ExtensionNames`, which the gate reads.
    ExtensionMembers,
    /// An entity's accessibility, combined with its enclosers'.
    Accessibility,
    /// `[<Measure>] type m`, and an exception's or a module's kind.
    EntityKind,
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
            | Channel::UncertainModuleSuffix
            | Channel::TypeProviderUse
            | Channel::UnreadableCompiledName
            | Channel::AssemblyAutoOpenUnreadable
            | Channel::TypeProviderAssembly
            | Channel::Unreadable
            | Channel::InputBound => Treatment::Declined,
            Channel::Defines | Channel::LanguageVersion | Channel::GeneratedItems => {
                Treatment::Caller
            }
            Channel::SignaturePair => Treatment::Approximated(A::SignaturePair),
            Channel::AbbreviationOrUnion => Treatment::Approximated(A::AbbreviationOrUnion),
            Channel::UncertifiedAttribute => Treatment::Approximated(A::UncertainAttribute),
            Channel::ExtensionMembers => Treatment::ExtensionNames,
            Channel::Accessibility | Channel::EntityKind => Treatment::Unconsumed,
            Channel::HeaderlessFile
            | Channel::Namespace
            | Channel::Module
            | Channel::ModuleAbbreviation
            | Channel::ModuleSuffix
            | Channel::TypeDefinition
            | Channel::Abbreviation
            | Channel::Exception
            | Channel::AutoOpenAttribute
            | Channel::CompiledNameAttribute
            | Channel::AttributeTarget
            | Channel::AssemblyAutoOpen => Treatment::Modelled,
        }
    }
}

/// What the walk does with a channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Treatment {
    /// Read: the facts it decides are FCS's, with no surplus.
    Modelled,
    /// Read, with the named surplus.
    Approximated(Approximation),
    /// A is unread.
    Declined,
    /// The caller's: the input carries it, already applied.
    Caller,
    /// Read by A's `ExtensionNames`, which the gate consumes, not by this
    /// walk.
    ExtensionNames,
    /// It decides only fields no entity question reads, which the walk
    /// leaves constant.
    Unconsumed,
}

/// The longest entity name (a namespace segment, a module, type or
/// exception name), in bytes, the walk reads.
pub const MAX_NAME_BYTES: usize = 256;

/// The most names in an entity's path (its namespace's segments, its
/// enclosing modules', and its own) the walk reads.
pub const MAX_DEPTH: usize = 16;

/// The most declarations (namespace segments of every header, modules,
/// types and exceptions) of one project the walk reads.
pub const MAX_DECLARATIONS: usize = 50_000;

/// A's entity surface, read from its source. See the module docs.
pub fn source_existence(producer: Producer<'_>) -> SourceExistence {
    read(producer).0
}

/// [`source_existence`], with every [`Form`] the walk classified before it
/// finished or declined.
pub(crate) fn read(producer: Producer<'_>) -> (SourceExistence, BTreeSet<Form>) {
    match producer {
        Producer::FoldRefused(why) => (
            SourceExistence::Unread(ExistenceUnread::FoldRefused(why.to_owned())),
            BTreeSet::new(),
        ),
        Producer::UnservedTfm(why) => (
            SourceExistence::Unread(ExistenceUnread::UnservedTfm(why.to_owned())),
            BTreeSet::new(),
        ),
        Producer::Evaluated {
            items,
            routes,
            providers,
        } => {
            let mut forms = BTreeSet::new();
            let read = match walk_project(items, routes, providers, &mut forms) {
                Ok(surface) => SourceExistence::Read(surface),
                Err(why) => SourceExistence::Unread(why),
            };
            (read, forms)
        }
    }
}

fn walk_project(
    items: &[CompileItem<'_>],
    routes: &MarkerRoutes,
    providers: ProviderReferences,
    forms: &mut BTreeSet<Form>,
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
    for (i, pf) in files.iter().enumerate() {
        if !matches!(&pf.recovery, SyntaxRecovery::Reported(errors) if errors.is_empty()) {
            return Err(ExistenceUnread::Recovered(i));
        }
    }
    preflight(&files)?;
    let partners = signature_partners(&files);
    let mut out = Out::default();
    for (i, pf) in files.iter().enumerate() {
        let root = pf.file.syntax();
        for directive in root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::HASH_DIRECTIVE_DECL)
        {
            let form = hash_directive(&directive);
            forms.insert(form);
            if form.verdict() == Verdict::Declined {
                return Err(ExistenceUnread::HashReference(i));
            }
        }
        // A signature and its implementation contribute both their rows
        // (decision D7): FCS's are the signature's, which the union holds.
        if partners[i].is_some() {
            out.approximations.insert(Approximation::SignaturePair);
        }
        let mut file = FileWalk {
            index: i,
            routes,
            providers,
            out: &mut out,
            forms,
        };
        file.walk(pf)?;
    }
    let mut entities: Vec<PickledEntityRow> = out
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
    entities.extend(out.entities);
    entities.sort();
    entities.dedup();
    Ok(SourceSurface {
        entities,
        assembly_auto_opens: out.auto_opens,
        approximations: out.approximations,
    })
}

/// Hold the input to the walk's bound before anything is walked: every
/// entity name at most [`MAX_NAME_BYTES`], every path at most
/// [`MAX_DEPTH`] deep, at most [`MAX_DECLARATIONS`] declarations.
fn preflight(files: &[ProjectFile]) -> Result<(), ExistenceUnread> {
    let mut declarations = 0usize;
    let mut count = |names: &[String], depth: usize| -> Result<(), ExistenceUnread> {
        declarations += names.len().max(1);
        if depth > MAX_DEPTH
            || declarations > MAX_DECLARATIONS
            || names.iter().any(|n| n.len() > MAX_NAME_BYTES)
        {
            Err(ExistenceUnread::TooManyReadings)
        } else {
            Ok(())
        }
    };
    for pf in files {
        let modules: Vec<ModuleOrNamespace> = match &pf.file {
            SourceFile::Impl(f) => f.modules().collect(),
            SourceFile::Sig(f) => f.modules().collect(),
        };
        for m in modules {
            let header = m.long_id().map(|li| names_of(&li)).unwrap_or_default();
            count(&header, header.len())?;
            let decls = match &pf.file {
                SourceFile::Impl(_) => Decls::Impl(m.decls().collect()),
                SourceFile::Sig(_) => Decls::Sig(m.sig_decls().collect()),
            };
            preflight_decls(&decls, header.len(), &mut count)?;
        }
    }
    Ok(())
}

fn preflight_decls(
    decls: &Decls,
    depth: usize,
    count: &mut impl FnMut(&[String], usize) -> Result<(), ExistenceUnread>,
) -> Result<(), ExistenceUnread> {
    let type_names = |defns: &mut dyn Iterator<Item = TypeDefn>| -> Vec<String> {
        defns
            .filter_map(|d| d.long_id())
            .flat_map(|li| names_of(&li))
            .collect()
    };
    match decls {
        Decls::Impl(ds) => {
            for d in ds {
                match d {
                    ModuleDecl::NestedModule(m) => {
                        let names = m.long_id().map(|li| names_of(&li)).unwrap_or_default();
                        count(&names, depth + 1)?;
                        preflight_decls(&Decls::Impl(m.decls().collect()), depth + 1, count)?;
                    }
                    ModuleDecl::Types(t) => count(&type_names(&mut t.defns()), depth + 1)?,
                    ModuleDecl::Exception(e) => count(&exception_names(e), depth + 1)?,
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
        Decls::Sig(ds) => {
            for d in ds {
                match d {
                    SigDecl::NestedModule(m) => {
                        let names = m.long_id().map(|li| names_of(&li)).unwrap_or_default();
                        count(&names, depth + 1)?;
                        preflight_decls(&Decls::Sig(m.sig_decls().collect()), depth + 1, count)?;
                    }
                    SigDecl::Types(t) => count(&type_names(&mut t.defns()), depth + 1)?,
                    SigDecl::Exception(e) => count(&exception_names(e), depth + 1)?,
                    SigDecl::Val(_)
                    | SigDecl::Open(_)
                    | SigDecl::ModuleAbbrev(_)
                    | SigDecl::HashDirective(_) => {}
                }
            }
        }
    }
    Ok(())
}

fn exception_names(e: &ExceptionDefnDecl) -> Vec<String> {
    e.union_case()
        .and_then(|c| c.ident())
        .map(|t| vec![id_text(&t).into_owned()])
        .unwrap_or_default()
}

fn names_of(li: &LongIdent) -> Vec<String> {
    li.idents().map(|t| id_text(&t).into_owned()).collect()
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

/// A long identifier's names, and its form: plain identifiers, or rooted at
/// `global.`, whose names start with `global` (a rooted name is written
/// apart from an unrooted one, and may resolve apart). `None` for any other
/// child (an operator, an active pattern's name).
fn long_ident(li: &LongIdent) -> Option<(Form, Vec<String>)> {
    if !consumed(
        li.syntax(),
        |_| false,
        |k| {
            matches!(
                k,
                SyntaxKind::IDENT_TOK | SyntaxKind::DOT_TOK | SyntaxKind::GLOBAL_TOK
            )
        },
    ) {
        return None;
    }
    // `global` leads a rooted name: a keyword token, or (in an attribute's
    // name) an identifier spelled `global` with no backticks.
    let first = li
        .syntax()
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| !t.kind().is_trivia());
    let keyword = first
        .as_ref()
        .is_some_and(|t| t.kind() == SyntaxKind::GLOBAL_TOK);
    let spelled = first
        .as_ref()
        .is_some_and(|t| t.kind() == SyntaxKind::IDENT_TOK && t.text() == "global");
    let mut names = names_of(li);
    if keyword {
        names.insert(0, "global".to_owned());
    }
    if names.is_empty() {
        return None;
    }
    Some((
        if keyword || spelled {
            Form::RootedName
        } else {
            Form::PlainName
        },
        names,
    ))
}

/// A `#` directive's form, by its name: its first identifier, de-quoted
/// (`#``load``` is `#load` to FCS).
fn hash_directive(directive: &SyntaxNode) -> Form {
    let name = directive
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| t.kind() == SyntaxKind::IDENT_TOK);
    match name {
        Some(t)
            if matches!(
                id_text(&t).as_ref(),
                "r" | "reference" | "load" | "I" | "i" | "include"
            ) =>
        {
            Form::ReferenceDirective
        }
        Some(_) | None => Form::OtherDirective,
    }
}

#[derive(Default)]
struct Out {
    namespaces: BTreeSet<Vec<String>>,
    entities: Vec<PickledEntityRow>,
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
}

/// What one attribute's argument says, for the markers that read it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Arg {
    /// No argument, or `()`.
    None,
    /// A string literal.
    Literal(String),
    /// A long identifier (`CompilationRepresentationFlags.ModuleSuffix`).
    LongIdent(Vec<String>),
    /// Anything else.
    Other,
}

/// One attribute, classified: its written name, whether it targets the
/// assembly, and its argument.
struct AttrRead {
    name: Vec<String>,
    assembly: bool,
    arg: Arg,
}

/// An attribute's form and reading, or `None` for a shape outside every
/// form: a child no classifier names (type arguments), an unnamed attribute
/// (`[<>]`), or a target FCS does not know.
fn attribute(attr: &Attribute, forms: &mut BTreeSet<Form>) -> Option<AttrRead> {
    if !consumed(
        attr.syntax(),
        |n| {
            n.kind() == SyntaxKind::ATTRIBUTE_TARGET
                || LongIdent::can_cast(n.kind())
                || Expr::can_cast(n.kind())
        },
        |_| false,
    ) {
        return None;
    }
    let (name_form, name) = long_ident(&attr.type_name()?)?;
    forms.insert(name_form);
    let assembly = match attr.target() {
        None => false,
        Some(t) => match t.text() {
            "assembly" => {
                forms.insert(Form::AssemblyTarget);
                true
            }
            // FCS's `attributeTarget`s that name the carrier.
            "module" | "type" | "return" | "field" | "property" | "method" | "param"
            | "constructor" | "event" => {
                forms.insert(Form::CarrierTarget);
                false
            }
            _ => return None,
        },
    };
    let (form, arg) = match attr.arg() {
        None => (Form::AttributeNoArgument, Arg::None),
        Some(e) => argument(&e),
    };
    forms.insert(form);
    Some(AttrRead {
        name,
        assembly,
        arg,
    })
}

/// An attribute argument's form and what it says.
fn argument(expr: &Expr) -> (Form, Arg) {
    let other = (Form::AttributeOtherArgument, Arg::Other);
    // `()`, which the parser keeps as a constant of its two tokens.
    if let Expr::Const(c) = expr
        && c.syntax()
            .children_with_tokens()
            .filter_map(|el| el.into_token())
            .filter(|t| !t.kind().is_trivia())
            .map(|t| t.kind())
            .eq([SyntaxKind::LPAREN_TOK, SyntaxKind::RPAREN_TOK])
    {
        return (Form::AttributeUnitArgument, Arg::None);
    }
    let Expr::Paren(p) = expr else {
        return other;
    };
    let Some(inner) = p.inner() else {
        return (Form::AttributeUnitArgument, Arg::None);
    };
    if let Expr::Const(c) = &inner {
        let Some(tok) = c.literal() else {
            return other;
        };
        let text = tok.text();
        let kind = tok.kind();
        return if kind == SyntaxKind::STRING_LIT {
            match text.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
                Some(s) if !s.contains('\\') => {
                    (Form::AttributeStringArgument, Arg::Literal(s.to_owned()))
                }
                _ => other,
            }
        } else if kind == SyntaxKind::VERBATIM_STRING_LIT {
            match text.strip_prefix("@\"").and_then(|s| s.strip_suffix('"')) {
                Some(s) => (
                    Form::AttributeVerbatimArgument,
                    Arg::Literal(s.replace("\"\"", "\"")),
                ),
                None => other,
            }
        } else if kind == SyntaxKind::TRIPLE_STRING_LIT {
            match text
                .strip_prefix("\"\"\"")
                .and_then(|s| s.strip_suffix("\"\"\""))
            {
                Some(s) => (
                    Form::AttributeTripleQuotedArgument,
                    Arg::Literal(s.to_owned()),
                ),
                None => other,
            }
        } else {
            other
        };
    }
    if let Expr::LongIdent(l) = &inner {
        return match l.long_ident().as_ref().and_then(long_ident) {
            Some((_, names)) => (Form::AttributeLongIdentArgument, Arg::LongIdent(names)),
            None => other,
        };
    }
    if let Expr::Ident(i) = &inner
        && let Some(t) = i.ident()
    {
        return (
            Form::AttributeLongIdentArgument,
            Arg::LongIdent(vec![id_text(&t).into_owned()]),
        );
    }
    other
}

/// What a set of attribute lists says about each marker.
struct Marks {
    markers: BTreeMap<Marker, Maybe>,
    /// The compiled names an attribute that may be `[<CompiledName>]` gives.
    compiled_names: Vec<String>,
    /// An attribute that may be `[<CompiledName>]` whose argument is no
    /// literal.
    compiled_name_unreadable: bool,
    /// Whether an attribute that may be `[<CompilationRepresentation>]` may
    /// pass `ModuleSuffix`.
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
    fn denotes(&self, name: &[String]) -> Option<&BTreeSet<Marker>> {
        match self {
            MarkerRoutes::Certified(map) => map.get(name),
            MarkerRoutes::Unknown => None,
        }
    }

    /// Whether the attribute written `name` may be `m`.
    fn may_be(&self, name: &[String], m: Marker) -> Maybe {
        match self.denotes(name) {
            Some(set) if set.contains(&m) => Maybe::Yes,
            Some(_) => Maybe::No,
            None => Maybe::Possibly,
        }
    }
}

struct FileWalk<'w> {
    index: usize,
    routes: &'w MarkerRoutes,
    providers: ProviderReferences,
    out: &'w mut Out,
    forms: &'w mut BTreeSet<Form>,
}

/// A declaration list being walked: impl decls or sig decls.
enum Decls {
    Impl(Vec<ModuleDecl>),
    Sig(Vec<SigDecl>),
}

/// The enclosing modules of a scope, innermost last: shared between every
/// scope beneath them, so entering a module copies no path.
struct Encloser {
    name: String,
    parent: Option<Rc<Encloser>>,
}

/// The scope a declaration sits in.
#[derive(Clone)]
struct Scope {
    namespace: Rc<[String]>,
    enclosing: Option<Rc<Encloser>>,
}

impl Scope {
    /// Directly in namespace `namespace`.
    fn root(namespace: &[String]) -> Scope {
        Scope {
            namespace: namespace.into(),
            enclosing: None,
        }
    }

    /// Inside the module `name` of this scope.
    fn inner(&self, name: &str) -> Scope {
        Scope {
            namespace: Rc::clone(&self.namespace),
            enclosing: Some(Rc::new(Encloser {
                name: name.to_owned(),
                parent: self.enclosing.clone(),
            })),
        }
    }

    /// The enclosing modules' names, outermost first: a row's own copy.
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

impl FileWalk<'_> {
    fn unreadable(&self, leaf: Leaf) -> ExistenceUnread {
        ExistenceUnread::Unreadable(self.index, leaf)
    }

    fn walk(&mut self, pf: &ProjectFile) -> Result<(), ExistenceUnread> {
        let root = pf.file.syntax();
        self.assembly_attributes(root)?;
        let modules: Vec<ModuleOrNamespace> = match &pf.file {
            SourceFile::Impl(f) => f.modules().collect(),
            SourceFile::Sig(f) => f.modules().collect(),
        };
        for m in modules {
            let decls = match &pf.file {
                SourceFile::Impl(_) => Decls::Impl(m.decls().collect()),
                SourceFile::Sig(_) => Decls::Sig(m.sig_decls().collect()),
            };
            // The header: its keyword, access and `rec` tokens, its name,
            // its attribute lists, and its declarations.
            if !consumed(
                m.syntax(),
                |n| {
                    LongIdent::can_cast(n.kind())
                        || AttributeList::can_cast(n.kind())
                        || ModuleDecl::can_cast(n.kind())
                        || SigDecl::can_cast(n.kind())
                },
                |k| {
                    matches!(
                        k,
                        SyntaxKind::MODULE_TOK
                            | SyntaxKind::NAMESPACE_TOK
                            | SyntaxKind::ACCESS_TOK
                            | SyntaxKind::REC_TOK
                            | SyntaxKind::GLOBAL_TOK
                            // Separators between declarations.
                            | SyntaxKind::SEMI_TOK
                            | SyntaxKind::SEMISEMI_TOK
                    )
                },
            ) {
                return Err(self.unreadable(Leaf::FileHeader));
            }
            match m.kind() {
                ModuleOrNamespaceKind::GlobalNamespace => {
                    self.forms.insert(Form::GlobalNamespace);
                    self.decls(&Scope::root(&[]), &decls, m.is_rec())?;
                }
                ModuleOrNamespaceKind::DeclaredNamespace => {
                    self.forms.insert(Form::Namespace);
                    let ns = self.name(m.long_id())?;
                    self.namespace(&ns);
                    self.decls(&Scope::root(&ns), &decls, m.is_rec())?;
                }
                ModuleOrNamespaceKind::NamedModule => {
                    self.forms.insert(Form::NamedModule);
                    let segments = self.name(m.long_id())?;
                    let attrs: Vec<AttributeList> = m.attributes().collect();
                    let (name, ns) = segments.split_last().expect("a name is not empty");
                    self.namespace(ns);
                    // FCS reads `module A.M` as a namespace holding one
                    // module: no type shares its list.
                    self.module(
                        &Scope::root(ns),
                        name,
                        &attrs,
                        &decls,
                        m.is_rec(),
                        Maybe::No,
                    )?;
                }
                ModuleOrNamespaceKind::Anon => {
                    self.forms.insert(Form::AnonymousModule);
                    let segments = pf
                        .qnof
                        .anonymous_module_segments()
                        .ok_or(ExistenceUnread::AnonymousModuleName(self.index))?;
                    let (name, ns) = segments.split_last().expect("a name is not empty");
                    self.namespace(ns);
                    self.module(&Scope::root(ns), name, &[], &decls, m.is_rec(), Maybe::No)?;
                }
            }
        }
        Ok(())
    }

    /// A long identifier's names, its form recorded.
    fn name(&mut self, li: Option<LongIdent>) -> Result<Vec<String>, ExistenceUnread> {
        let (form, names) = li
            .as_ref()
            .and_then(long_ident)
            .ok_or_else(|| self.unreadable(Leaf::Name))?;
        self.forms.insert(form);
        Ok(names)
    }

    /// Record namespace `ns` and its prefixes.
    fn namespace(&mut self, ns: &[String]) {
        for k in 1..=ns.len() {
            self.out.namespaces.insert(ns[..k].to_vec());
        }
    }

    /// Every attribute of the file FCS may read as assembly-level: one with
    /// an `assembly:` target anywhere, and any in a standalone attribute
    /// declaration (`[<A>]` before `do ()`), which FCS checks against the
    /// top-level targets and keeps as the assembly's when the attribute
    /// allows it (`[<AutoOpen>]` and `[<TypeProviderAssembly>]` do). An
    /// `[<AutoOpen>]` path, or a reason A is unread.
    fn assembly_attributes(&mut self, root: &SyntaxNode) -> Result<(), ExistenceUnread> {
        for list in root.descendants().filter_map(AttributeList::cast) {
            let standalone = list
                .syntax()
                .ancestors()
                .any(|a| a.kind() == SyntaxKind::ATTRIBUTES_DECL);
            for read in self.attribute_list(&list)? {
                if !(read.assembly || standalone) {
                    continue;
                }
                if self.routes.may_be(&read.name, Marker::TypeProviderAssembly) != Maybe::No {
                    return Err(ExistenceUnread::TypeProvider(self.index));
                }
                match (self.routes.may_be(&read.name, Marker::AutoOpen), read.arg) {
                    (Maybe::No, _) | (_, Arg::None) => {}
                    (Maybe::Yes, Arg::Literal(path)) => self.out.auto_opens.push(path),
                    (Maybe::Possibly, Arg::Literal(path)) => {
                        self.out.auto_opens.push(path);
                        self.out
                            .approximations
                            .insert(Approximation::UncertainAttribute);
                    }
                    (Maybe::Yes | Maybe::Possibly, Arg::LongIdent(_) | Arg::Other) => {
                        return Err(ExistenceUnread::UnreadableAutoOpen(self.index));
                    }
                }
            }
        }
        Ok(())
    }

    /// An attribute list's attributes, each classified.
    fn attribute_list(&mut self, list: &AttributeList) -> Result<Vec<AttrRead>, ExistenceUnread> {
        if !consumed(
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
        ) {
            return Err(self.unreadable(Leaf::Attribute));
        }
        list.attributes()
            .map(|a| {
                attribute(&a, self.forms)
                    .ok_or(ExistenceUnread::Unreadable(self.index, Leaf::Attribute))
            })
            .collect()
    }

    /// What `lists` on an entity say. An entity keeps every attribute of its
    /// lists, whatever its target (FCS gives a `return:` one to the carrier
    /// on an entity).
    fn marks(&mut self, lists: &[AttributeList]) -> Result<Marks, ExistenceUnread> {
        let mut marks = Marks {
            markers: BTreeMap::new(),
            compiled_names: Vec::new(),
            compiled_name_unreadable: false,
            module_suffix: Maybe::No,
            uncertain: false,
        };
        for list in lists {
            for read in self.attribute_list(list)? {
                for m in Marker::ALL {
                    let maybe = self.routes.may_be(&read.name, m);
                    if maybe == Maybe::No {
                        continue;
                    }
                    if maybe == Maybe::Possibly {
                        marks.uncertain = true;
                    }
                    let slot = marks.markers.entry(m).or_insert(Maybe::No);
                    *slot = slot.or(maybe);
                    match m {
                        Marker::CompiledName => match &read.arg {
                            Arg::Literal(s) => marks.compiled_names.push(s.clone()),
                            // `[<CompiledName>]` with no argument does not
                            // compile; any other attribute with none names
                            // nothing.
                            Arg::None => {}
                            Arg::LongIdent(_) | Arg::Other => marks.compiled_name_unreadable = true,
                        },
                        Marker::CompilationRepresentation => {
                            let suffix = match &read.arg {
                                Arg::None | Arg::Literal(_) => Maybe::No,
                                // `CompilationRepresentationFlags.ModuleSuffix`,
                                // or an alias of it: a flag named anything
                                // else is no suffix.
                                Arg::LongIdent(names) => {
                                    if names.last().is_some_and(|n| n == "ModuleSuffix") {
                                        maybe
                                    } else {
                                        Maybe::No
                                    }
                                }
                                // `A ||| B`, a value bound elsewhere.
                                Arg::Other => Maybe::Possibly,
                            };
                            marks.module_suffix = marks.module_suffix.or(suffix);
                        }
                        Marker::AutoOpen | Marker::Measure | Marker::TypeProviderAssembly => {}
                    }
                }
            }
        }
        Ok(marks)
    }

    /// The declaration list `decls` in `scope`.
    fn decls(&mut self, scope: &Scope, decls: &Decls, is_rec: bool) -> Result<(), ExistenceUnread> {
        let type_names = type_names(decls, self.routes);
        match decls {
            Decls::Impl(ds) => {
                for d in ds {
                    match d {
                        ModuleDecl::NestedModule(m) => {
                            let inner = Decls::Impl(m.decls().collect());
                            self.nested_module(
                                scope,
                                m.syntax(),
                                m.long_id(),
                                &m.attributes().collect::<Vec<_>>(),
                                &inner,
                                m.is_rec() || is_rec,
                                &type_names,
                            )?;
                        }
                        ModuleDecl::Types(t) => {
                            for defn in t.defns() {
                                self.type_defn(scope, &defn)?;
                            }
                        }
                        ModuleDecl::Exception(e) => self.exception(scope, e)?,
                        // Extension members, `let`s and `extern`s are A's
                        // `ExtensionNames`'; the rest declares no entity.
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
            Decls::Sig(ds) => {
                for d in ds {
                    match d {
                        SigDecl::NestedModule(m) => {
                            let inner = Decls::Sig(m.sig_decls().collect());
                            self.nested_module(
                                scope,
                                m.syntax(),
                                m.long_id(),
                                &m.attributes().collect::<Vec<_>>(),
                                &inner,
                                m.is_rec() || is_rec,
                                &type_names,
                            )?;
                        }
                        SigDecl::Types(t) => {
                            for defn in t.defns() {
                                self.type_defn(scope, &defn)?;
                            }
                        }
                        SigDecl::Exception(e) => self.exception(scope, e)?,
                        SigDecl::Val(_)
                        | SigDecl::Open(_)
                        | SigDecl::ModuleAbbrev(_)
                        | SigDecl::HashDirective(_) => {}
                    }
                }
            }
        }
        Ok(())
    }

    /// `module M = …` in a declaration list whose types are `type_names`.
    #[allow(clippy::too_many_arguments)]
    fn nested_module(
        &mut self,
        scope: &Scope,
        node: &SyntaxNode,
        long_id: Option<LongIdent>,
        attrs: &[AttributeList],
        decls: &Decls,
        is_rec: bool,
        type_names: &BTreeMap<String, Maybe>,
    ) -> Result<(), ExistenceUnread> {
        if !consumed(
            node,
            |n| {
                LongIdent::can_cast(n.kind())
                    || AttributeList::can_cast(n.kind())
                    || ModuleDecl::can_cast(n.kind())
                    || SigDecl::can_cast(n.kind())
            },
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
        let names = self.name(long_id)?;
        let [name] = names.as_slice() else {
            return Err(self.unreadable(Leaf::NestedModule));
        };
        let has_decls = match decls {
            Decls::Impl(ds) => !ds.is_empty(),
            Decls::Sig(ds) => !ds.is_empty(),
        };
        self.forms.insert(if has_decls {
            Form::NestedModule
        } else {
            Form::EmptyNestedModule
        });
        let beside_type = type_names.get(name).copied().unwrap_or(Maybe::No);
        self.module(scope, name, attrs, decls, is_rec, beside_type)
    }

    /// A module entity named `name` (`beside_type`: whether a type of its
    /// name in its own list may suffix it), and its contents.
    fn module(
        &mut self,
        scope: &Scope,
        name: &str,
        attrs: &[AttributeList],
        decls: &Decls,
        is_rec: bool,
        beside_type: Maybe,
    ) -> Result<(), ExistenceUnread> {
        let marks = self.marks(attrs)?;
        // Canonical spelling strips one `Module`, so the suffix moves a fact
        // only on a name already ending in it.
        let logical = if name.len() > "Module".len() && name.ends_with("Module") {
            match marks.module_suffix.or(beside_type) {
                Maybe::Yes => format!("{name}Module"),
                Maybe::No => name.to_owned(),
                Maybe::Possibly => return Err(ExistenceUnread::ModuleSuffix(self.index)),
            }
        } else {
            name.to_owned()
        };
        self.decls(&scope.inner(&logical), decls, is_rec)?;
        // `[<CompiledName>]` does not rename a module.
        self.entity(scope, &logical, &[PickledEntityKind::Module], &marks, false)
    }

    /// Emit an entity's rows: one per kind and compiled-name reading. Its
    /// compiled name is its logical name, or, when `honours_compiled_name`,
    /// a name an attribute that may be `[<CompiledName>]` gives.
    fn entity(
        &mut self,
        scope: &Scope,
        logical: &str,
        kinds: &[PickledEntityKind],
        marks: &Marks,
        honours_compiled_name: bool,
    ) -> Result<(), ExistenceUnread> {
        if honours_compiled_name && marks.compiled_name_unreadable {
            return Err(ExistenceUnread::UnreadableCompiledName(self.index));
        }
        // The logical spelling always: a row whose compiled name is the
        // logical one holds no path the renamed row lacks.
        let mut compiled: BTreeSet<String> = BTreeSet::from([logical.to_owned()]);
        if honours_compiled_name {
            compiled.extend(marks.compiled_names.iter().cloned());
        }
        let auto_open = marks.get(Marker::AutoOpen);
        if marks.uncertain
            && (auto_open == Maybe::Possibly
                || (compiled.len() > 1 && marks.get(Marker::CompiledName) == Maybe::Possibly))
        {
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
        let enclosing = scope.enclosing();
        for &kind in kinds {
            for c in &compiled {
                self.out.entities.push(PickledEntityRow {
                    namespace: scope.namespace.to_vec(),
                    enclosing: enclosing.clone(),
                    logical_name: logical.to_owned(),
                    compiled_name: c.clone(),
                    kind,
                    public: true,
                    auto_open: auto_open != Maybe::No,
                    extension: false,
                });
            }
        }
        Ok(())
    }

    fn type_defn(&mut self, scope: &Scope, defn: &TypeDefn) -> Result<(), ExistenceUnread> {
        // The head's keyword, access, name, type parameters, constraints,
        // attributes and primary constructor; the representation and members
        // (read only for an abbreviation's target), and `with … end`.
        if !consumed(
            defn.syntax(),
            |n| {
                let k = n.kind();
                AttributeList::can_cast(k)
                    || LongIdent::can_cast(k)
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
            self.forms.insert(Form::TupleAugmentation);
            return Ok(());
        }
        if is_augmentation(defn) {
            self.forms.insert(Form::Augmentation);
            return Ok(());
        }
        let names = self.name(defn.long_id())?;
        let [name] = names.as_slice() else {
            self.forms.insert(Form::DottedType);
            return Err(self.unreadable(Leaf::TypeDefinition));
        };
        let generic = defn
            .typar_decls()
            .is_some_and(|d| d.typars().next().is_some());
        self.forms.insert(if generic {
            Form::GenericType
        } else {
            Form::Type
        });
        let attrs: Vec<AttributeList> = defn.attributes().collect();
        let marks = self.marks(&attrs)?;
        let kinds: Vec<PickledEntityKind> = match defn.repr() {
            Some(TypeDefnRepr::Abbrev(a)) => match a.ty() {
                Some(target) => self.abbreviation_kinds(name, generic, &target, &marks)?,
                None => return Err(self.unreadable(Leaf::AbbreviationTarget)),
            },
            Some(
                TypeDefnRepr::Record(_)
                | TypeDefnRepr::Union(_)
                | TypeDefnRepr::Enum(_)
                | TypeDefnRepr::ObjectModel(_)
                | TypeDefnRepr::Delegate(_)
                | TypeDefnRepr::InlineIl(_),
            )
            | None => vec![PickledEntityKind::Type],
        };
        self.entity(scope, name, &kinds, &marks, true)
    }

    /// What `type name = target` may be: an abbreviation, or (`target` one
    /// identifier) FCS's single-case union when it names no type in scope,
    /// or itself (`type X = X`, a union unless a unit of measure). The
    /// abbreviation reading is emitted alone only where FCS's is certain: a
    /// target FSharp.Core declares (open in every file).
    fn abbreviation_kinds(
        &mut self,
        name: &str,
        generic: bool,
        target: &Type,
        marks: &Marks,
    ) -> Result<Vec<PickledEntityKind>, ExistenceUnread> {
        let target = abbreviation_target(target, name, generic);
        self.forms.insert(target.form());
        let abbreviation = vec![PickledEntityKind::Abbreviation];
        let either = vec![PickledEntityKind::Abbreviation, PickledEntityKind::Type];
        let measure = marks.get(Marker::Measure);
        let provider = self.providers == ProviderReferences::Possible;
        Ok(match target {
            Target::StaticArgument => return Err(ExistenceUnread::TypeProvider(self.index)),
            Target::Named | Target::SingleIdent | Target::SelfNamed | Target::FSharpCore
                if provider =>
            {
                return Err(ExistenceUnread::TypeProvider(self.index));
            }
            Target::SelfNamed => match measure {
                Maybe::No => vec![PickledEntityKind::Type],
                Maybe::Yes => abbreviation,
                Maybe::Possibly => {
                    self.out
                        .approximations
                        .insert(Approximation::UncertainAttribute);
                    either
                }
            },
            Target::SingleIdent if measure != Maybe::Yes => {
                self.out
                    .approximations
                    .insert(Approximation::AbbreviationOrUnion);
                either
            }
            Target::FSharpCore | Target::SingleIdent | Target::Structural | Target::Named => {
                abbreviation
            }
        })
    }

    fn exception(&mut self, scope: &Scope, e: &ExceptionDefnDecl) -> Result<(), ExistenceUnread> {
        if !consumed(
            e.syntax(),
            |n| {
                let k = n.kind();
                AttributeList::can_cast(k)
                    || UnionCase::can_cast(k)
                    || LongIdent::can_cast(k)
                    || MemberDefn::can_cast(k)
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
        self.forms.insert(if e.abbrev_path().is_some() {
            Form::ExceptionAbbreviation
        } else {
            Form::Exception
        });
        let attrs: Vec<AttributeList> = e.attributes().collect();
        let marks = self.marks(&attrs)?;
        self.entity(scope, &name, &[PickledEntityKind::Exception], &marks, false)
    }
}

/// The type names of a declaration list that suffix a module of the same
/// name (`TypeNamesInNonMutRecDecls`, `TypeNamesInMutRecDecls`,
/// `TypeNamesInNonMutRecSigDecls`, `CheckDeclarations.fs:2773-2809`): every
/// type that is no augmentation, in an implementation only when each of its
/// type parameters is a unit of measure (one with an attribute may be), in a
/// signature only with none.
fn type_names(decls: &Decls, routes: &MarkerRoutes) -> BTreeMap<String, Maybe> {
    let mut names: BTreeMap<String, Maybe> = BTreeMap::new();
    let mut add = |defn: TypeDefn, signature: bool| {
        if is_augmentation(&defn) {
            return;
        }
        let Some(name) = defn.long_id().and_then(|li| li.idents().last()) else {
            return;
        };
        let typars: Vec<_> = defn
            .typar_decls()
            .map(|d| d.typars().collect())
            .unwrap_or_default();
        let counts = if typars.is_empty() {
            Maybe::Yes
        } else if signature {
            Maybe::No
        } else {
            // Each must be `[<Measure>]`.
            typars
                .iter()
                .map(|t| {
                    t.attributes()
                        .flat_map(|l| l.attributes().collect::<Vec<_>>())
                        .filter_map(|a| a.type_name().map(|li| names_of(&li)))
                        .map(|n| routes.may_be(&n, Marker::Measure))
                        .fold(Maybe::No, Maybe::or)
                })
                .fold(Maybe::Yes, |all, t| match (all, t) {
                    (Maybe::No, _) | (_, Maybe::No) => Maybe::No,
                    (Maybe::Yes, Maybe::Yes) => Maybe::Yes,
                    _ => Maybe::Possibly,
                })
        };
        let slot = names
            .entry(id_text(&name).into_owned())
            .or_insert(Maybe::No);
        *slot = slot.or(counts);
    };
    match decls {
        Decls::Impl(ds) => {
            for d in ds {
                if let ModuleDecl::Types(t) = d {
                    t.defns().for_each(|defn| add(defn, false));
                }
            }
        }
        Decls::Sig(ds) => {
            for d in ds {
                if let SigDecl::Types(t) = d {
                    t.defns().for_each(|defn| add(defn, true));
                }
            }
        }
    }
    names
}

fn is_augmentation(defn: &TypeDefn) -> bool {
    matches!(defn.repr(), Some(TypeDefnRepr::ObjectModel(om)) if om.is_augmentation())
        || defn.tuple_type_head().is_some()
        // A signature's augmentation (`type T with member …`) has no
        // representation, just the `with` directly on the definition.
        || (defn.repr().is_none()
            && defn
                .syntax()
                .children_with_tokens()
                .filter_map(|el| el.into_token())
                .any(|t| t.kind() == SyntaxKind::WITH_TOK))
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

/// What an abbreviation's target is, as its kinds read it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Target {
    SelfNamed,
    FSharpCore,
    SingleIdent,
    Structural,
    Named,
    StaticArgument,
}

impl Target {
    fn form(self) -> Form {
        match self {
            Target::SelfNamed => Form::SelfNamedTarget,
            Target::FSharpCore => Form::FSharpCoreTarget,
            Target::SingleIdent => Form::SingleIdentTarget,
            Target::Structural => Form::StructuralTarget,
            Target::Named => Form::NamedTarget,
            Target::StaticArgument => Form::StaticArgumentTarget,
        }
    }
}

/// An abbreviation target's reading (`name` the abbreviation's own,
/// `generic` whether it has type parameters).
fn abbreviation_target(ty: &Type, name: &str, generic: bool) -> Target {
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
        return Target::StaticArgument;
    }
    match ty {
        Type::Paren(p) => match p.inner() {
            Some(inner) => abbreviation_target(&inner, name, generic),
            None => Target::Named,
        },
        Type::LongIdent(t) => {
            let Some((_, names)) = t.long_ident().as_ref().and_then(long_ident) else {
                return Target::Named;
            };
            match names.as_slice() {
                // `type Foo<'a> = Foo` may abbreviate another `Foo` of no
                // arity.
                [single] if single == name && !generic => Target::SelfNamed,
                [single] if FSHARP_CORE_TYPE_NAMES.contains(&single.as_str()) => Target::FSharpCore,
                [_] => Target::SingleIdent,
                _ => Target::Named,
            }
        }
        Type::Tuple(_)
        | Type::Fun(_)
        | Type::Array(_)
        | Type::Var(_)
        | Type::Anon(_)
        | Type::AnonRecd(_) => Target::Structural,
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
        | Type::SignatureParameter(_) => Target::Named,
    }
}

/// Certify `routes` from spelling: each written name in `files` denotes
/// the marker whose type name it spells (with or without the `Attribute`
/// suffix) under a qualifier that is a suffix of that marker's namespace
/// path, and nothing else. A name some type of A's own is declared as is
/// omitted: it may resolve to A's type, whose full name the walk does not
/// know. A test's certificate and the corpus's: sound for the tests' own
/// producers, which reference no abbreviation of a marker.
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
        for e in root.descendants().filter_map(ExceptionDefnDecl::cast) {
            if let Some(t) = e.union_case().and_then(|c| c.ident()) {
                declared.insert(id_text(&t).into_owned());
            }
        }
        for list in root.descendants().filter_map(AttributeList::cast) {
            for attr in list.attributes() {
                if let Some(li) = attr.type_name() {
                    let name = names_of(&li);
                    if !name.is_empty() {
                        written.insert(name);
                    }
                }
            }
        }
    }
    let mut map = BTreeMap::new();
    for name in written {
        let (last, qualifier) = name.split_last().expect("written names are not empty");
        // `global.` roots a fully qualified name: its qualifier must then be
        // the whole namespace.
        let (qualifier, rooted) = match qualifier.split_first() {
            Some((first, rest)) if first == "global" => (rest, true),
            _ => (qualifier, false),
        };
        // `[<X>]` denotes a type named `X` or `XAttribute`: a type of A's own
        // of either name may be any marker's abbreviation.
        let stem = last.strip_suffix("Attribute").unwrap_or(last);
        if [
            stem.to_owned(),
            format!("{stem}Attribute"),
            last.clone(),
            format!("{last}Attribute"),
        ]
        .iter()
        .any(|n| declared.contains(n))
        {
            continue;
        }
        let mut set = BTreeSet::new();
        for m in Marker::ALL {
            let full = m.full_name();
            let (type_name, ns) = full.split_last().expect("a full name is not empty");
            let spelled = last == type_name || format!("{last}Attribute") == *type_name;
            let qualified = qualifier.len() <= ns.len()
                && (!rooted || qualifier.len() == ns.len())
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
