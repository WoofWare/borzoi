//! A referenced F# project's **existence surface**, read from its source
//! ([`source_existence`]): rows in the currency of
//! [`borzoi_assembly::existence`], so the extension gate's existence
//! questions read a project reference as they read a DLL.
//!
//! The function is pure. Its input is a producer project A as the caller
//! evaluated it ([`Producer`]): A's Compile items, parsed under A's own
//! defines and language version, and what the caller knows of A's reference
//! environment ([`MarkerRoutes`]). Its output ([`SourceExistence`]) is either
//! the rows, or `Unread` with the reason A's surface cannot be known.
//!
//! # Who reads it, and the claim
//!
//! This surface serves the **existence consumers only**: the
//! [`crate::assembly_env::existence`] set, which `add_index` builds from an
//! [`ExistenceIndex`], and the open certification and extension-scope gate
//! that question it. What that set reads of a row is all the walk derives:
//!
//! - an entity's namespace, enclosers and names, each **canonical** (a
//!   generic arity suffix and one trailing `Module` stripped), its logical
//!   and compiled names alike;
//! - whether it is a namespace, an abbreviation or anything else;
//! - its `[<AutoOpen>]` flag, and on an abbreviation its `[<Extension>]` one;
//! - an extension row's place, each of its names (a call answers to a name
//!   or to its accessor-stripped stem), and its staticness;
//! - the assembly-level `[<AutoOpen("…")>]` paths, as a set.
//!
//! Every question the set answers is monotone: a fact more only ever makes
//! it say "something may be there". So the claim is **containment**: every
//! fact the set holds of FCS's CCU for A (its in-memory signature, and the
//! pickle of the DLL FCS compiles from it) it also holds of these rows.
//! `source_existence_diff` holds that on the set's own facts
//! (`test_support::existence_facts`), and pins the surplus, which is what a
//! superset costs the gate. No consumer needs a field exactly, so none is
//! claimed exact; where a surplus could make the gate useless (one
//! abbreviation marked `[<Extension>]` or `[<AutoOpen>]` makes every name a
//! possible extension), the walk names the [`Approximation`] it came from.
//!
//! Fields no existence question reads are left as constants: an entity's
//! accessibility (`public` is always `true`), its kind beyond namespace and
//! abbreviation (a measure, an exception and a module are all `Type` or
//! `Module`), and the `[<Extension>]` flag FCS infers on a type or module
//! from its members. **A later stage that reads more of a source producer
//! (stage 2a's shells read accessibility and kinds) must derive those fields
//! itself, with its own exactness claim and grading**: nothing here is an
//! exact source for them.
//!
//! # Attributes
//!
//! Whether an attribute is `[<AutoOpen>]`, `[<Extension>]`, `[<Measure>]`,
//! `[<CompiledName>]`, `[<CLIEvent>]` or `[<TypeProviderAssembly>]` depends on
//! what its name resolves to, and A's references can route any name to any of
//! them (an abbreviation) or away from them (a shadow). The walk does not
//! resolve: the caller states what each written attribute name denotes
//! ([`MarkerRoutes::Certified`]), or nothing at all
//! ([`MarkerRoutes::Unknown`]), in which case every attribute may denote every
//! marker.
//!
//! Whether a type application, or a bare type name, is a generative type
//! provider's (`type T = Gen<N>`, `N` a literal) depends on whether one of A's
//! references is a provider: the caller states that too
//! ([`ProviderReferences`]).
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

use borzoi_assembly::existence::{
    ExistenceIndex, ExtensionRow, IndexLayer, PickleLayer, PickledEntityKind, PickledEntityRow,
};
use borzoi_cst::syntax::{
    AstNode, Attribute, AttributeList, Binding, Expr, ImplicitCtor, LongIdent, MemberDefn,
    MemberLetBindings, ModuleDecl, ModuleOrNamespace, ModuleOrNamespaceKind, Pat, SigDecl,
    SyntaxKind, SyntaxNode, TextSize, Type, TypeDefn, TypeDefnRepr,
};

use crate::FcsRange;
use crate::def::id_text;
use crate::recovery::SyntaxRecovery;
use crate::resolve::extension_names::{
    MemberRole, MemberShape, MemberVal, active_pattern_name, member_shape, val_sig_name,
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
    /// One may be: an abbreviation of a prefix type application may be a
    /// generative provider's.
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
    /// `Microsoft.FSharp.Core.CompilerServices.TypeProviderAssemblyAttribute`.
    TypeProviderAssembly,
    /// `Microsoft.FSharp.Core.CLIEventAttribute`.
    CliEvent,
}

impl Marker {
    /// Every marker.
    pub const ALL: [Marker; 6] = [
        Marker::AutoOpen,
        Marker::Extension,
        Marker::Measure,
        Marker::CompiledName,
        Marker::TypeProviderAssembly,
        Marker::CliEvent,
    ];

    /// The marker's full name, its namespace's segments then its type name.
    pub fn full_name(self) -> &'static [&'static str] {
        match self {
            Marker::AutoOpen => &["Microsoft", "FSharp", "Core", "AutoOpenAttribute"],
            Marker::Extension => &[
                "System",
                "Runtime",
                "CompilerServices",
                "ExtensionAttribute",
            ],
            Marker::Measure => &["Microsoft", "FSharp", "Core", "MeasureAttribute"],
            Marker::CompiledName => &["Microsoft", "FSharp", "Core", "CompiledNameAttribute"],
            Marker::TypeProviderAssembly => &[
                "Microsoft",
                "FSharp",
                "Core",
                "CompilerServices",
                "TypeProviderAssemblyAttribute",
            ],
            Marker::CliEvent => &["Microsoft", "FSharp", "Core", "CLIEventAttribute"],
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
    /// and only widens the surplus. An empty set certifies that the name
    /// denotes no marker.
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
    /// target, or with [`ProviderReferences::Possible`] any prefix type
    /// application there), or A may be one (an assembly attribute that may
    /// be `[<TypeProviderAssembly>]`): FCS then reads A's DLL, not its
    /// source.
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
    /// The rows exceed `MAX_ROWS`: each module whose name ends in `Module`
    /// doubles the paths under it.
    TooManyReadings,
    /// A type's `[<Extension>]` `let`, whose compiled name may carry its
    /// line (`f@7`), in a file whose `#line` directives may move the lines
    /// FCS reports.
    LineDirective(usize),
    /// A leaf form outside the certified domain ([`LEAF_FORMS`]).
    OutsideDomain(usize, Leaf),
}

/// A syntax leaf the walk interprets, whose forms it certifies one by one
/// ([`LEAF_FORMS`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Leaf {
    /// A type definition's name.
    TypeHead,
    /// An augmentation's head: the type it extends.
    AugmentationHead,
    /// An abbreviation's target, where a reference may be a type provider.
    ProvidedTarget,
    /// An `[<Extension>]` binding's pattern: the values it names.
    BindingHead,
}

/// What the walk does with one form of a [`Leaf`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Read, and graded by `source_existence_diff`.
    Read,
    /// Declined.
    Declined,
}

/// One form of a leaf: a file that writes it, and the walk's verdict. The
/// table is the certified domain: `source_existence_domain` grades every
/// `Read` row against FCS and holds the walk to every row's verdict, so the
/// predicate and the forms it admits cannot drift apart. A form not in the
/// table is outside the domain only if the walk declines it; a leaf the walk
/// reads gains a row for each form it reads.
#[derive(Debug, Clone, Copy)]
pub struct LeafForm {
    pub leaf: Leaf,
    pub form: &'static str,
    /// A producer file writing the form.
    pub source: &'static str,
    /// Whether the producer's references may hold a type provider.
    pub providers: ProviderReferences,
    pub verdict: Verdict,
}

/// The certified domain of each leaf ([`LeafForm`]).
pub const LEAF_FORMS: &[LeafForm] = &[
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "value",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet f = fun (s: string) -> s\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "function",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet f (s: string) = s\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "operator",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet (+++) (a: string) (b: string) = a + b\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "active_pattern",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet (|Even|Odd|) (n: int) = if n % 2 = 0 then Even else Odd\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "nullary_active_pattern",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet (|Zero|_|) = function 0 -> Some () | _ -> None\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "parenthesised_typed",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet (f: string -> string) = id\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "upper_case_head",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet Shout (s: string) = s\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "tuple",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet a, b = 1, 2\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "as",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet ((|Foo|_|) as f) = fun (x: int) -> Some x\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "record",
        source: "module D\ntype R = { A: int }\n[<System.Runtime.CompilerServices.Extension>]\nlet { A = a } = { A = 1 }\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "list",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet [ a; b ] = [ 1; 2 ]\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "named_fields",
        source: "module D\ntype U = C of F: int\n[<System.Runtime.CompilerServices.Extension>]\nlet C(F = x) = C 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::BindingHead,
        form: "nested_tuple",
        source: "module D\n[<System.Runtime.CompilerServices.Extension>]\nlet (a, (b, c)) = (1, (2, 3))\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::TypeHead,
        form: "single",
        source: "namespace D\ntype T = { X: int }\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::TypeHead,
        form: "dotted",
        source: "module D\ntype X.Y = { N: int }\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "local",
        source: "module D\ntype R = { X: int }\ntype R with\n    member r.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "qualified",
        source: "module D\ntype System.String with\n    member s.M() = 1\n",
        providers: ProviderReferences::None,
        // No written parameters: the head does not bound the arity in the
        // extension's compiled names.
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "arity_less_generic",
        source: "module D\ntype list with\n    member xs.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "qualified_generic",
        source: "module D\ntype System.Collections.Generic.List<'T> with\n    member l.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    // Fewer parameters than the type has: FCS rejects it, and the domain
    // grid shows whether its recovery keeps the written arity.
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "under_written_arity",
        source: "module D\ntype System.Collections.Generic.Dictionary<'K> with\n    member d.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "generic",
        source: "module D\ntype List<'T> with\n    member l.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "tuple",
        source: "module D\ntype (int * int) with\n    member x.M() = 1\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "module_alias",
        source: "module rec D\nmodule Alias = D\ntype T<'a>() =\n    member _.X = 1\ntype Alias.T<'a> with\n    [<System.Runtime.CompilerServices.Extension>]\n    static member E(s: string) = s\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::AugmentationHead,
        form: "global",
        source: "namespace rec D\ntype C() = class end\ntype global.D.C with\n    static member E(s: string) = s\n",
        providers: ProviderReferences::None,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "tuple",
        source: "namespace D\ntype T = int * int\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "function",
        source: "namespace D\ntype T = int -> int\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "array",
        source: "namespace D\ntype T = int[]\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "variable",
        source: "namespace D\ntype T<'a> = 'a\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "anonymous_record",
        source: "namespace D\ntype T = {| X: int |}\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "wildcard",
        source: "namespace D\ntype T<'a> = _\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Read,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "named",
        source: "namespace D\ntype T = int\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "postfix",
        source: "namespace D\ntype T = int list\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Declined,
    },
    LeafForm {
        leaf: Leaf::ProvidedTarget,
        form: "prefix",
        source: "namespace D\ntype T = Map<int, int>\n",
        providers: ProviderReferences::Possible,
        verdict: Verdict::Declined,
    },
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
    /// An augmentation that may be intrinsic or optional: both readings'
    /// rows.
    AugmentationKind,
    /// A module whose name ends in `Module`: FCS may add the suffix
    /// (`FooModuleModule`), which the set's canonical spelling does not
    /// strip, so both readings' paths.
    ModuleSuffix,
    /// An `[<Extension>]` binding whose pattern is not a single name.
    BindingPattern,
    /// A declaration FCS rejects in its position, read as written.
    RejectedShape,
    /// A type's `[<Extension>]` `let`: its name, and every name FCS may
    /// mangle it to (`f@7`, `f@7-1`, …) when an earlier name of the type
    /// took it.
    ClassLetName,
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
    /// The paths an assembly-level `[<AutoOpen("…")>]` may name: FCS's
    /// `GetAutoOpenAttributes`, or more.
    pub assembly_auto_opens: Vec<String>,
    /// Where the rows may hold more than FCS's.
    pub approximations: BTreeSet<Approximation>,
    /// Every abbreviation row that may lend (marked, or possibly marked,
    /// `[<AutoOpen>]` or `[<Extension>]`), with the approximations that may
    /// have made it: a surplus lender is accounted for at its own path.
    pub lender_sources: Vec<LenderSource>,
}

/// An abbreviation row that may lend, and the approximations that may have
/// made it ([`SourceSurface::lender_sources`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LenderSource {
    pub namespace: Vec<String>,
    pub enclosing: Vec<String>,
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

/// Declare [`Channel`] and [`Channel::ALL`] together, so that a channel
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
    /// The `Module` suffix FCS adds to a module beside a type of its name,
    /// or under `[<CompilationRepresentation(ModuleSuffix)>]`: canonical
    /// spelling strips it, but for a name already ending in `Module`.
    ModuleSuffix,
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
    /// `[<Extension>]` on an abbreviation or a member.
    ExtensionAttribute,
    /// `[<CompiledName("…")>]` on a type (modules and exceptions ignore it).
    CompiledNameAttribute,
    /// An attribute's explicit target: a `return:` one is the return
    /// value's, any other the carrier's.
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
    /// A type's `let` under `[<Extension>]`, whose name FCS mangles when an
    /// earlier name of the type took it.
    ClassLet,
    /// A `#line` directive in a file with a type's `[<Extension>]` `let`.
    LineDirective,
    /// A leaf form outside the certified domain ([`LEAF_FORMS`]).
    OutsideDomain,
    /// A member or declaration the walk cannot name.
    UnnamedDeclaration,
    /// A member FCS rejects in an augmentation.
    RejectedShape,
    /// More readings than the walk will emit.
    ReadingsBudget,
    /// An entity's accessibility, combined with its enclosers'.
    Accessibility,
    /// A generic type's arity suffix, which units of measure do not count.
    GenericArity,
    /// `[<Measure>] type m`, and an exception's or a module's kind.
    EntityKind,
    /// The `[<Extension>]` FCS adds to a type or module from its members.
    ImpliedExtensionAttribute,
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
            | Channel::UnnamedDeclaration
            | Channel::ReadingsBudget
            | Channel::LineDirective
            | Channel::OutsideDomain => Treatment::Declined,
            Channel::Defines | Channel::LanguageVersion | Channel::GeneratedItems => {
                Treatment::Caller
            }
            Channel::SignaturePair => Treatment::Approximated(A::SignaturePair),
            Channel::ModuleSuffix => Treatment::Approximated(A::ModuleSuffix),
            Channel::AbbreviationOrUnion => Treatment::Approximated(A::AbbreviationOrUnion),
            Channel::UncertifiedAttribute => Treatment::Approximated(A::UncertainAttribute),
            Channel::AugmentationKind => Treatment::Approximated(A::AugmentationKind),
            Channel::BindingPattern => Treatment::Approximated(A::BindingPattern),
            Channel::RejectedShape => Treatment::Approximated(A::RejectedShape),
            Channel::ClassLet => Treatment::Approximated(A::ClassLetName),
            Channel::Accessibility
            | Channel::GenericArity
            | Channel::EntityKind
            | Channel::ImpliedExtensionAttribute => Treatment::Unconsumed,
            Channel::HeaderlessFile
            | Channel::Namespace
            | Channel::Module
            | Channel::ModuleAbbreviation
            | Channel::TypeDefinition
            | Channel::Abbreviation
            | Channel::Exception
            | Channel::AutoOpenAttribute
            | Channel::ExtensionAttribute
            | Channel::CompiledNameAttribute
            | Channel::AttributeTarget
            | Channel::AssemblyAutoOpen
            | Channel::OptionalExtensionMember
            | Channel::IntrinsicAugmentation
            | Channel::CSharpExtensionMember
            | Channel::ExtensionBinding => Treatment::Modelled,
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
    /// It decides only fields no existence question reads, which the walk
    /// leaves constant.
    Unconsumed,
}

/// The most rows one file's walk emits, and the most declarations it visits,
/// before it declines ([`ExistenceUnread::TooManyReadings`]).
pub const MAX_ROWS: usize = 200_000;

/// The most bytes of names the walk's rows copy, every row's path included,
/// before it declines ([`ExistenceUnread::TooManyReadings`]). Each row
/// repeats every name enclosing it, so [`MAX_ROWS`] alone does not bound
/// them: long names under deep nesting multiply.
pub const MAX_ROW_BYTES: usize = 64 << 20;

/// A's existence surface, read from its source. See the module docs.
pub fn source_existence(producer: Producer<'_>) -> SourceExistence {
    match producer {
        Producer::FoldRefused(why) => {
            SourceExistence::Unread(ExistenceUnread::FoldRefused(why.to_owned()))
        }
        Producer::UnservedTfm(why) => {
            SourceExistence::Unread(ExistenceUnread::UnservedTfm(why.to_owned()))
        }
        Producer::Evaluated {
            items,
            routes,
            providers,
        } => match walk_project(items, routes, providers) {
            Ok(surface) => SourceExistence::Read(surface),
            Err(why) => SourceExistence::Unread(why),
        },
    }
}

fn walk_project(
    items: &[CompileItem<'_>],
    routes: &MarkerRoutes,
    providers: ProviderReferences,
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
    let module_abbreviations = files.iter().any(|pf| {
        pf.file
            .syntax()
            .descendants()
            .any(|n| n.kind() == SyntaxKind::MODULE_ABBREV_DECL)
    });
    let mut out = Out::default();
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
        // A signature and its implementation contribute both their rows
        // (decision D7): FCS's are the signature's, which the union holds.
        if partners[i].is_some() {
            out.approximations.insert(Approximation::SignaturePair);
        }
        let mut file = FileWalk {
            index: i,
            routes,
            providers,
            module_abbreviations,
            paired: partners[i].is_some(),
            visits: 0,
            out: std::mem::take(&mut out),
            lines: Lines::of(root).map(std::rc::Rc::new),
        };
        file.walk(pf)?;
        out = file.out;
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
    rows.dedup();
    let mut extensions = out.extensions;
    extensions.sort();
    extensions.dedup();
    Ok(SourceSurface {
        index: ExistenceIndex {
            il: Vec::new(),
            pickle: PickleLayer::Read(rows),
            extensions,
        },
        assembly_auto_opens: out.auto_opens,
        approximations: out.approximations,
        lender_sources: out.lender_sources,
    })
}

/// Whether a hash directive brings in an assembly or a source file.
fn brings_in_references(directive: &SyntaxNode) -> bool {
    directive
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| t.kind() == SyntaxKind::IDENT_TOK)
        .is_some_and(|t| {
            // `#``load```: FCS reads the quoted name as the directive.
            matches!(
                id_text(&t).as_ref(),
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
    lender_sources: Vec<LenderSource>,
    /// The bytes of names the rows so far copy, paths included
    /// ([`MAX_ROW_BYTES`]).
    bytes: usize,
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
    if let Expr::Paren(p) = expr {
        return p.inner().as_ref().and_then(string_literal);
    }
    let Expr::Const(c) = expr else {
        return None;
    };
    let tok = c.literal()?;
    let text = tok.text();
    let kind = tok.kind();
    if kind == SyntaxKind::STRING_LIT {
        let inner = text.strip_prefix('"')?.strip_suffix('"')?;
        (!inner.contains('\\')).then(|| inner.to_owned())
    } else if kind == SyntaxKind::VERBATIM_STRING_LIT {
        let inner = text.strip_prefix("@\"")?.strip_suffix('"')?;
        Some(inner.replace("\"\"", "\""))
    } else if kind == SyntaxKind::TRIPLE_STRING_LIT {
        let inner = text.strip_prefix("\"\"\"")?.strip_suffix("\"\"\"")?;
        Some(inner.to_owned())
    } else {
        None
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
    /// The compiled names an attribute that may be `[<CompiledName>]` gives.
    compiled_names: Vec<String>,
    /// An attribute that may be `[<CompiledName>]` whose argument is no
    /// literal.
    compiled_name_unreadable: bool,
    /// Some denotation was uncertain and some marker possible because of it.
    uncertain: bool,
}

impl Marks {
    fn get(&self, m: Marker) -> Maybe {
        self.markers.get(&m).copied().unwrap_or(Maybe::No)
    }

    /// Whether `m` may apply.
    fn may(&self, m: Marker) -> bool {
        self.get(m) != Maybe::No
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

    /// What `lists` on a member or a `let` definition say: a `return:`
    /// attribute is the return value's.
    fn marks<'l>(&self, lists: impl IntoIterator<Item = &'l AttributeList>) -> Marks {
        self.marks_on(lists, true)
    }

    /// What `lists` on a carrier FCS gives a `return:` attribute to say: a
    /// module, a type, an exception, a primary constructor, and a signature
    /// (`val`, member signature, abstract slot).
    fn entity_marks<'l>(&self, lists: impl IntoIterator<Item = &'l AttributeList>) -> Marks {
        self.marks_on(lists, false)
    }

    fn marks_on<'l>(
        &self,
        lists: impl IntoIterator<Item = &'l AttributeList>,
        has_return_value: bool,
    ) -> Marks {
        let mut marks = Marks {
            markers: BTreeMap::new(),
            compiled_names: Vec::new(),
            compiled_name_unreadable: false,
            uncertain: false,
        };
        for list in lists {
            // Every attribute of the list FCS keeps on the carrier
            // (`TcAttributes`), whatever its target, an `assembly:` one too
            // (which the assembly's own list also gets); but a `return:` one
            // is a return value's, where the carrier has one.
            for attr in list.attributes() {
                if has_return_value && attr.target().is_some_and(|t| t.text() == "return") {
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
                    if m == Marker::CompiledName {
                        match arg_of(&attr) {
                            Arg::Literal(s) => marks.compiled_names.push(s),
                            // `[<CompiledName>]` with no argument does not
                            // compile; any other attribute with none names
                            // nothing.
                            Arg::None => {}
                            Arg::Other => marks.compiled_name_unreadable = true,
                        }
                    }
                }
            }
        }
        marks
    }
}

/// The scope a declaration sits in.
#[derive(Debug, Clone)]
struct Scope {
    namespace: Vec<String>,
    /// The enclosing modules' and types' logical names, outermost first.
    enclosing: Vec<String>,
    /// Whether an enclosing module is read under the `Module` suffix the
    /// walk adds as a second reading ([`Approximation::ModuleSuffix`]).
    suffixed: bool,
}

impl Scope {
    /// Directly in namespace `namespace`.
    fn root(namespace: Vec<String>) -> Scope {
        Scope {
            namespace,
            enclosing: Vec::new(),
            suffixed: false,
        }
    }

    /// Inside the entity `name` of this scope.
    fn inner(&self, name: &str) -> Scope {
        let mut enclosing = self.enclosing.clone();
        enclosing.push(name.to_owned());
        Scope {
            namespace: self.namespace.clone(),
            enclosing,
            suffixed: self.suffixed,
        }
    }
}

/// One type definition of a declaration list, as an augmentation's kind
/// reads it.
#[derive(Debug, Clone)]
struct LocalType {
    /// The name as written (no arity).
    name: String,
    /// Its declared type parameters' count.
    arity: usize,
    /// Its position in the declaration list.
    position: usize,
    /// Certainly a class, struct, record or union whose name counts every
    /// type parameter (none may be a unit of measure): augmenting it in its
    /// own list, under its full arity, is intrinsic.
    class_like: bool,
}

/// The declaration list an augmentation sits in.
struct ListCtx {
    locals: Vec<LocalType>,
    /// The positions that may change what a later name resolves to: an
    /// `open`, a nested module (which may be `[<AutoOpen>]`).
    barriers: Vec<usize>,
    is_rec: bool,
}

struct FileWalk<'r> {
    index: usize,
    routes: &'r MarkerRoutes,
    providers: ProviderReferences,
    /// Whether some file of the project declares a module abbreviation.
    module_abbreviations: bool,
    /// Whether this file is one of a signature pair.
    paired: bool,
    /// Declarations visited, which a module's second reading repeats.
    visits: usize,
    out: Out,
    /// The file's lines, or `None` when a `#line` directive may move them.
    lines: Option<std::rc::Rc<Lines>>,
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
                    self.decls(&Scope::root(Vec::new()), &decls, m.is_rec())?;
                }
                ModuleOrNamespaceKind::DeclaredNamespace => {
                    let ns = long_id_segments(m.long_id())
                        .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                    self.namespace(&ns)?;
                    self.decls(&Scope::root(ns), &decls, m.is_rec())?;
                }
                ModuleOrNamespaceKind::NamedModule | ModuleOrNamespaceKind::Anon => {
                    let (segments, attrs): (Vec<String>, Vec<AttributeList>) =
                        if m.kind() == ModuleOrNamespaceKind::Anon {
                            let segs = pf
                                .qnof
                                .anonymous_module_segments()
                                .ok_or(ExistenceUnread::AnonymousModuleName(self.index))?;
                            (segs, Vec::new())
                        } else {
                            (
                                long_id_segments(m.long_id())
                                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?,
                                m.attributes().collect(),
                            )
                        };
                    let (name, ns) = segments.split_last().expect("segments are not empty");
                    self.namespace(ns)?;
                    self.module(&Scope::root(ns.to_vec()), name, &attrs, &decls, m.is_rec())?;
                }
            }
        }
        Ok(())
    }

    /// Whether the rows so far are within [`MAX_ROWS`]: a module whose name
    /// ends in `Module` doubles the paths under it, and a walk past the bound
    /// declines rather than emit an unbounded or truncated surface.
    fn within_budget(&self) -> Result<(), ExistenceUnread> {
        let rows = self.out.entities.len() + self.out.extensions.len() + self.out.namespaces.len();
        if rows > MAX_ROWS {
            Err(ExistenceUnread::TooManyReadings)
        } else {
            Ok(())
        }
    }

    /// Charge `rows` rows at `scope`, each copying its path and `names`
    /// bytes of its own, before they are made.
    fn charge(&mut self, scope: &Scope, rows: usize, names: usize) -> Result<(), ExistenceUnread> {
        let path: usize = scope
            .namespace
            .iter()
            .chain(&scope.enclosing)
            .map(String::len)
            .sum();
        self.out.bytes = self
            .out
            .bytes
            .saturating_add(rows.saturating_mul(path.saturating_add(names)));
        if self.out.bytes > MAX_ROW_BYTES {
            Err(ExistenceUnread::TooManyReadings)
        } else {
            Ok(())
        }
    }

    /// Charge one declaration visit: each reading of a module whose name
    /// ends in `Module` walks its contents again, rows or none, so the work
    /// is bounded apart from the rows.
    fn visit(&mut self) -> Result<(), ExistenceUnread> {
        self.visits += 1;
        if self.visits > MAX_ROWS {
            Err(ExistenceUnread::TooManyReadings)
        } else {
            Ok(())
        }
    }

    /// Record namespace `ns` and its prefixes: quadratic in its segments,
    /// so charged to the budget before they are made.
    fn namespace(&mut self, ns: &[String]) -> Result<(), ExistenceUnread> {
        if self.out.namespaces.len() + ns.len() * (ns.len() + 1) / 2 > MAX_ROWS {
            return Err(ExistenceUnread::TooManyReadings);
        }
        let prefixes: usize = (1..=ns.len())
            .map(|k| ns[..k].iter().map(String::len).sum::<usize>())
            .sum();
        self.charge(&Scope::root(Vec::new()), 1, prefixes)?;
        for k in 1..=ns.len() {
            self.out.namespaces.insert(ns[..k].to_vec());
        }
        Ok(())
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
            for attr in list.attributes() {
                let assembly = attr.target().is_some_and(|t| t.text() == "assembly");
                if !(assembly || standalone) {
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

    /// The type definitions and barriers of a declaration list.
    fn list_ctx(&self, decls: &Decls, is_rec: bool) -> ListCtx {
        let mut ctx = ListCtx {
            locals: Vec::new(),
            barriers: Vec::new(),
            is_rec,
        };
        let types = |position: usize, defn: &TypeDefn, ctx: &mut ListCtx| {
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
            // A type parameter with an attribute may be a unit of measure,
            // which the name does not count.
            let full_arity = typars.iter().all(|t| t.attributes().next().is_none());
            ctx.locals.push(LocalType {
                name,
                arity: typars.len(),
                position,
                class_like: full_arity && certainly_class_like(defn),
            });
        };
        // An exception is a class-like augmentation target too.
        let exception =
            |position: usize, e: &borzoi_cst::syntax::ExceptionDefnDecl, ctx: &mut ListCtx| {
                if let Some(t) = e.union_case().and_then(|c| c.ident()) {
                    ctx.locals.push(LocalType {
                        name: id_text(&t).into_owned(),
                        arity: 0,
                        position,
                        class_like: true,
                    });
                }
            };
        match decls {
            Decls::Impl(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    match d {
                        ModuleDecl::Types(t) => {
                            for defn in t.defns() {
                                types(i, &defn, &mut ctx);
                            }
                        }
                        ModuleDecl::Exception(e) => exception(i, e, &mut ctx),
                        ModuleDecl::Open(_) | ModuleDecl::NestedModule(_) => ctx.barriers.push(i),
                        ModuleDecl::Let(_)
                        | ModuleDecl::Extern(_)
                        | ModuleDecl::Expr(_)
                        | ModuleDecl::ModuleAbbrev(_)
                        | ModuleDecl::Attributes(_)
                        | ModuleDecl::HashDirective(_) => {}
                    }
                }
            }
            Decls::Sig(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    match d {
                        SigDecl::Types(t) => {
                            for defn in t.defns() {
                                types(i, &defn, &mut ctx);
                            }
                        }
                        SigDecl::Exception(e) => exception(i, e, &mut ctx),
                        SigDecl::Open(_) | SigDecl::NestedModule(_) => ctx.barriers.push(i),
                        SigDecl::Val(_) | SigDecl::ModuleAbbrev(_) | SigDecl::HashDirective(_) => {}
                    }
                }
            }
        }
        ctx
    }

    /// The declaration list `decls` in `scope`.
    fn decls(&mut self, scope: &Scope, decls: &Decls, is_rec: bool) -> Result<(), ExistenceUnread> {
        let ctx = self.list_ctx(decls, is_rec);
        match decls {
            Decls::Impl(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    self.visit()?;
                    self.impl_decl(scope, d, i, &ctx, is_rec)?;
                    self.within_budget()?;
                }
            }
            Decls::Sig(ds) => {
                for (i, d) in ds.iter().enumerate() {
                    self.visit()?;
                    self.sig_decl(scope, d, i, &ctx, is_rec)?;
                    self.within_budget()?;
                }
            }
        }
        Ok(())
    }

    fn impl_decl(
        &mut self,
        scope: &Scope,
        d: &ModuleDecl,
        position: usize,
        ctx: &ListCtx,
        is_rec: bool,
    ) -> Result<(), ExistenceUnread> {
        match d {
            ModuleDecl::NestedModule(m) => {
                let name = long_id_segments(m.long_id())
                    .and_then(|s| s.last().cloned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = m.attributes().collect();
                self.module(
                    scope,
                    &name,
                    &attrs,
                    &Decls::Impl(m.decls().collect()),
                    m.is_rec() || is_rec,
                )
            }
            ModuleDecl::Types(t) => {
                for defn in t.defns() {
                    self.type_defn(scope, &defn, position, ctx)?;
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
                let marks = self.routes.entity_marks(&attrs);
                let members: Vec<MemberDefn> = e.members().collect();
                self.members(&scope.inner(&name), &members, None)?;
                self.type_bodies(&scope.inner(&name), None, &members)?;
                self.entity(
                    scope,
                    &name,
                    &[PickledEntityKind::Exception],
                    &marks,
                    false,
                    &BTreeSet::new(),
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
                if !marks.may(Marker::Extension) {
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
        ctx: &ListCtx,
        is_rec: bool,
    ) -> Result<(), ExistenceUnread> {
        match d {
            SigDecl::NestedModule(m) => {
                let name = long_id_segments(m.long_id())
                    .and_then(|s| s.last().cloned())
                    .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
                let attrs: Vec<AttributeList> = m.attributes().collect();
                self.module(
                    scope,
                    &name,
                    &attrs,
                    &Decls::Sig(m.sig_decls().collect()),
                    m.is_rec() || is_rec,
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
                let marks = self.routes.entity_marks(&attrs);
                let members: Vec<MemberDefn> = e.members().collect();
                self.members(&scope.inner(&name), &members, None)?;
                self.type_bodies(&scope.inner(&name), None, &members)?;
                self.entity(
                    scope,
                    &name,
                    &[PickledEntityKind::Exception],
                    &marks,
                    false,
                    &BTreeSet::new(),
                )
            }
            SigDecl::Val(v) => {
                let lists: Vec<AttributeList> = v.attributes().collect();
                let marks = self.routes.entity_marks(&lists);
                if !marks.may(Marker::Extension) {
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

    /// A module entity, and its contents. FCS may give the module a
    /// `Module` suffix; the set's canonical spelling strips it, so a module
    /// takes it unseen, but for a name already ending in `Module`
    /// (`FooModule` may be `FooModuleModule`, canonically `FooModule`), whose
    /// both readings the walk emits.
    fn module(
        &mut self,
        scope: &Scope,
        name: &str,
        attrs: &[AttributeList],
        decls: &Decls,
        is_rec: bool,
    ) -> Result<(), ExistenceUnread> {
        let marks = self.routes.entity_marks(attrs);
        let mut readings = vec![name.to_owned()];
        if name.len() > "Module".len() && name.ends_with("Module") {
            self.out.approximations.insert(Approximation::ModuleSuffix);
            readings.push(format!("{name}Module"));
        }
        for logical in &readings {
            self.within_budget()?;
            let mut inner = scope.inner(logical);
            inner.suffixed |= logical != name;
            self.decls(&inner, decls, is_rec)?;
            // `[<CompiledName>]` does not rename a module.
            self.entity(
                scope,
                logical,
                &[PickledEntityKind::Module],
                &marks,
                false,
                &BTreeSet::new(),
            )?;
        }
        Ok(())
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
        abbreviation_sources: &BTreeSet<Approximation>,
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
        let extension = marks.get(Marker::Extension);
        if marks.uncertain
            && (auto_open == Maybe::Possibly
                || extension == Maybe::Possibly
                || (compiled.len() > 1 && marks.get(Marker::CompiledName) == Maybe::Possibly))
        {
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
        // A row that may lend, with what may have made it one.
        if kinds.contains(&PickledEntityKind::Abbreviation)
            && (auto_open != Maybe::No || extension != Maybe::No)
        {
            let mut approximations = abbreviation_sources.clone();
            if marks.uncertain && (auto_open == Maybe::Possibly || extension == Maybe::Possibly) {
                approximations.insert(Approximation::UncertainAttribute);
            }
            if scope.suffixed {
                approximations.insert(Approximation::ModuleSuffix);
            }
            if self.paired {
                approximations.insert(Approximation::SignaturePair);
            }
            self.charge(scope, 1, 0)?;
            self.out.lender_sources.push(LenderSource {
                namespace: scope.namespace.clone(),
                enclosing: scope.enclosing.clone(),
                approximations,
            });
        }
        let names = logical.len() + compiled.iter().map(String::len).max().unwrap_or(0);
        self.charge(scope, kinds.len() * compiled.len(), names)?;
        for &kind in kinds {
            for c in &compiled {
                self.out.entities.push(PickledEntityRow {
                    namespace: scope.namespace.clone(),
                    enclosing: scope.enclosing.clone(),
                    logical_name: logical.to_owned(),
                    compiled_name: c.clone(),
                    kind,
                    public: true,
                    auto_open: auto_open != Maybe::No,
                    extension: extension != Maybe::No,
                });
            }
        }
        Ok(())
    }

    fn type_defn(
        &mut self,
        scope: &Scope,
        defn: &TypeDefn,
        position: usize,
        ctx: &ListCtx,
    ) -> Result<(), ExistenceUnread> {
        if is_augmentation(defn) {
            return self.augmentation(scope, defn, position, ctx);
        }
        // `type X.Y = …` (FS0925, recovered as `X`) is outside the domain.
        if defn.long_id().is_some_and(|li| li.idents().count() > 1) {
            return Err(ExistenceUnread::OutsideDomain(self.index, Leaf::TypeHead));
        }
        let name = defn
            .long_id()
            .and_then(|li| li.idents().last())
            .map(|t| id_text(&t).into_owned())
            .ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
        let attrs: Vec<AttributeList> = defn.attributes().collect();
        let marks = self.routes.entity_marks(&attrs);
        let generic = defn
            .typar_decls()
            .is_some_and(|d| d.typars().next().is_some());
        let mut abbreviation_sources: BTreeSet<Approximation> = BTreeSet::new();
        let kinds: Vec<PickledEntityKind> = match defn.repr() {
            Some(TypeDefnRepr::Abbrev(a)) => {
                let target = a.ty();
                let provided = |t: &Type| {
                    has_static_argument(t)
                        || (self.providers == ProviderReferences::Possible && may_be_provided(t))
                };
                if target.as_ref().is_some_and(provided) {
                    return Err(ExistenceUnread::TypeProvider(self.index));
                }
                let (kinds, source) =
                    self.abbreviation_kinds(&name, generic, target.as_ref(), &marks);
                abbreviation_sources.extend(source);
                kinds
            }
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
        // The type's own members, which are C#-style extensions when marked.
        let mut members: Vec<MemberDefn> = defn.members().collect();
        if let Some(TypeDefnRepr::ObjectModel(om)) = defn.repr() {
            members.extend(om.members());
        }
        let inner = scope.inner(&name);
        self.members(&inner, &members, None)?;
        self.type_bodies(&inner, defn.implicit_ctor(), &members)?;
        self.entity(scope, &name, &kinds, &marks, true, &abbreviation_sources)
    }

    /// What `type name = target` may be: an abbreviation, or (`target` one
    /// identifier) FCS's single-case union when it names no type in scope,
    /// or itself (`type X = X`, a union unless a unit of measure). Only an
    /// abbreviation lends what an `[<AutoOpen>]` or `[<Extension>]` on it
    /// brings, and one surplus lender makes every name a possible extension,
    /// so the abbreviation reading is emitted alone only where FCS's is
    /// certain: a target FSharp.Core declares (open in every file).
    fn abbreviation_kinds(
        &mut self,
        name: &str,
        generic: bool,
        target: Option<&Type>,
        marks: &Marks,
    ) -> (Vec<PickledEntityKind>, Option<Approximation>) {
        let measure = marks.get(Marker::Measure);
        let (kinds, source) = match target.and_then(abbrev_single_ident) {
            // `type Foo<'a> = Foo` may abbreviate another `Foo` of no arity.
            Some(t) if t == name && !generic => match measure {
                Maybe::No => (vec![PickledEntityKind::Type], None),
                Maybe::Yes => (vec![PickledEntityKind::Abbreviation], None),
                Maybe::Possibly => (
                    vec![PickledEntityKind::Abbreviation, PickledEntityKind::Type],
                    Some(Approximation::UncertainAttribute),
                ),
            },
            Some(t) if FSHARP_CORE_TYPE_NAMES.contains(&t.as_str()) => {
                (vec![PickledEntityKind::Abbreviation], None)
            }
            Some(_) if measure != Maybe::Yes => (
                vec![PickledEntityKind::Abbreviation, PickledEntityKind::Type],
                Some(Approximation::AbbreviationOrUnion),
            ),
            _ => (vec![PickledEntityKind::Abbreviation], None),
        };
        if let Some(a) = source {
            self.out.approximations.insert(a);
        }
        (kinds, source)
    }

    /// The rows of what a type, an augmentation or an exception declares
    /// beside its members (`ctor` its primary constructor): a primary
    /// constructor and class `let`s under `[<Extension>]` are pickled as
    /// C#-style rows; a marked interface implementation's member has an
    /// interface-qualified compiled name the walk does not spell. Every
    /// caller of [`Self::members`] runs this too, so between them every
    /// member kind is read.
    fn type_bodies(
        &mut self,
        inner: &Scope,
        ctor: Option<ImplicitCtor>,
        members: &[MemberDefn],
    ) -> Result<(), ExistenceUnread> {
        if let Some(ctor) = &ctor {
            let lists: Vec<AttributeList> = ctor.attributes().collect();
            let marks = self.routes.entity_marks(&lists);
            if marks.may(Marker::Extension) {
                self.csharp_row(inner, ".ctor", &marks)?;
            }
        }
        self.class_lets(inner, ctor.as_ref(), members)?;
        for m in members {
            if let MemberDefn::Interface(i) = m {
                for im in i.members() {
                    let (lists, shape) = member_shape(&im);
                    let mut all = lists;
                    if let MemberShape::Named { vals, .. } = shape {
                        for v in vals {
                            all.extend(v.own_lists);
                        }
                    }
                    if self.routes.marks(&all).may(Marker::Extension) {
                        return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                    }
                }
            }
        }
        Ok(())
    }

    /// The C#-style rows of a type's `let`s under `[<Extension>]`. FCS
    /// compiles a `let` that takes arguments to a method val under the name
    /// it takes, which is its own unless an earlier name of the type took
    /// it: then `basic@line`, with `-k` for the `k`th earlier fresh name of
    /// the same `basic` (the name before its first `@`), `line` the
    /// binder's. Every binder of the type (constructor argument, self
    /// identifier, `let` binder, a pattern's matched value) takes at most
    /// one fresh name, so their count bounds `k`; and a `let` that is a
    /// value has no val. The walk emits every one of those names for every
    /// marked `let`, whatever its arity, and for every line its head spans
    /// ([`head_lines`]) rather than the binder's alone: which token FCS
    /// takes the binder's range from is a parser rule the walk need not
    /// model, and no query names a mangled name but a backticked one.
    fn class_lets(
        &mut self,
        inner: &Scope,
        ctor: Option<&ImplicitCtor>,
        members: &[MemberDefn],
    ) -> Result<(), ExistenceUnread> {
        let lets: Vec<&MemberLetBindings> = members
            .iter()
            .filter_map(|m| {
                if let MemberDefn::LetBindings(l) = m {
                    Some(l)
                } else {
                    None
                }
            })
            .collect();
        // Each binding with its attribute lists: a group's own lists mark
        // its first binding.
        let bindings: Vec<(Binding, Vec<AttributeList>)> = lets
            .iter()
            .flat_map(|l| {
                let lists: Vec<AttributeList> = l.attributes().collect();
                l.bindings().enumerate().map(move |(k, b)| {
                    let mut own: Vec<AttributeList> = b.attributes().collect();
                    if k == 0 {
                        own.extend(lists.iter().cloned());
                    }
                    (b, own)
                })
            })
            .collect();
        if !bindings
            .iter()
            .any(|(_, lists)| self.routes.marks(lists).may(Marker::Extension))
        {
            return Ok(());
        }
        let Some(lines) = self.lines.clone() else {
            return Err(ExistenceUnread::LineDirective(self.index));
        };
        // An upper bound on the type's binders: every identifier or
        // wildcard of the constructor's arguments, its self identifier, and
        // each binding's identifiers and matched value.
        let ctor_binders = ctor.and_then(|c| c.args()).map_or(0, |p| {
            p.syntax()
                .descendants_with_tokens()
                .filter_map(|el| el.into_token())
                .filter(|t| matches!(t.kind(), SyntaxKind::IDENT_TOK | SyntaxKind::UNDERSCORE_TOK))
                .count()
        });
        let binders = ctor_binders
            + usize::from(ctor.and_then(|c| c.self_id()).is_some())
            + bindings
                .iter()
                .map(|(b, _)| b.pat().map_or(0, |p| pattern_idents(&p).len()) + 1)
                .sum::<usize>();
        for (b, lists) in &bindings {
            let marks = self.routes.marks(lists);
            if !marks.may(Marker::Extension) {
                continue;
            }
            let Some(pat) = b.pat() else {
                return Err(ExistenceUnread::UnnamedDeclaration(self.index));
            };
            let named: Vec<String> = match binding_name(&pat) {
                Some(name) => vec![name],
                None => {
                    if !certified_pattern(&pat) {
                        return Err(ExistenceUnread::OutsideDomain(
                            self.index,
                            Leaf::BindingHead,
                        ));
                    }
                    self.out
                        .approximations
                        .insert(Approximation::BindingPattern);
                    pattern_idents(&pat)
                }
            };
            if named.is_empty() {
                return Err(ExistenceUnread::UnnamedDeclaration(self.index));
            }
            self.out.approximations.insert(Approximation::ClassLetName);
            // FCS mangles a taken name by its binder's line, which some token
            // of the head holds: so every line the head spans, from its
            // node's first byte (any trivia it holds included) to its last
            // token's end. No query names a mangled name but a backticked
            // one, so the span's surplus costs nothing a consumer reads.
            let span =
                head_lines(&pat, &lines).ok_or(ExistenceUnread::UnnamedDeclaration(self.index))?;
            // Each name is a row per line, binder and compiled name: charged
            // before expanding.
            let rows = named.len()
                * span.clone().count()
                * (binders + 1)
                * (marks.compiled_names.len() + 1);
            if self.out.entities.len() + self.out.extensions.len() + rows > MAX_ROWS {
                return Err(ExistenceUnread::TooManyReadings);
            }
            for name in named {
                let basic = match name.find('@') {
                    None | Some(0) => name.as_str(),
                    Some(n) => &name[..n],
                };
                let mut taken = vec![name.clone()];
                for line in span.clone() {
                    for k in 0..binders {
                        taken.push(if k == 0 {
                            format!("{basic}@{line}")
                        } else {
                            format!("{basic}@{line}-{k}")
                        });
                    }
                }
                for n in taken {
                    self.csharp_row(inner, &n, &marks)?;
                }
                // Marked `let`s by binders is quadratic in the type.
                self.within_budget()?;
            }
        }
        Ok(())
    }

    /// The extension rows of members `members` of a type (or of an
    /// augmentation, `augmented`: the names the extended type's logical name
    /// may have): an optional extension's every member, and any member that
    /// may carry `[<Extension>]`.
    fn members(
        &mut self,
        scope: &Scope,
        members: &[MemberDefn],
        augmented: Option<&[String]>,
    ) -> Result<(), ExistenceUnread> {
        for m in members {
            // A member's rows multiply its compiled names by the type's.
            self.within_budget()?;
            let (lists, shape) = member_shape(m);
            let (vals, role) = match shape {
                MemberShape::NoVal => match m {
                    // A `do` binds nothing; a `let` and an interface
                    // implementation are [`Self::type_bodies`]'s, which
                    // every caller runs.
                    MemberDefn::Do(_) | MemberDefn::LetBindings(_) | MemberDefn::Interface(_) => {
                        continue;
                    }
                    MemberDefn::Member(_)
                    | MemberDefn::ValField(_)
                    | MemberDefn::Inherit(_)
                    | MemberDefn::GetSetMember(_)
                    | MemberDefn::AutoProperty(_)
                    | MemberDefn::AbstractSlot(_)
                    | MemberDefn::MemberSig(_) => {
                        return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                    }
                },
                MemberShape::Inherit => {
                    if augmented.is_some() {
                        self.out.approximations.insert(Approximation::RejectedShape);
                    }
                    continue;
                }
                MemberShape::Unnamed => {
                    // A member no attribute marks, outside an augmentation,
                    // has no row whatever its name.
                    if augmented.is_none() && !self.routes.marks(&lists).may(Marker::Extension) {
                        continue;
                    }
                    return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                }
                // A `val` field is no method: `[<Extension>]` on it makes no
                // row.
                MemberShape::Named {
                    role: MemberRole::Field,
                    ..
                } => {
                    if augmented.is_some() {
                        self.out.approximations.insert(Approximation::RejectedShape);
                    }
                    continue;
                }
                MemberShape::Named {
                    vals,
                    rejected,
                    role,
                    ..
                } => {
                    // An abstract slot FCS rejects in an augmentation: its
                    // rows are read as written.
                    if rejected && augmented.is_some() {
                        self.out.approximations.insert(Approximation::RejectedShape);
                    }
                    (vals, role)
                }
            };
            // A signature keeps its `return:` attributes.
            let signature = matches!(m, MemberDefn::AbstractSlot(_) | MemberDefn::MemberSig(_));
            // A `[<CLIEvent>]` property compiles to its event's accessors
            // too, which `[<CompiledName>]` does not rename.
            let mut vals = vals;
            let mut event_vals: BTreeSet<String> = BTreeSet::new();
            // `[<CLIEvent>]` on the member, or on an accessor's own list.
            let event_marks = {
                let mut all = lists.clone();
                for v in &vals {
                    all.extend(v.own_lists.iter().cloned());
                }
                self.routes.marks_on(&all, !signature)
            };
            if event_marks.may(Marker::CliEvent) && role == MemberRole::Member {
                if event_marks.get(Marker::CliEvent) == Maybe::Possibly && event_marks.uncertain {
                    self.out
                        .approximations
                        .insert(Approximation::UncertainAttribute);
                }
                // Every val: FCS's recovery of an event on a method (which it
                // rejects) names its accessors after the method.
                let carriers: Vec<MemberVal> = vals
                    .iter()
                    .filter(|v| v.accessor != Some("set_"))
                    .cloned()
                    .collect();
                for g in carriers {
                    let bare = match g.accessor {
                        Some(prefix) => g.logical.strip_prefix(prefix).unwrap_or(&g.logical),
                        None => &g.logical,
                    };
                    for prefix in ["add_", "remove_"] {
                        let logical = format!("{prefix}{bare}");
                        event_vals.insert(logical.clone());
                        vals.push(MemberVal {
                            logical,
                            accessor: None,
                            is_static: g.is_static,
                            own_lists: Vec::new(),
                        });
                    }
                }
            }
            for v in vals {
                let mut all = lists.clone();
                all.extend(v.own_lists.iter().cloned());
                let marks = self.routes.marks_on(&all, !signature);
                let marked = marks.get(Marker::Extension);
                if augmented.is_none() && marked == Maybe::No {
                    continue;
                }
                if marks.uncertain && marked == Maybe::Possibly && augmented.is_none() {
                    self.out
                        .approximations
                        .insert(Approximation::UncertainAttribute);
                }
                // A `[<CompiledName>]` renames a method, never a property's
                // or an event's accessor. A signature's getter reading may be
                // a method whose type the walk does not classify (`'T -> bool
                // when 'T: equality`), so its rename applies too.
                let renames =
                    (v.accessor.is_none() || signature) && !event_vals.contains(&v.logical);
                if marks.compiled_name_unreadable && renames {
                    return Err(ExistenceUnread::UnreadableCompiledName(self.index));
                }
                match augmented {
                    Some(type_names) => {
                        if role == MemberRole::Constructor {
                            // FCS rejects a constructor in an optional
                            // augmentation, and keeps it in its recovery
                            // (`String..ctor`).
                            self.out.approximations.insert(Approximation::RejectedShape);
                        }
                        // An optional extension: compiled `T.name[.Static]`,
                        // or the name a `[<CompiledName>]` gives. A signature's
                        // getter reading may be a method (`'T -> bool when
                        // 'T: equality`), compiled under its bare name.
                        let mut logicals = vec![v.logical.clone()];
                        if signature
                            && let Some(bare) = v.accessor.and_then(|p| v.logical.strip_prefix(p))
                        {
                            logicals.push(bare.to_owned());
                        }
                        let mut compiled: BTreeSet<String> = type_names
                            .iter()
                            .flat_map(|t| logicals.iter().map(move |l| (t, l)))
                            .map(|(t, logical)| {
                                let mut c = format!("{t}.{logical}");
                                // A constructor (rejected, and recovered as
                                // static) takes no suffix.
                                if v.is_static && role != MemberRole::Constructor {
                                    c.push_str(".Static");
                                }
                                c
                            })
                            .collect();
                        if renames {
                            self.uncertain_renames(&marks);
                            compiled.extend(marks.compiled_names.iter().cloned());
                        }
                        let names = 2 * v.logical.len()
                            + compiled.iter().map(String::len).max().unwrap_or(0);
                        self.charge(scope, compiled.len(), names)?;
                        for c in compiled {
                            self.out.extensions.push(ExtensionRow {
                                layer: IndexLayer::Pickle,
                                namespace: scope.namespace.clone(),
                                enclosing: scope.enclosing.clone(),
                                names: val_names(&v.logical, v.accessor, Some(&c)),
                                instance: (role != MemberRole::Constructor).then_some(!v.is_static),
                            });
                        }
                    }
                    None => self.csharp_val(scope, &v, &marks, renames)?,
                }
            }
        }
        Ok(())
    }

    /// A C#-style extension row for a member val `v` of a type: one per
    /// compiled name it may have. `renames`: whether a `[<CompiledName>]`
    /// renames it (a method; never a property's or an event's accessor).
    fn csharp_val(
        &mut self,
        scope: &Scope,
        v: &MemberVal,
        marks: &Marks,
        renames: bool,
    ) -> Result<(), ExistenceUnread> {
        let mut compiled: Vec<Option<&String>> = vec![None];
        if renames {
            self.uncertain_renames(marks);
            compiled.extend(marks.compiled_names.iter().map(Some));
        }
        let names = 2 * v.logical.len()
            + marks
                .compiled_names
                .iter()
                .map(String::len)
                .max()
                .unwrap_or(0);
        self.charge(scope, compiled.len(), names)?;
        for c in compiled {
            self.out.extensions.push(ExtensionRow {
                layer: IndexLayer::Pickle,
                namespace: scope.namespace.clone(),
                enclosing: scope.enclosing.clone(),
                names: val_names(&v.logical, v.accessor, c.map(String::as_str)),
                instance: None,
            });
        }
        Ok(())
    }

    /// Name the surplus of a compiled name an attribute only may give.
    fn uncertain_renames(&mut self, marks: &Marks) {
        if !marks.compiled_names.is_empty() && marks.get(Marker::CompiledName) == Maybe::Possibly {
            self.out
                .approximations
                .insert(Approximation::UncertainAttribute);
        }
    }

    /// A C#-style extension row for a value `name` bound by a `let`.
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
            own_lists: Vec::new(),
        };
        self.csharp_val(scope, &v, marks, true)
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
        if !marks.may(Marker::Extension) {
            return Ok(());
        }
        match pat.as_ref().and_then(binding_name) {
            Some(name) => self.csharp_row(scope, &name, &marks),
            None => {
                // A pattern binding names several values, each carrying the
                // attribute: in a certified form ([`Leaf::BindingHead`]),
                // every name the pattern spells.
                let Some(pat) = pat.as_ref() else {
                    return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                };
                if !certified_pattern(pat) {
                    return Err(ExistenceUnread::OutsideDomain(
                        self.index,
                        Leaf::BindingHead,
                    ));
                }
                let names = pattern_idents(pat);
                if names.is_empty() {
                    return Err(ExistenceUnread::UnnamedDeclaration(self.index));
                }
                // A row per name and compiled name: charged before expanding.
                let rows = names.len() * (marks.compiled_names.len() + 1);
                if self.out.entities.len() + self.out.extensions.len() + rows > MAX_ROWS {
                    return Err(ExistenceUnread::TooManyReadings);
                }
                self.out
                    .approximations
                    .insert(Approximation::BindingPattern);
                for n in names {
                    self.csharp_row(scope, &n, &marks)?;
                }
                Ok(())
            }
        }
    }

    /// A `type T with …` augmentation's extension rows. An intrinsic one's
    /// members are the type's own, rows only where marked; an optional one's
    /// every member is a row. The walk takes it as intrinsic only where FCS
    /// certainly does, as optional only where no type of its name is in its
    /// list, and both otherwise.
    fn augmentation(
        &mut self,
        scope: &Scope,
        defn: &TypeDefn,
        position: usize,
        ctx: &ListCtx,
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
            // A tuple type extension (`type (int * int) with`), which FCS
            // rejects and recovers as an extension of its tuple type:
            // ``Tuple`n``, or ``ValueTuple`n`` for a struct tuple, `n` its
            // elements' count (one beyond seven nest, so ``Tuple`8`` too).
            self.out.approximations.insert(Approximation::RejectedShape);
            let n = defn.tuple_type_head().map_or(0, |t| tuple_arity(&t));
            let mut names = Vec::new();
            for family in ["Tuple", "ValueTuple"] {
                names.push(family.to_owned());
                for k in [n, 8] {
                    if k > 0 {
                        names.push(format!("{family}`{k}"));
                    }
                }
            }
            names.sort();
            names.dedup();
            // Its `let`s, which FCS rejects here, kept in the container.
            self.type_bodies(scope, None, &members)?;
            return self.members(scope, &members, Some(&names));
        };
        if head.first().is_some_and(|h| h == "global") {
            return Err(ExistenceUnread::OutsideDomain(
                self.index,
                Leaf::AugmentationHead,
            ));
        }
        let last = head.last().expect("not empty").clone();
        // A qualified head names a type of this list only through a path to
        // the list's own container.
        let qualifier = &head[..head.len() - 1];
        let container: Vec<&String> = scope.namespace.iter().chain(&scope.enclosing).collect();
        // A qualifier names this list's container through a suffix of its
        // path, or through a module abbreviation (`module Alias = D`, then
        // `type Alias.T with`), which the walk does not resolve: with one
        // anywhere in the project, any qualifier may.
        let intrinsic = if qualifier.is_empty() {
            intrinsic_in(ctx, &last, arity, position)
        } else if self.module_abbreviations
            || (qualifier.len() <= container.len()
                && container[container.len() - qualifier.len()..]
                    .iter()
                    .zip(qualifier)
                    .all(|(a, b)| *a == b))
        {
            Maybe::Possibly
        } else {
            Maybe::No
        };
        // An extension's compiled names carry the extended type's arity
        // (``list`1.M``). A head that writes no parameters bounds it only
        // for a type the walk knows: FCS rejects such a head on a generic
        // type and imports the extension under the type's own arity.
        if arity == 0 && intrinsic != Maybe::Yes {
            return Err(ExistenceUnread::OutsideDomain(
                self.index,
                Leaf::AugmentationHead,
            ));
        }
        if intrinsic == Maybe::Possibly {
            self.out
                .approximations
                .insert(Approximation::AugmentationKind);
        }
        // A `let` compiles into the type where the augmentation is
        // intrinsic; elsewhere FCS rejects it, and its recovery keeps the
        // val in the augmentation's own container.
        self.type_bodies(&scope.inner(&last), None, &members)?;
        if intrinsic != Maybe::Yes {
            self.type_bodies(scope, None, &members)?;
        }
        if intrinsic != Maybe::No {
            self.members(&scope.inner(&last), &members, None)?;
            if intrinsic == Maybe::Yes {
                return Ok(());
            }
        }
        // The extended type's logical name: its name, with an arity suffix
        // of at most the head's parameter count (units of measure are not
        // counted, and the head need not repeat the type's measures).
        let mut type_names = vec![last.clone()];
        type_names.extend((1..=arity).map(|n| format!("{last}`{n}")));
        self.members(scope, &members, Some(&type_names))
    }
}

/// Whether an augmentation of `name` with `arity` type parameters at
/// `position` of a declaration list is intrinsic: the name resolves to a type
/// of the same list (FCS's `isInSameModuleOrNamespace`) that is not an
/// interface, delegate, enum or abbreviation. `Yes` only for the latest
/// earlier class-like definition of that name and arity with nothing
/// between that may bring another of its name; `No` when the list declares
/// no type of that name at all.
fn intrinsic_in(ctx: &ListCtx, name: &str, arity: usize, position: usize) -> Maybe {
    let same_name: Vec<&LocalType> = ctx.locals.iter().filter(|t| t.name == name).collect();
    if same_name.is_empty() {
        return Maybe::No;
    }
    let earlier = |t: &&LocalType| ctx.is_rec || t.position <= position;
    let Some(t) = same_name
        .iter()
        .copied()
        .filter(earlier)
        .max_by_key(|t| t.position)
    else {
        return Maybe::Possibly;
    };
    let clear = |from: usize| {
        if ctx.is_rec {
            ctx.barriers.is_empty()
        } else {
            !ctx.barriers.iter().any(|&b| b > from && b < position)
        }
    };
    let only_one = same_name.iter().filter(|u| earlier(u)).count() == 1;
    if t.class_like && t.arity == arity && clear(t.position) && only_one {
        Maybe::Yes
    } else {
        Maybe::Possibly
    }
}

/// Whether `defn` is certainly a class, struct, record or union. An
/// attribute may change the kind FCS infers (`[<Interface>]`,
/// `[<AbstractClass>]`, `[<Struct>]`, `[<Class>]`, `[<Measure>]`), so an
/// attributed type is not certainly one.
fn certainly_class_like(defn: &TypeDefn) -> bool {
    if defn.attributes().next().is_some() {
        return false;
    }
    match defn.repr() {
        Some(TypeDefnRepr::Record(_)) | Some(TypeDefnRepr::Union(_)) => true,
        Some(TypeDefnRepr::ObjectModel(om)) => {
            !om.is_interface()
                && !om.is_augmentation()
                && (om.is_class() || om.is_struct() || defn.implicit_ctor().is_some())
        }
        _ => false,
    }
}

fn is_augmentation(defn: &TypeDefn) -> bool {
    matches!(defn.repr(), Some(TypeDefnRepr::ObjectModel(om)) if om.is_augmentation())
        || defn.tuple_type_head().is_some()
        // A signature's `type T with member …`: no representation, its
        // `with` directly on the definition.
        || (defn.repr().is_none()
            && defn
                .syntax()
                .children_with_tokens()
                .filter_map(|el| el.into_token())
                .any(|t| t.kind() == SyntaxKind::WITH_TOK))
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
    if let Type::Paren(p) = ty {
        return p.inner().as_ref().and_then(abbrev_single_ident);
    }
    let Type::LongIdent(t) = ty else {
        return None;
    };
    let li = t.long_ident()?;
    let mut idents = li.idents();
    let first = idents.next()?;
    idents
        .next()
        .is_none()
        .then(|| id_text(&first).into_owned())
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

/// The element count of a tuple augmentation's head (`(int * int)`: 2).
fn tuple_arity(head: &borzoi_cst::syntax::TupleTypeExtensionHead) -> usize {
    match head.ty() {
        Some(Type::Tuple(t)) => t
            .segments()
            .iter()
            .filter(|s| matches!(s, borzoi_cst::syntax::TupleSegment::Type(_)))
            .count(),
        Some(_) => 1,
        None => 0,
    }
}

/// Whether an abbreviation's target may be a generative provider's type,
/// where a reference may be a provider ([`Leaf::ProvidedTarget`]): any
/// named type, applied or not, prefix or postfix (FCS hands a provider any
/// `SynType.App` or bare name, and an opened provider namespace may shadow
/// even FSharp.Core's names). Only a structural type (a tuple, a function,
/// an array, a variable, an anonymous record) is no provider's.
fn may_be_provided(ty: &Type) -> bool {
    match ty {
        Type::Paren(p) => p.inner().as_ref().is_none_or(may_be_provided),
        Type::Tuple(_)
        | Type::Fun(_)
        | Type::Array(_)
        | Type::Var(_)
        | Type::Anon(_)
        | Type::AnonRecd(_) => false,
        Type::LongIdent(_)
        | Type::App(_)
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
        | Type::SignatureParameter(_) => true,
    }
}

/// The 1-based line of each offset of one file, in FCS's sense: a line
/// starts after every `\n` (`newline = '\n' | '\r' '\n'`), wherever it
/// sits.
struct Lines {
    /// The offset of each `\n`, ascending.
    newlines: Vec<TextSize>,
}

impl Lines {
    /// The table of `root`'s file, or `None` when a `#line` directive may
    /// move the lines FCS reports.
    fn of(root: &SyntaxNode) -> Option<Lines> {
        let mut newlines = Vec::new();
        for el in root.descendants_with_tokens() {
            let Some(t) = el.into_token() else { continue };
            if t.kind() == SyntaxKind::HASH_LINE {
                return None;
            }
            let start = t.fcs_range().start();
            for (i, _) in t.text().match_indices('\n') {
                // In range: a file is under 4 GiB.
                newlines.push(start + TextSize::new(i as u32));
            }
        }
        Some(Lines { newlines })
    }

    fn line(&self, at: TextSize) -> u32 {
        // In range: a file is under 4 GiB.
        self.newlines.partition_point(|&n| n < at) as u32 + 1
    }
}

/// Every identifier in `pat`: a superset of the binders of a certified
/// pattern ([`certified_pattern`]), none of which holds an active pattern.
fn pattern_idents(pat: &Pat) -> Vec<String> {
    pat.syntax()
        .descendants_with_tokens()
        .filter_map(|el| el.into_token())
        .filter(|t| t.kind() == SyntaxKind::IDENT_TOK)
        .map(|t| id_text(&t).into_owned())
        .collect()
}

/// Every line binding head `pat` spans: from its node's first byte, any
/// trivia the node holds included, to the end of its last token. The only
/// positions the walk reads.
/// `None` for a head that holds no token, which names nothing.
fn head_lines(pat: &Pat, lines: &Lines) -> Option<std::ops::RangeInclusive<u32>> {
    let tokens = || {
        pat.syntax()
            .descendants_with_tokens()
            .filter_map(|el| el.into_token())
    };
    let first = tokens().next()?.fcs_range().start();
    let last = tokens().last()?.fcs_range().end();
    Some(lines.line(first)..=lines.line(last))
}

/// Whether a binding's pattern, when it names no single value
/// ([`binding_name`]), is a certified form ([`Leaf::BindingHead`]): a tuple
/// of names and wildcards, or a head that may be a union case
/// (`let Q (s: string) = …`, `let X = …`), under parentheses or a type
/// annotation. Its identifiers then hold its binders. Any other pattern (an
/// `as`, a record, a list, a cons, an `|`, a qualified case) is outside the
/// domain.
fn certified_pattern(pat: &Pat) -> bool {
    let simple = |p: &Pat| match p {
        Pat::Named(n) => n.active_pat_name().is_none(),
        Pat::Wildcard(_) => true,
        Pat::LongIdent(l) => {
            l.active_pat_name().is_none()
                && l.args().next().is_none()
                && l.name_pat_pairs().is_none()
                && l.head().is_some_and(|h| h.idents().count() == 1)
        }
        Pat::Paren(_)
        | Pat::Typed(_)
        | Pat::Const(_)
        | Pat::MeasureLit(_)
        | Pat::Null(_)
        | Pat::Tuple(_)
        | Pat::As(_)
        | Pat::ArrayOrList(_)
        | Pat::Record(_)
        | Pat::IsInst(_)
        | Pat::ListCons(_)
        | Pat::Ands(_)
        | Pat::Or(_)
        | Pat::Attrib(_)
        | Pat::OptionalVal(_)
        | Pat::Quote(_) => false,
    };
    match pat {
        Pat::Paren(p) => p.inner().as_ref().is_some_and(certified_pattern),
        Pat::Typed(t) => t.pat().as_ref().is_some_and(certified_pattern),
        Pat::Tuple(t) => t.elements().all(|e| simple(&e)),
        // A head that may be a union case, its arguments simple names.
        Pat::LongIdent(l) => {
            l.active_pat_name().is_none()
                && l.name_pat_pairs().is_none()
                && l.head().is_some_and(|h| h.idents().count() == 1)
                && l.args().all(|a| {
                    // Through parentheses and annotations: `(s: string)`.
                    let mut a = a;
                    loop {
                        let inner = match &a {
                            Pat::Paren(p) => p.inner(),
                            Pat::Typed(t) => t.pat(),
                            Pat::Named(_)
                            | Pat::LongIdent(_)
                            | Pat::Wildcard(_)
                            | Pat::Const(_)
                            | Pat::MeasureLit(_)
                            | Pat::Null(_)
                            | Pat::Tuple(_)
                            | Pat::As(_)
                            | Pat::ArrayOrList(_)
                            | Pat::Record(_)
                            | Pat::IsInst(_)
                            | Pat::ListCons(_)
                            | Pat::Ands(_)
                            | Pat::Or(_)
                            | Pat::Attrib(_)
                            | Pat::OptionalVal(_)
                            | Pat::Quote(_) => break simple(&a),
                        };
                        match inner {
                            Some(i) => a = i,
                            None => break false,
                        }
                    }
                })
        }
        // `let _ = …` binds nothing: certified, and then unnamed.
        Pat::Wildcard(_) => true,
        Pat::Named(_)
        | Pat::Const(_)
        | Pat::MeasureLit(_)
        | Pat::Null(_)
        | Pat::As(_)
        | Pat::ArrayOrList(_)
        | Pat::Record(_)
        | Pat::IsInst(_)
        | Pat::ListCons(_)
        | Pat::Ands(_)
        | Pat::Or(_)
        | Pat::Attrib(_)
        | Pat::OptionalVal(_)
        | Pat::Quote(_) => false,
    }
}

/// A module `let` binding's single name: `let f …`, `let x`, `let (|A|_|) …`,
/// an operator, under parentheses or a type annotation.
fn binding_name(pat: &Pat) -> Option<String> {
    binding_name_at(pat, true)
}

/// [`binding_name`], `top` when `pat` is the binding's whole pattern. A
/// long-ident head names a value only when spelled as no union case can be
/// (lower case first), and, with arguments, only at the top, where it is a
/// function: `let Some x = …`, `let None = …` and `let (f x) = …` do not.
fn binding_name_at(pat: &Pat, top: bool) -> Option<String> {
    match pat {
        // `let (|Zero|_|) = …`: a nullary active pattern, named by its
        // recognizer.
        Pat::Named(n) => match n.active_pat_name() {
            Some(ap) => Some(active_pattern_name(&ap)),
            None => n.ident().map(|t| id_text(&t).into_owned()),
        },
        Pat::LongIdent(l) => {
            if let Some(ap) = l.active_pat_name() {
                return Some(active_pattern_name(&ap));
            }
            let li = l.head()?;
            let mut idents = li.idents();
            let first = idents.next()?;
            if idents.next().is_some() {
                return None;
            }
            let name = id_text(&first).into_owned();
            let function_like = name.chars().next().is_some_and(char::is_lowercase);
            // An upper-case head may be a union case binding nothing.
            let no_args = l.args().next().is_none() && l.name_pat_pairs().is_none();
            (function_like && (no_args || top) && l.name_pat_pairs().is_none()).then_some(name)
        }
        Pat::Paren(p) => p.inner().as_ref().and_then(|p| binding_name_at(p, false)),
        Pat::Typed(t) => t.pat().as_ref().and_then(|p| binding_name_at(p, top)),
        Pat::Attrib(a) => a.pat().as_ref().and_then(|p| binding_name_at(p, top)),
        // A pattern binding no single name, or several.
        Pat::Wildcard(_)
        | Pat::Const(_)
        | Pat::MeasureLit(_)
        | Pat::Null(_)
        | Pat::Tuple(_)
        | Pat::As(_)
        | Pat::ArrayOrList(_)
        | Pat::Record(_)
        | Pat::IsInst(_)
        | Pat::ListCons(_)
        | Pat::Ands(_)
        | Pat::Or(_)
        | Pat::OptionalVal(_)
        | Pat::Quote(_) => None,
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
