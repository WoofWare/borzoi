//! The extension-scope gate's grid (#794): which method calls inference may
//! commit while an extension member of some name may be in scope, graded by
//! FCS checking the same files as one project.
//!
//! # What the gate claims
//!
//! A method call `recv.M(…)` is committed only when no extension member named
//! `M` can join FCS's method group (`ExtensionScope::decline`). The claim is
//! per name: an extension competes only within its own name's group. So every
//! cell declares at most one extension source, of one [`Kind`], somewhere
//! relative to a file that calls
//!
//! - `(asTable x).ContainsKey(1)` on a `System.Collections.Hashtable`, whose
//!   intrinsic `ContainsKey(obj)` returns `bool`;
//! - `(asTable x).ContainsValue(1)`, a name no project declaration here
//!   declares, but the fixture does, behind namespaces no cell opens;
//! - `"abc".Normalize()`, a name a referenced assembly declares an extension
//!   of (`System.StringNormalizationExtensions`) in a namespace no cell opens;
//! - `"abc".Equals(1)`, whose literal receiver needs no resolution, so the
//!   resolver can never decline the call before the gate is asked;
//! - `(asTable x).Clone()`, a name no extension anywhere declares, so the one
//!   call even an `open` the resolver does not enumerate lets pass.
//!
//! Every extension a cell declares takes an `int` and returns `int64`, so
//! where FCS binds it over the intrinsic (the better fit for `1`), a gate that
//! let the intrinsic group stand commits `bool` where FCS says `int64`: the
//! soundness check sees a type mismatch, not an agreement.
//!
//! # The dimensions
//!
//! - [`Kind`]: what declares the extension, including the shapes that look
//!   like one and are not, and type abbreviations of the fixture's extension
//!   classes.
//! - [`Relation`]: what the extension extends, relative to the receiver. The
//!   gate is receiver-blind, so this never moves its verdict; it moves which
//!   member FCS binds, which is what soundness grades. `StringEquals` names
//!   the extension `Equals` on `string`, for the literal call.
//! - [`Placement`]: where the extension is declared and how the calling file
//!   reaches it.
//! - [`OpenShape`]: an assembly-side `open` in the calling file.
//!
//! # The properties
//!
//! 1. Certain-implies-exact soundness in every file.
//! 2. **The gate's input**, per call: [`expected`] says, from the cell's
//!    dimensions alone, which input of the gate declines the call, or none.
//!    The gate is asked directly, so a call the resolver declines before
//!    inference reaches the gate is still graded. A call no input declines
//!    must be committed (unless its receiver is one the resolver cannot name,
//!    [`receiver_named`]); a declined call must not be.
//! 3. **The design covers FCS**: wherever FCS binds a call to an extension,
//!    `expected` declines it. The kinds and open shapes FCS binds through are
//!    pinned ([`FCS_BINDS_KINDS`], [`FCS_BINDS_OPENS`]), so a cell that stops
//!    discriminating fails.
//!
//! `expected` is the design, not a measurement of FCS, and it is coarser than
//! FCS: an extension FCS would not bind (out of scope, inapplicable to the
//! receiver, losing to the intrinsic) still declines the call of its name.
//!
//! `BORZOI_EXT_GRID_FILTER=<substring>` runs only the cells whose label
//! (`Kind/Relation/Placement/open=Shape`) contains it.

use crate::common::ext_scope::{Call, CallOutcome, check};
use borzoi_oracle_harness::par_map::par_map;
use borzoi_sema::{GateInput, Incomplete, NamesUnknowable};

/// What declares the extension (or something shaped like one).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// No extension source at all: the control.
    None,
    /// `type R with member this.N(i: int) = 0L`.
    FsMethod,
    /// `type R with member this.N = fun (i: int) -> 0L`: an extension
    /// *property* of the call's name.
    FsProperty,
    /// `type R with static member N(i: int) = 0L`: joins only a type-qualified
    /// call's group, never an instance call's.
    FsStatic,
    /// A C#-style `[<Extension>]` static member in an `[<Extension>]` type.
    CsStyle,
    /// The same, with no marker on the type (F#'s
    /// `CSharpExtensionAttributeNotRequired`, for a type of this compilation).
    CsNoTypeAttr,
    /// The same, marked through a project abbreviation of
    /// `ExtensionAttribute` in the same file.
    CsAbbrevAttr,
    /// The same, marked through an abbreviation declared in an earlier file,
    /// written qualified (`[<Aliases.ExtAttrAlias>]`).
    CsAliasEarlierFile,
    /// The same, in a generic container type (`type E<'a>`).
    CsGenericContainer,
    /// An `[<Extension>]` static member in an *intrinsic* augmentation of a
    /// project type: a C#-style member of that type, which FCS binds.
    CsInIntrinsicAugmentation,
    /// An `[<Extension>]` *instance* member: not an extension (FCS requires a
    /// static method).
    CsInstanceMember,
    /// An `[<Extension>]` module `let`: not an extension (a module value is no
    /// member of the module's type).
    ExtAttrOnLet,
    /// The marker on a type alone: not an extension (FCS requires the
    /// method's own marker).
    ExtAttrOnTypeOnly,
    /// A static member named `N` under an attribute the resolver cannot pin
    /// (`System.Obsolete`, qualified): may be the marker as far as the
    /// resolver knows; FCS says it is not.
    DeferredAttrOnStatic,
    /// A module `let` named `N` under such an attribute.
    DeferredAttrOnLet,
    /// `[<CompiledName("N")>] member this.Other`: the extension's logical name
    /// is `Other`.
    CompiledNameAway,
    /// `[<CompiledName("Other")>] member this.N`: its logical name is `N`.
    CompiledNameTo,
    /// `[<Extension>] type A = ExtUniverse.Cs.CsExts`: the fixture class's
    /// `ContainsKey` is in scope wherever the abbreviation is.
    ExtAttrOnAbbrev,
    /// `[<AutoOpen>] type A = ExtUniverse.Str.StrExts`: the fixture class's
    /// `Equals` is in scope wherever the abbreviation is.
    AutoOpenOnAbbrev,
    /// `type A = ExtUniverse.Cs.CsExts`: brings nothing.
    PlainAbbrev,
    /// `#r "Nowhere.dll"`: an assembly outside the project's references.
    HashReference,
}

impl Kind {
    const ALL: [Kind; 21] = [
        Kind::None,
        Kind::FsMethod,
        Kind::FsProperty,
        Kind::FsStatic,
        Kind::CsStyle,
        Kind::CsNoTypeAttr,
        Kind::CsAbbrevAttr,
        Kind::CsAliasEarlierFile,
        Kind::CsGenericContainer,
        Kind::CsInIntrinsicAugmentation,
        Kind::CsInstanceMember,
        Kind::ExtAttrOnLet,
        Kind::ExtAttrOnTypeOnly,
        Kind::DeferredAttrOnStatic,
        Kind::DeferredAttrOnLet,
        Kind::CompiledNameAway,
        Kind::CompiledNameTo,
        Kind::ExtAttrOnAbbrev,
        Kind::AutoOpenOnAbbrev,
        Kind::PlainAbbrev,
        Kind::HashReference,
    ];

    /// A `type R with` augmentation, which must name a concrete type.
    fn is_augmentation(self) -> bool {
        matches!(
            self,
            Kind::FsMethod
                | Kind::FsProperty
                | Kind::FsStatic
                | Kind::CompiledNameAway
                | Kind::CompiledNameTo
        )
    }

    /// Declares a type `E`, which `open type` can name.
    fn declares_type_e(self) -> bool {
        matches!(
            self,
            Kind::CsStyle
                | Kind::CsNoTypeAttr
                | Kind::CsAbbrevAttr
                | Kind::CsAliasEarlierFile
                | Kind::CsInstanceMember
                | Kind::ExtAttrOnTypeOnly
                | Kind::DeferredAttrOnStatic
        )
    }

    /// Declares a module `let` or a directive, which cannot sit directly in
    /// a namespace.
    fn needs_module(self) -> bool {
        matches!(
            self,
            Kind::ExtAttrOnLet | Kind::DeferredAttrOnLet | Kind::HashReference
        )
    }

    /// Whether the declaration names nothing of the relation's: it
    /// abbreviates a fixture class or is a directive.
    fn relation_blind(self) -> bool {
        matches!(
            self,
            Kind::None
                | Kind::ExtAttrOnAbbrev
                | Kind::AutoOpenOnAbbrev
                | Kind::PlainAbbrev
                | Kind::HashReference
        )
    }

    fn relations(self) -> &'static [Relation] {
        if self.relation_blind() {
            &[Relation::Exact]
        } else if self.is_augmentation() {
            &[
                Relation::Exact,
                Relation::Interface,
                Relation::Base,
                Relation::Unrelated,
                Relation::StringEquals,
            ]
        } else {
            &Relation::ALL
        }
    }

    /// The declaration, unindented, one line per element.
    fn decl(self, relation: Relation) -> Vec<String> {
        let r = relation.type_text();
        let n = relation.name();
        let lines: Vec<String> = match self {
            Kind::None => vec![],
            Kind::FsMethod => vec![
                format!("type {r} with"),
                format!("    member this.{n}(i: int) = 0L"),
            ],
            Kind::FsProperty => vec![
                format!("type {r} with"),
                format!("    member this.{n} = fun (i: int) -> 0L"),
            ],
            Kind::FsStatic => vec![
                format!("type {r} with"),
                format!("    static member {n}(i: int) = 0L"),
            ],
            Kind::CsStyle => vec![
                "[<Extension>]".into(),
                "type E =".into(),
                "    [<Extension>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsNoTypeAttr => vec![
                "type E =".into(),
                "    [<Extension>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsAbbrevAttr => vec![
                "type ExtAttr = System.Runtime.CompilerServices.ExtensionAttribute".into(),
                "[<ExtAttr>]".into(),
                "type E =".into(),
                "    [<ExtAttr>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsAliasEarlierFile => vec![
                "[<Aliases.ExtAttrAlias>]".into(),
                "type E =".into(),
                "    [<Aliases.ExtAttrAlias>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsGenericContainer => vec![
                "[<Extension>]".into(),
                "type G<'a> =".into(),
                "    [<Extension>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsInIntrinsicAugmentation => vec![
                "type H() = class end".into(),
                "type H with".into(),
                "    [<Extension>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::CsInstanceMember => vec![
                "type E() =".into(),
                "    [<Extension>]".into(),
                format!("    member _.{n}(x: {r}, i: int) = 0L"),
            ],
            Kind::ExtAttrOnLet => vec![
                "[<Extension>]".into(),
                format!("let {n} (x: {r}, i: int) = 0L"),
            ],
            Kind::ExtAttrOnTypeOnly => vec![
                "[<Extension>]".into(),
                "type E =".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::DeferredAttrOnStatic => vec![
                "type E =".into(),
                "    [<System.Obsolete(\"x\")>]".into(),
                format!("    static member {n}(x: {r}, i: int) = 0L"),
            ],
            Kind::DeferredAttrOnLet => vec![
                "[<System.Obsolete(\"x\")>]".into(),
                format!("let {n} (x: {r}, i: int) = 0L"),
            ],
            Kind::CompiledNameAway => vec![
                format!("type {r} with"),
                format!("    [<CompiledName(\"{n}\")>]"),
                "    member this.Other(i: int) = 0L".into(),
            ],
            Kind::CompiledNameTo => vec![
                format!("type {r} with"),
                "    [<CompiledName(\"Other\")>]".into(),
                format!("    member this.{n}(i: int) = 0L"),
            ],
            Kind::ExtAttrOnAbbrev => vec![
                "[<Extension>]".into(),
                "type A = ExtUniverse.Cs.CsExts".into(),
            ],
            Kind::AutoOpenOnAbbrev => vec![
                "[<AutoOpen>]".into(),
                "type A = ExtUniverse.Str.StrExts".into(),
            ],
            Kind::PlainAbbrev => vec!["type A = ExtUniverse.Cs.CsExts".into()],
            Kind::HashReference => vec!["#r \"Nowhere.dll\"".into()],
        };
        lines
    }

    /// The instance-group names the design reads off this declaration: an
    /// augmentation member of that logical name, or a member under an
    /// attribute that may be the marker (whatever it is, an instance member
    /// or one in an intrinsic augmentation included). A module `let`, a
    /// marker on a type alone, or a static augmentation member contributes
    /// none.
    fn contributes_instance_name(self) -> bool {
        matches!(
            self,
            Kind::FsMethod
                | Kind::FsProperty
                | Kind::CsStyle
                | Kind::CsNoTypeAttr
                | Kind::CsAbbrevAttr
                | Kind::CsAliasEarlierFile
                | Kind::CsGenericContainer
                | Kind::CsInIntrinsicAugmentation
                | Kind::CsInstanceMember
                | Kind::DeferredAttrOnStatic
                | Kind::CompiledNameTo
        )
    }

    /// Why the design reads no name as absent, for a kind that declares
    /// something it cannot enumerate.
    fn unknowable(self) -> Option<NamesUnknowable> {
        match self {
            Kind::ExtAttrOnAbbrev | Kind::AutoOpenOnAbbrev => {
                Some(NamesUnknowable::AttributedAbbreviation)
            }
            Kind::HashReference => Some(NamesUnknowable::HashReference),
            _ => None,
        }
    }
}

/// What the extension extends, relative to the receiver, and the name it
/// declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Relation {
    Exact,
    Interface,
    Base,
    /// A C#-style generic `this` (`x: 'T`).
    Generic,
    Unrelated,
    /// `Equals` on `string`, against the literal `"abc".Equals(1)`.
    StringEquals,
}

impl Relation {
    const ALL: [Relation; 6] = [
        Relation::Exact,
        Relation::Interface,
        Relation::Base,
        Relation::Generic,
        Relation::Unrelated,
        Relation::StringEquals,
    ];

    fn type_text(self) -> &'static str {
        match self {
            Relation::Exact => "System.Collections.Hashtable",
            Relation::Interface => "System.Collections.IDictionary",
            Relation::Base => "System.Object",
            Relation::Generic => "'T",
            Relation::Unrelated | Relation::StringEquals => "System.String",
        }
    }

    fn name(self) -> &'static str {
        match self {
            Relation::StringEquals => "Equals",
            _ => "ContainsKey",
        }
    }
}

/// Where the extension is declared, and how the calling file reaches it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Placement {
    /// In the calling file, before the calls, in its own module.
    OwnTop,
    /// In the calling file, after the calls, in a `module rec`.
    OwnRecAfter,
    /// In a nested module of the calling file that is never opened.
    OwnNestedUnopened,
    /// In a nested module of the calling file, then `open`ed.
    OwnNestedOpened,
    /// In an earlier file's module, which the calling file opens.
    EarlierOpened,
    /// In an earlier file's `[<AutoOpen>]` module, whose namespace the
    /// calling file opens.
    EarlierAutoOpen,
    /// In an earlier file's namespace, which the calling file also declares.
    EarlierSameNamespace,
    /// In an earlier file's module, which the calling file never opens.
    EarlierUnopened,
    /// In an earlier file's module, whose type `E` the calling file opens with
    /// `open type`.
    EarlierOpenType,
    /// As [`Self::EarlierOpened`], with the declaration's last line cut short,
    /// so that the parser has to recover from the earlier file.
    EarlierDamaged,
}

impl Placement {
    const ALL: [Placement; 10] = [
        Placement::OwnTop,
        Placement::OwnRecAfter,
        Placement::OwnNestedUnopened,
        Placement::OwnNestedOpened,
        Placement::EarlierOpened,
        Placement::EarlierAutoOpen,
        Placement::EarlierSameNamespace,
        Placement::EarlierUnopened,
        Placement::EarlierOpenType,
        Placement::EarlierDamaged,
    ];

    fn applies_to(self, kind: Kind) -> bool {
        match self {
            Placement::EarlierOpenType => kind.declares_type_e(),
            _ if kind == Kind::None => self == Placement::OwnTop,
            // A directive must sit at a file's top level.
            _ if kind == Kind::HashReference => {
                matches!(self, Placement::OwnTop | Placement::EarlierUnopened)
            }
            // A `let` after the calls would take the census's last entries.
            Placement::OwnRecAfter => !kind.needs_module(),
            _ => true,
        }
    }

    /// Whether the calling file holds an `open` the resolver does not
    /// enumerate: an `open type` (#794 PR 2b), or a relative `open N` of the
    /// file's own nested module, whose written path is not the module's (the
    /// certified domain takes only an `open` whose written path names what it
    /// opens; `infer_assembly_extension_grid` holds every form to it).
    fn opens_unenumerated(self) -> bool {
        matches!(
            self,
            Placement::EarlierOpenType | Placement::OwnNestedOpened
        )
    }
}

/// An assembly-side `open` in the calling file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenShape {
    None,
    /// `open System.Collections`: a namespace with no extension of the name.
    Namespace,
    /// `open ExtUniverse.Cs`: a namespace whose `[<Extension>]` type declares
    /// `ContainsKey`.
    NamespaceWithExtension,
    /// `open Nowhere.Special`: an `open` of nothing.
    Unresolved,
    /// `open type System.Math`.
    OpenTypeBcl,
    /// `open Microsoft.FSharp.Core.ExtraTopLevelOperators`: an assembly module.
    BclModule,
    /// `open ExtUniverse.FsExts`: an assembly module declaring an F#
    /// extension `ContainsKey`.
    FixtureModule,
    /// `open ExtUniverse.Outer`: an assembly module whose nested
    /// `[<AutoOpen>]` module declares one.
    FixtureAutoOpenModule,
    /// `open type ExtUniverse.Cs.CsExts`: an `[<Extension>]` type declaring a
    /// C#-style one.
    FixtureOpenType,
}

impl OpenShape {
    const ALL: [OpenShape; 9] = [
        OpenShape::None,
        OpenShape::Namespace,
        OpenShape::NamespaceWithExtension,
        OpenShape::Unresolved,
        OpenShape::OpenTypeBcl,
        OpenShape::BclModule,
        OpenShape::FixtureModule,
        OpenShape::FixtureAutoOpenModule,
        OpenShape::FixtureOpenType,
    ];

    fn line(self) -> Option<&'static str> {
        match self {
            OpenShape::None => None,
            OpenShape::Namespace => Some("open System.Collections"),
            OpenShape::NamespaceWithExtension => Some("open ExtUniverse.Cs"),
            OpenShape::Unresolved => Some("open Nowhere.Special"),
            OpenShape::OpenTypeBcl => Some("open type System.Math"),
            OpenShape::BclModule => Some("open Microsoft.FSharp.Core.ExtraTopLevelOperators"),
            OpenShape::FixtureModule => Some("open ExtUniverse.FsExts"),
            OpenShape::FixtureAutoOpenModule => Some("open ExtUniverse.Outer"),
            OpenShape::FixtureOpenType => Some("open type ExtUniverse.Cs.CsExts"),
        }
    }

    /// Whether the resolver leaves this `open`'s extension surface
    /// un-enumerated: everything but a namespace (assembly modules and
    /// `open type`, #794 PR 2b; an unresolved path).
    fn not_enumerated(self) -> bool {
        !matches!(
            self,
            OpenShape::None | OpenShape::Namespace | OpenShape::NamespaceWithExtension
        )
    }
}

/// One project: an extension source, where it is, and an assembly-side open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cell {
    kind: Kind,
    relation: Relation,
    placement: Placement,
    open: OpenShape,
}

/// The calls every cell makes, last in the calling module. The `Hashtable`
/// receiver is typed through [`PREAMBLE`], declared before any `open`: an
/// `open` of a project module, or an `open type`, leaves the resolver unable
/// to pin a dotted type path written after it.
const CALLS: [Call; 5] = [
    Call {
        binder: "c1",
        text: "(asTable x).ContainsKey(1)",
    },
    Call {
        binder: "c2",
        text: "(asTable x).ContainsValue(1)",
    },
    Call {
        binder: "c3",
        text: "\"abc\".Normalize()",
    },
    Call {
        binder: "c4",
        text: "\"abc\".Equals(1)",
    },
    Call {
        binder: "c5",
        text: "(asTable x).Clone()",
    },
];

/// The method each of [`CALLS`] names.
const METHODS: [&str; 5] = [
    "ContainsKey",
    "ContainsValue",
    "Normalize",
    "Equals",
    "Clone",
];

const PREAMBLE: &str = "let asTable (h: System.Collections.Hashtable) = h";

/// Which input of the gate the design says declines each of [`CALLS`] in
/// `cell`, computed from the dimensions alone:
///
/// - a project declaration whose names cannot be read declines every call:
///   an attributed abbreviation, a `#r`, or a declaration the parser recovered
///   from that holds an attribute list;
/// - a declaration the parser recovered from declines every name it spells;
/// - otherwise a project declaration declines the calls of the names it
///   contributes, whatever its placement (the project's names are
///   scope-blind);
/// - then an `open` the resolver does not enumerate declines every name;
/// - then an opened assembly namespace declines the names it declares.
///
/// An `open` of a project module or namespace declines nothing.
fn expected(cell: Cell) -> [Option<GateInput>; 5] {
    // The damaged text: the declaration's last line, which the cut damages,
    // with the attribute lines directly above it, which belong to the same
    // declaration.
    let decl = cell.kind.decl(cell.relation);
    let damaged = cell.placement == Placement::EarlierDamaged;
    let damaged_text: Vec<&String> = {
        let mut lines: Vec<&String> = decl.iter().rev().take(1).collect();
        lines.extend(
            decl.iter()
                .rev()
                .skip(1)
                .take_while(|l| l.trim_start().starts_with("[<")),
        );
        lines
    };
    let unknowable = cell.kind.unknowable().or_else(|| {
        // Damaged text holding an attribute list may declare what no token
        // names.
        (damaged && damaged_text.iter().any(|l| l.contains("[<")))
            .then_some(NamesUnknowable::Recovered)
    });
    // Otherwise damaged text may declare any name it spells.
    let spelled = |method: &str| {
        damaged
            && damaged_text.iter().any(|l| {
                l.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .any(|word| word == method)
            })
    };
    let not_enumerated = cell.placement.opens_unenumerated() || cell.open.not_enumerated();
    METHODS.map(|method| {
        if let Some(why) = unknowable {
            Some(GateInput::ProjectUnknowable(why))
        } else if (cell.kind.contributes_instance_name() && method == cell.relation.name())
            || spelled(method)
        {
            Some(GateInput::ProjectName)
        } else if not_enumerated {
            Some(GateInput::OpenNotEnumerated)
        } else if method == "ContainsKey" && cell.open == OpenShape::NamespaceWithExtension {
            Some(GateInput::AssemblyInScope)
        } else {
            None
        }
    })
}

/// Whether the resolver can name the receiver of each of [`CALLS`] in
/// `cell`, so that inference reaches the call. After `open type ExtLib.E` of
/// a project type, or with an `[<AutoOpen>]` abbreviation in scope, a bare
/// name may be one of a type's statics, which the resolver does not
/// enumerate; after an `open` of a namespace holding a project `[<AutoOpen>]`
/// module, one of that module's; in a `module rec`, a declaration after the
/// use. Each way `asTable` declines first. The literal receivers need no name.
fn receiver_named(cell: Cell) -> [bool; 5] {
    let opaque = matches!(
        cell.placement,
        Placement::EarlierOpenType | Placement::OwnRecAfter | Placement::EarlierAutoOpen
    ) || (cell.kind == Kind::AutoOpenOnAbbrev
        && !matches!(
            cell.placement,
            Placement::OwnNestedUnopened | Placement::EarlierUnopened
        ));
    [!opaque, !opaque, true, true, !opaque]
}

/// The kinds whose declaration FCS binds a call to in some cell with no
/// assembly-side open, and the open shapes it binds an extension through with
/// no project source. Pinned both ways: a cell that stops discriminating makes
/// the soundness property vacuous for that kind, and one that starts names a
/// kind the design must decline.
///
/// FCS binds none of the look-alikes: an extension property (the intrinsic
/// method wins), a static augmentation member (an instance call's group takes
/// none), an `[<Extension>]` instance member, module `let` or type-only
/// marker, a member under `[<System.Obsolete>]`, a member whose
/// `[<CompiledName>]` alone is the name, or a plain abbreviation. It does bind
/// an `[<Extension>]` static member of an intrinsic augmentation of a project
/// type, as a C#-style member of that type.
const FCS_BINDS_KINDS: &[Kind] = &[
    Kind::FsMethod,
    Kind::CsStyle,
    Kind::CsNoTypeAttr,
    Kind::CsAbbrevAttr,
    Kind::CsAliasEarlierFile,
    Kind::CsGenericContainer,
    Kind::CsInIntrinsicAugmentation,
    Kind::CompiledNameTo,
    Kind::ExtAttrOnAbbrev,
    Kind::AutoOpenOnAbbrev,
];
const FCS_BINDS_OPENS: &[OpenShape] = &[
    OpenShape::NamespaceWithExtension,
    OpenShape::FixtureModule,
    OpenShape::FixtureAutoOpenModule,
    OpenShape::FixtureOpenType,
];

/// The cells: every kind at every placement and relation with no
/// assembly-side open, then every open shape over a slice of kinds and
/// placements.
fn cells() -> Vec<Cell> {
    let mut out = Vec::new();
    for kind in Kind::ALL {
        for &relation in kind.relations() {
            for placement in Placement::ALL {
                if placement.applies_to(kind) {
                    out.push(Cell {
                        kind,
                        relation,
                        placement,
                        open: OpenShape::None,
                    });
                }
            }
        }
    }
    for open in OpenShape::ALL.into_iter().skip(1) {
        for kind in [
            Kind::None,
            Kind::FsMethod,
            Kind::CsStyle,
            Kind::DeferredAttrOnStatic,
        ] {
            for placement in [Placement::OwnTop, Placement::EarlierOpened] {
                if placement.applies_to(kind) {
                    out.push(Cell {
                        kind,
                        relation: Relation::Exact,
                        placement,
                        open,
                    });
                }
            }
        }
    }
    out
}

fn indent(lines: &[String], n: usize) -> Vec<String> {
    let pad = " ".repeat(n);
    lines.iter().map(|l| format!("{pad}{l}")).collect()
}

/// The cell's files, in Compile order: `Aliases.fs` for a kind that marks
/// through an earlier file's alias, an optional `Ext.fs`, then `Use.fs`,
/// whose last bindings are [`CALLS`].
fn sources(cell: Cell) -> Vec<(&'static str, String)> {
    let mut decl = cell.kind.decl(cell.relation);
    if cell.placement == Placement::EarlierDamaged
        && let Some(last) = decl.last_mut()
    {
        // Cut the last line short: `= 0L` becomes `= (0L +`, and anything
        // else gains an unclosed parenthesis.
        *last = if last.contains("= 0L") {
            last.replacen("= 0L", "= (0L +", 1)
        } else {
            format!("{last} (")
        };
    }
    let srcs = "open System.Runtime.CompilerServices".to_string();
    let open_line: Vec<String> = cell.open.line().map(String::from).into_iter().collect();
    let calls = |n: usize| -> Vec<String> {
        let pad = " ".repeat(n);
        CALLS
            .iter()
            .map(|c| format!("{pad}let {} x = {}", c.binder, c.text))
            .collect()
    };
    let mut out = Vec::new();
    // The oracle reads the project's references off its first file as a
    // script, where `#r "Nowhere.dll"` would fail them all; behind a first
    // file without it, the directive is an ordinary error.
    if cell.kind == Kind::HashReference {
        out.push(("Pre.fs", "module Pre\n".to_string()));
    }
    if cell.kind == Kind::CsAliasEarlierFile {
        out.push((
            "Aliases.fs",
            "module Aliases\ntype ExtAttrAlias = System.Runtime.CompilerServices.ExtensionAttribute\n"
                .to_string(),
        ));
    }
    let mut ext: Option<Vec<String>> = None;
    let mut u: Vec<String> = Vec::new();
    match cell.placement {
        Placement::OwnTop => {
            u.extend(["module Use".into(), PREAMBLE.into(), srcs]);
            u.extend(open_line);
            u.extend(decl);
            u.extend(calls(0));
        }
        Placement::OwnRecAfter => {
            u.extend(["module rec Use".into(), PREAMBLE.into(), srcs]);
            u.extend(open_line);
            u.extend(calls(0));
            u.extend(decl);
        }
        Placement::OwnNestedUnopened | Placement::OwnNestedOpened => {
            u.extend(["module Use".into(), PREAMBLE.into(), srcs]);
            u.extend(open_line);
            u.push("module N =".into());
            u.extend(indent(&decl, 4));
            if cell.placement == Placement::OwnNestedOpened {
                u.push("open N".into());
            }
            u.extend(calls(0));
        }
        Placement::EarlierOpened
        | Placement::EarlierUnopened
        | Placement::EarlierOpenType
        | Placement::EarlierDamaged => {
            let mut e = vec!["module ExtLib".to_string(), srcs];
            e.extend(decl);
            ext = Some(e);
            u.extend(["module Use".into(), PREAMBLE.into()]);
            match cell.placement {
                Placement::EarlierOpened | Placement::EarlierDamaged => {
                    u.push("open ExtLib".into())
                }
                Placement::EarlierOpenType => u.push("open type ExtLib.E".into()),
                _ => {}
            }
            u.extend(open_line);
            u.extend(calls(0));
        }
        Placement::EarlierAutoOpen => {
            let mut e = vec![
                "namespace ExtNs".to_string(),
                srcs,
                "[<AutoOpen>]".into(),
                "module Auto =".into(),
            ];
            e.extend(indent(&decl, 4));
            ext = Some(e);
            u.extend(["module Use".into(), PREAMBLE.into(), "open ExtNs".into()]);
            u.extend(open_line);
            u.extend(calls(0));
        }
        Placement::EarlierSameNamespace => {
            let mut e = vec!["namespace Shared".to_string(), srcs];
            if cell.kind.needs_module() {
                e.extend(["[<AutoOpen>]".into(), "module Auto =".into()]);
                e.extend(indent(&decl, 4));
            } else {
                e.extend(decl);
            }
            ext = Some(e);
            u.extend(["namespace Shared".into(), "module Use =".into()]);
            u.push(format!("    {PREAMBLE}"));
            u.extend(indent(&open_line, 4));
            u.extend(calls(4));
        }
    }
    if let Some(e) = ext {
        out.push(("Ext.fs", e.join("\n") + "\n"));
    }
    out.push(("Use.fs", u.join("\n") + "\n"));
    out
}

fn cell_label(cell: Cell) -> String {
    format!(
        "{:?}/{:?}/{:?}/open={:?}",
        cell.kind, cell.relation, cell.placement, cell.open
    )
}

/// What one cell found.
struct Outcome {
    failures: Vec<String>,
    /// Per call: whether FCS bound it to an extension (typed it `int64`).
    fcs_bound: [bool; 5],
}

fn grade(cell: Cell, unsound: &[String], calls: &[CallOutcome]) -> Outcome {
    let mut failures: Vec<String> = unsound.iter().map(|u| format!("unsound: {u}")).collect();
    let want = expected(cell);
    let named = receiver_named(cell);
    let mut fcs_bound = [false; 5];
    for (k, (call, outcome)) in CALLS.iter().zip(calls).enumerate() {
        fcs_bound[k] = outcome.fcs.as_deref() == Some("System.Int64");
        // Which input declines a damaged file's calls depends on how much of
        // the declaration the parser kept (the damage bound has its own unit
        // tests), so only that some input declines is compared there.
        let same = if cell.placement == Placement::EarlierDamaged {
            outcome.gate.is_some() == want[k].is_some()
        } else {
            outcome.gate == want[k]
        };
        if !same {
            failures.push(format!(
                "`{}`: the gate's input is {:?}, the design's {:?}",
                call.text, outcome.gate, want[k]
            ));
        }
        if want[k].is_some() {
            if outcome.ours.is_some() {
                failures.push(format!(
                    "`{}`: declined by {:?}, yet committed {:?}",
                    call.text, want[k], outcome.ours
                ));
            }
        } else if named[k] {
            if outcome.ours.is_none() {
                failures.push(format!(
                    "`{}`: the gate passes it, yet it is not committed; census {:?}",
                    call.text, outcome.census
                ));
            }
        } else if !outcome
            .census
            .iter()
            .any(|r| matches!(r, Incomplete::NotInFileValue))
        {
            failures.push(format!(
                "`{}`: its receiver was expected to decline before the gate \
                 (`NotInFileValue`); census {:?}",
                call.text, outcome.census
            ));
        }
        if fcs_bound[k] && want[k].is_none() {
            failures.push(format!(
                "`{}`: FCS binds it to an extension, which the design lets pass",
                call.text
            ));
        }
    }
    Outcome {
        failures,
        fcs_bound,
    }
}

#[test]
fn extension_scope_grid() {
    let mut cells = cells();
    let filter = std::env::var("BORZOI_EXT_GRID_FILTER").ok();
    if let Some(filter) = &filter {
        cells.retain(|&c| cell_label(c).contains(filter.as_str()));
    }
    let outcomes = par_map(cells.len(), |i| {
        let checked = check(&sources(cells[i]), &CALLS);
        grade(cells[i], &checked.unsound, &checked.calls)
    });
    let mut binds_kinds: Vec<String> = Vec::new();
    let mut binds_opens: Vec<String> = Vec::new();
    let mut report = String::new();
    let mut failed = 0usize;
    for (cell, o) in cells.iter().zip(&outcomes) {
        if o.fcs_bound.iter().any(|b| *b) {
            let k = format!("{:?}", cell.kind);
            if cell.open == OpenShape::None && !binds_kinds.contains(&k) {
                binds_kinds.push(k);
            }
            let s = format!("{:?}", cell.open);
            if cell.kind == Kind::None && !binds_opens.contains(&s) {
                binds_opens.push(s);
            }
        }
        if !o.failures.is_empty() {
            failed += 1;
            report.push_str(&format!("{}\n", cell_label(*cell)));
            for f in &o.failures {
                report.push_str(&format!("    {f}\n"));
            }
        }
    }
    binds_kinds.sort();
    binds_opens.sort();
    eprintln!(
        "extension-scope grid: {} cells, {failed} failing; FCS binds an extension for kinds \
         {binds_kinds:?}, opens {binds_opens:?}",
        outcomes.len()
    );
    assert!(
        failed == 0,
        "{failed} of {} cells failed:\n{report}",
        outcomes.len()
    );
    if filter.is_none() {
        let mut pinned: Vec<String> = FCS_BINDS_KINDS.iter().map(|k| format!("{k:?}")).collect();
        pinned.sort();
        assert_eq!(
            binds_kinds, pinned,
            "the kinds FCS binds an extension for moved"
        );
        let mut pinned: Vec<String> = FCS_BINDS_OPENS.iter().map(|k| format!("{k:?}")).collect();
        pinned.sort();
        assert_eq!(
            binds_opens, pinned,
            "the open shapes FCS binds an extension through moved"
        );
    }
}

/// A `[<CLIEvent>]` extension member `Changed` compiles to generated
/// `add_Changed` / `remove_Changed` extension methods, which a call can spell:
/// against a type whose intrinsic `add_Changed(obj)` returns `bool`, FCS binds
/// the generated `add_Changed(EventHandler)`. So the member's name declines
/// its accessors' spellings too, whether the attribute resolves to
/// `CLIEventAttribute` (an augmentation member) or is one the resolver cannot
/// pin (a member under an attribute that may be the marker).
#[test]
fn an_event_member_declines_its_accessor_spellings() {
    const CALL: Call = Call {
        binder: "c1",
        text: "(asR x).add_Changed(h)",
    };
    for attribute in ["CLIEvent", "Microsoft.FSharp.Core.CLIEvent"] {
        let src = format!(
            "module Use\n\
             let asR (r: ExtUniverse.Recv.Receiver) = r\n\
             type ExtUniverse.Recv.Receiver with\n    \
             [<{attribute}>]\n    \
             member this.Changed = (new Event<System.EventHandler, System.EventArgs>()).Publish\n\
             let c1 x (h: System.EventHandler) = (asR x).add_Changed(h)\n"
        );
        let checked = check(&[("Use.fs", src)], &[CALL]);
        assert!(
            checked.unsound.is_empty(),
            "[<{attribute}>]: {:?}",
            checked.unsound
        );
        let call = &checked.calls[0];
        assert!(
            call.fcs.as_deref().is_some_and(|t| t != "System.Boolean"),
            "[<{attribute}>]: FCS must bind the generated accessor, or this pins nothing: {:?}",
            call.fcs
        );
        assert_eq!(
            call.gate,
            Some(GateInput::ProjectName),
            "[<{attribute}>]: `add_Changed` is a spelling of `Changed`"
        );
        assert_eq!(call.ours, None, "[<{attribute}>]");
    }
}

/// While a project reference has no built output, the assembly it will build
/// may declare an extension of any name, in a namespace this project shares:
/// a file that opens a project module or namespace declines every call
/// (`GateInput::ProjectOpenReferencesNotBuilt`). A file with no such `open`
/// is graded as the env without the mark grades it.
#[test]
fn an_unbuilt_reference_keeps_every_open_but_an_assembly_namespace_wholesale() {
    let mut cells = Vec::new();
    for (kind, placement) in [
        (Kind::None, Placement::OwnTop),
        (Kind::FsMethod, Placement::OwnTop),
        (Kind::FsMethod, Placement::OwnNestedOpened),
        (Kind::FsMethod, Placement::EarlierOpened),
        (Kind::FsMethod, Placement::EarlierSameNamespace),
        (Kind::FsMethod, Placement::EarlierUnopened),
    ] {
        for open in [OpenShape::None, OpenShape::Namespace, OpenShape::Unresolved] {
            cells.push(Cell {
                kind,
                relation: Relation::Exact,
                placement,
                open,
            });
        }
    }
    let env = crate::common::ext_universe_env_not_built();
    let outcomes = par_map(cells.len(), |i| {
        let checked = crate::common::ext_scope::check_in(env, &sources(cells[i]), &CALLS);
        (checked.unsound, checked.calls)
    });
    let unbuilt = Some(GateInput::ProjectOpenReferencesNotBuilt);
    let mut failures = Vec::new();
    for (cell, (unsound, calls)) in cells.iter().zip(&outcomes) {
        let label = cell_label(*cell);
        failures.extend(unsound.iter().map(|u| format!("{label}: unsound: {u}")));
        let project_open = matches!(
            cell.placement,
            Placement::OwnNestedOpened | Placement::EarlierOpened
        );
        for (k, (call, outcome)) in CALLS.iter().zip(calls).enumerate() {
            let design = expected(*cell)[k];
            let want = match design {
                None | Some(GateInput::OpenNotEnumerated) if project_open => unbuilt,
                other => other,
            };
            if outcome.gate != want {
                failures.push(format!(
                    "{label}: `{}`: the gate's input is {:?}, the design's {want:?}",
                    call.text, outcome.gate
                ));
            }
            if want.is_some() && outcome.ours.is_some() {
                failures.push(format!(
                    "{label}: `{}`: declined by {want:?}, yet committed {:?}",
                    call.text, outcome.ours
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures over {} cells:\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n")
    );
}
