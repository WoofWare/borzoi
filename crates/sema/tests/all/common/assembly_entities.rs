//! The `assembly-entities` oracle: every entity a referenced assembly
//! declares, at every accessibility, from two independent readers.
//!
//! `fcs-dump`'s resident `file-batch` child checks an anchor file against the
//! request's refs, then reports, for each ref:
//!
//! * **FCS's view** ([`FcsEntities`]): a recursive walk of the loaded
//!   assembly's `Contents.Entities`, every entity and every nested entity,
//!   whatever its accessibility. For an F# assembly this is the pickled
//!   signature, so it holds abbreviations, measures and exceptions but no
//!   compiler-generated type, and no entity a `.fsi` leaves out. FCS cannot
//!   tell a referenced assembly's `internal` from its `private`: both read
//!   [`FcsAccess::Private`].
//! * **An IL reader's view** ([`IlEntities`]): one row per `TypeDefinition`,
//!   read with `System.Reflection.Metadata`, `<Module>` and nested types
//!   included.
//!
//! Each view also lists the assembly's *extension universe*: every member
//! that might be an extension, whatever its container
//! ([`FcsExtensionMember`], [`IlExtensionMethod`]).
//!
//! Neither view filters by accessibility, which is the point: the oracle
//! grades an index that answers "does anything of any accessibility exist at
//! this path".

use std::path::Path;

use serde::Deserialize;

pub use borzoi_oracle_harness::assembly_entities::{
    ExtensionStyle, FcsAccess, FcsEntity, FcsEntityKind, FcsExtensionMember,
};

/// The oracle's answer for one request: one entry per ref, in request order.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct AssemblyEntitiesReport {
    pub assemblies: Vec<AssemblyEntities>,
}

/// Both readers' views of one referenced file.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct AssemblyEntities {
    /// The file's absolute path, as the oracle normalised it.
    pub file: String,
    pub fcs: FcsEntities,
    pub il: IlEntities,
}

/// FCS's view of one referenced file.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct FcsEntities {
    /// Whether FCS loaded the file as one of the check's referenced
    /// assemblies (matched by full path, case-insensitively).
    pub seen: bool,
    /// An exception the walk raised as a whole; `entities` is then empty.
    pub error: Option<String>,
    pub entities: Vec<FcsEntity>,
    /// Every member of every entity in `entities` (abbreviations aside) that
    /// might be an extension. Identical rows are merged, so overloads of one
    /// name are one row.
    pub extension_members: Vec<FcsExtensionMember>,
    /// A property read that threw for one entity or member: that entity or
    /// member has no row, and this names it and the property.
    pub read_errors: Vec<String>,
}

/// The IL reader's view of one referenced file.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct IlEntities {
    /// An exception reading the file; `rows` is then empty.
    pub error: Option<String>,
    pub rows: Vec<IlTypeDef>,
    /// Every method that might be an extension, in method order.
    pub extension_methods: Vec<IlExtensionMethod>,
}

/// One `MethodDefinition` that carries
/// `System.Runtime.CompilerServices.ExtensionAttribute`, or is an accessor
/// (getter, setter, adder, remover, raiser or other) of a property or event
/// that does; or that carries, or is such an accessor of one that carries, an
/// attribute whose type cannot be named. An F# extension member carries no
/// attribute, so it is not here.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct IlExtensionMethod {
    /// The outermost enclosing type's namespace.
    pub namespace: String,
    /// The metadata names of the enclosing types, outermost first, the
    /// declaring type included.
    pub enclosing: Vec<String>,
    /// The method's metadata name.
    pub name: String,
    pub is_static: bool,
    /// An attribute that made the method count has a type that cannot be
    /// named, so it might not be `ExtensionAttribute`.
    pub unreadable_attribute: bool,
}

/// One `TypeDefinition` row.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct IlTypeDef {
    /// The dotted namespace; a nested type's is its outermost enclosing
    /// type's.
    pub namespace: String,
    /// The metadata names of the enclosing types, outermost first.
    pub enclosing: Vec<String>,
    /// The metadata name, `` `n `` arity suffix kept.
    pub name: String,
    pub visibility: IlVisibility,
    /// Some custom attribute's constructor names
    /// `Microsoft.FSharp.Core.AutoOpenAttribute` as its type.
    pub auto_open: bool,
    /// Likewise, `System.Runtime.CompilerServices.ExtensionAttribute`.
    pub extension: bool,
    /// Some custom attribute's type could not be named from its constructor
    /// (a `TypeSpecification` parent, say), so `auto_open` and `extension`
    /// may be false for want of reading it.
    pub unreadable_attribute: bool,
}

/// The `TypeAttributes.VisibilityMask` value of a `TypeDefinition`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
pub enum IlVisibility {
    NotPublic,
    Public,
    NestedPublic,
    NestedPrivate,
    NestedFamily,
    NestedAssembly,
    #[serde(rename = "NestedFamANDAssem")]
    NestedFamAndAssem,
    #[serde(rename = "NestedFamORAssem")]
    NestedFamOrAssem,
}

/// Ask the oracle for every entity each of `refs` declares, checking `anchor`
/// (any `.fs` file) against them to load them.
///
/// Routed through the resident `file-batch` pool, as every single-file kind
/// is; a failed check panics with FCS's message.
pub fn invoke_fcs_dump_assembly_entities(anchor: &Path, refs: &[&Path]) -> AssemblyEntitiesReport {
    let line = super::invoke_fcs_dump_with_refs("assembly-entities", anchor, refs);
    let report: AssemblyEntitiesReport = serde_json::from_str(&line)
        .unwrap_or_else(|e| panic!("fcs-dump assembly-entities JSON shape: {e}\n{line}"));
    assert_eq!(
        report.assemblies.len(),
        refs.len(),
        "assembly-entities answered for a different number of refs"
    );
    report
}
