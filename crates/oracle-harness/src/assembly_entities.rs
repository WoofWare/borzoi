//! FCS's rows of a referenced assembly, as `fcs-dump` reports them: the
//! `assembly-entities` kind's entities and extension universe, and the
//! `extension-members` kind's extensions. Both the single-file oracle (a DLL
//! referenced by path) and the project-graph oracle (a project referenced
//! from source, [`crate::project_graph::ReferencedResponse`]) answer in these
//! shapes.

use serde::Deserialize;

/// One member FCS reports that might be an extension (the `assembly-entities`
/// kind's extension universe).
///
/// FCS does not list an IL type's private, internal or
/// family-and-assembly members, nor any member of a non-public IL type: its
/// `MembersFunctionsAndValues` asks for what some F# code could access. An F#
/// type's members, and an F# module's extension members, it lists at every
/// accessibility.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct FcsExtensionMember {
    /// The outermost enclosing entity's namespace.
    pub namespace: String,
    /// The logical names of the enclosing entities, outermost first, the
    /// declaring entity included.
    pub enclosing: Vec<String>,
    pub logical_name: String,
    pub compiled_name: String,
    pub is_instance: bool,
    pub style: ExtensionStyle,
}

/// Why a member is in the extension universe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ExtensionStyle {
    /// FCS reads it as an F# extension member (`IsExtensionMember`). An
    /// extension property is two rows, its value (`get_P`) and its property
    /// (`P`).
    Fsharp,
    /// A method or accessor carrying
    /// `System.Runtime.CompilerServices.ExtensionAttribute`, or an accessor
    /// of a property or event that does, whatever its container.
    Csharp,
}

/// One non-namespace entity, as FCS reports it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct FcsEntity {
    /// The dotted namespace (`""` for the root). A nested entity's is its
    /// outermost enclosing entity's.
    pub namespace: String,
    /// The logical names of the enclosing non-namespace entities, outermost
    /// first.
    pub enclosing: Vec<String>,
    pub logical_name: String,
    pub compiled_name: String,
    pub kind: FcsEntityKind,
    pub access: FcsAccess,
    /// Carries `Microsoft.FSharp.Core.AutoOpenAttribute`.
    pub auto_open: bool,
    /// Carries `System.Runtime.CompilerServices.ExtensionAttribute`.
    pub extension: bool,
}

/// An entity's kind, tested in this order: module, abbreviation, exception,
/// measure; anything else is a type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FcsEntityKind {
    Module,
    Abbreviation,
    Exception,
    Measure,
    Type,
}

/// `FSharpEntity.Accessibility`. For a referenced assembly FCS reads an F#
/// `internal` and an IL `NotPublic`/`NestedAssembly`/`NestedPrivate`/
/// `NestedFamANDAssem` all as `Private`, and an IL `NestedFamily`/
/// `NestedFamORAssem` as `Public`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FcsAccess {
    Public,
    Internal,
    Private,
    Protected,
}

/// One member FCS reads as an extension in a referenced assembly
/// (`fcs-dump`'s `extension-members` kind).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ExtensionMemberRead {
    /// The namespace holding the member's top-level type, dotted.
    #[serde(rename = "Namespace")]
    pub namespace: String,
    #[serde(rename = "Entity")]
    pub entity: String,
    /// The name a call spells.
    #[serde(rename = "Name")]
    pub name: String,
    #[serde(rename = "CompiledName")]
    pub compiled_name: String,
    /// `fsharp` (an optional extension) or `csharp`.
    #[serde(rename = "Style")]
    pub style: String,
    /// Whether a value receiver calls it (else a type-qualified call).
    #[serde(rename = "IsInstance")]
    pub is_instance: bool,
}
