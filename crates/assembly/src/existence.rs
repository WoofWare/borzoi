//! The **existence index**: everything one assembly declares, at every
//! accessibility, read straight from its `TypeDef` table and its host F#
//! signature pickle, with no projection in between.
//!
//! The [`Entity`](crate::Entity) projection is name resolution's view of an
//! assembly, and it filters: it drops what the reader cannot decode, hides
//! what fsc synthesises, and leaves out pickle-only declarations a
//! referencing assembly cannot name (a non-public abbreviation). A question
//! of *existence* ("may anything, of any accessibility, sit at this path?")
//! cannot be answered from a filtered view, because a friend assembly
//! (`InternalsVisibleTo`) sees what the filter took away. This index is the
//! positive domain such questions read instead: two flat layers, each held
//! to an independent reader of the same metadata.
//!
//! - [`IlTypeRow`]: one per `TypeDef` row, `<Module>` and nested types
//!   included. `assembly_entities_diff` holds the layer to
//!   `System.Reflection.Metadata`'s walk of the same table.
//! - [`PickledEntityRow`]: one per entity of the host pickle, namespace
//!   fragments, modules, types, abbreviations, exceptions and measures, at
//!   every accessibility. Abbreviations exist only here. The same
//!   differential holds the layer to FCS's view of the assembly
//!   (`FSharpAssembly.Contents`), which reads the same pickle.
//!
//! A pickle that exists but cannot be read gives [`PickleLayer::Unreadable`],
//! never an empty layer.

use crate::ImportError;
use crate::ecma335_assembly::MAX_NESTING_DEPTH;
use crate::fsharp_pickle::model::{
    IsType, PickledAttribute, PickledCcu, PickledEntity, PickledExnRepr, PickledTcRef, TyparKind,
};
use crate::reader::{Accessibility, Image, TypeDefId};

/// What one assembly declares, at every accessibility.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExistenceIndex {
    /// Every `TypeDef` row.
    pub il: Vec<IlTypeRow>,
    /// Every entity of the host F# signature pickle.
    pub pickle: PickleLayer,
}

/// The pickle layer of an [`ExistenceIndex`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PickleLayer {
    /// The assembly is not F# (it carries no
    /// `FSharpInterfaceDataVersionAttribute`): it declares nothing beyond its
    /// `TypeDef` rows.
    NotFSharp,
    /// The assembly is F#, and its host pickle is missing, failed to decode,
    /// or sits beside foreign CCUs' pickles (`fsc --standalone`): what it
    /// declares beyond its `TypeDef` rows is unknown, and the reason says why.
    Unreadable(String),
    /// Every entity the host pickle declares.
    Read(Vec<PickledEntityRow>),
}

/// The visibility of a `TypeDef` row, by its `TypeAttributes.VisibilityMask`
/// name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IlVisibility {
    NotPublic,
    Public,
    NestedPublic,
    NestedPrivate,
    NestedFamily,
    NestedAssembly,
    NestedFamAndAssem,
    NestedFamOrAssem,
}

/// One `TypeDef` row.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IlTypeRow {
    /// The namespace of the row, or of its outermost enclosing row.
    pub namespace: Vec<String>,
    /// The metadata names of the enclosing rows, outermost first.
    pub enclosing: Vec<String>,
    /// The metadata name, a generic arity suffix (`` `1 ``) included.
    pub name: String,
    pub visibility: IlVisibility,
    /// The row carries `Microsoft.FSharp.Core.AutoOpenAttribute`.
    pub auto_open: bool,
    /// The row carries `System.Runtime.CompilerServices.ExtensionAttribute`.
    pub extension: bool,
    /// Some attribute of the row names an owner the reader cannot read, so
    /// neither flag above is known false.
    pub unreadable_attribute: bool,
}

/// What kind of entity a pickled entity is, in the order FCS's
/// `FSharpEntity` tests them (`IsFSharpModule`, `IsFSharpAbbreviation`,
/// `IsFSharpExceptionDeclaration`, `IsMeasure`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PickledEntityKind {
    Namespace,
    Module,
    Abbreviation,
    Exception,
    Measure,
    Type,
}

/// One entity of the host pickle.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PickledEntityRow {
    /// The enclosing namespace fragments' names.
    pub namespace: Vec<String>,
    /// The logical names of the enclosing modules and types, outermost first.
    pub enclosing: Vec<String>,
    pub logical_name: String,
    /// The `[<CompiledName>]`, else the logical name.
    pub compiled_name: String,
    pub kind: PickledEntityKind,
    /// The entity's own accessibility is public (an empty `TAccess`).
    pub public: bool,
    pub auto_open: bool,
    pub extension: bool,
}

const AUTO_OPEN: [&str; 4] = ["Microsoft", "FSharp", "Core", "AutoOpenAttribute"];
const EXTENSION: [&str; 4] = [
    "System",
    "Runtime",
    "CompilerServices",
    "ExtensionAttribute",
];

/// The `TypeDef` layer of `image`, or a refusal when a row's `NestedClass`
/// chain is deeper than [`MAX_NESTING_DEPTH`]: a cycle, or corrupt metadata
/// no compiler writes, whose paths would cost memory cubic in the table.
pub(crate) fn il_rows(image: &Image) -> Result<Vec<IlTypeRow>, ImportError> {
    image
        .type_defs
        .iter()
        .enumerate()
        .map(|(i, td)| {
            let mut enclosing = Vec::new();
            let mut outermost = i;
            while let Some(TypeDefId(parent)) = image.type_defs[outermost].enclosing {
                if enclosing.len() >= MAX_NESTING_DEPTH {
                    return Err(ImportError::UnsupportedEcmaLayout {
                        detail: format!(
                            "TypeDef row {i}'s nesting chain is cyclic or deeper than \
                             {MAX_NESTING_DEPTH}"
                        ),
                    });
                }
                outermost = parent as usize;
                let Some(encloser) = image.type_defs.get(outermost) else {
                    return Err(ImportError::UnsupportedEcmaLayout {
                        detail: format!("TypeDef row {i} is nested in a missing row {outermost}"),
                    });
                };
                enclosing.push(encloser.name.name.clone());
            }
            enclosing.reverse();
            let namespace = &image.type_defs[outermost].name.namespace;
            let nested = td.enclosing.is_some();
            let visibility = match (nested, td.accessibility) {
                (false, Accessibility::Public) => IlVisibility::Public,
                (false, _) => IlVisibility::NotPublic,
                (true, Accessibility::Public) => IlVisibility::NestedPublic,
                (true, Accessibility::Private) => IlVisibility::NestedPrivate,
                (true, Accessibility::Family) => IlVisibility::NestedFamily,
                (true, Accessibility::Assembly) => IlVisibility::NestedAssembly,
                (true, Accessibility::FamAndAssem) => IlVisibility::NestedFamAndAssem,
                (true, Accessibility::FamOrAssem) => IlVisibility::NestedFamOrAssem,
            };
            let mut auto_open = false;
            let mut extension = false;
            let mut unreadable_attribute = false;
            for raw in &td.attributes {
                match image.attribute_owning_type(raw) {
                    Ok(owner) => {
                        let is = |path: &[&str; 4]| {
                            owner.name == path[3] && owner.namespace == path[..3].join(".")
                        };
                        auto_open |= is(&AUTO_OPEN);
                        extension |= is(&EXTENSION);
                    }
                    Err(_) => unreadable_attribute = true,
                }
            }
            Ok(IlTypeRow {
                namespace: split_namespace(namespace),
                enclosing,
                name: td.name.name.clone(),
                visibility,
                auto_open,
                extension,
                unreadable_attribute,
            })
        })
        .collect()
}

fn split_namespace(namespace: &str) -> Vec<String> {
    if namespace.is_empty() {
        Vec::new()
    } else {
        namespace.split('.').map(str::to_owned).collect()
    }
}

/// One entity the pickle walk has yet to visit.
struct Frame {
    stamp: u32,
    is_root: bool,
    namespace: Vec<String>,
    enclosing: Vec<String>,
    depth: usize,
}

/// The entity layer of the host pickle `pickled`, or why it cannot be read.
pub(crate) fn pickled_rows(pickled: &PickledCcu) -> Result<Vec<PickledEntityRow>, String> {
    // Every entity's full logical path, so an attribute whose type the
    // assembly itself declares (a `Local` tcref, as FSharp.Core's own
    // `[<AutoOpen>]` is) is read as surely as a non-local one.
    let mut paths: Vec<Option<Vec<String>>> = vec![None; pickled.tables.tycons.len()];
    // (stamp, namespace, enclosing) of each entity, depth first, the root
    // excluded.
    let mut order: Vec<(u32, Vec<String>, Vec<String>)> = Vec::new();
    let mut stack: Vec<Frame> = vec![Frame {
        stamp: pickled.root_entity,
        is_root: true,
        namespace: Vec::new(),
        enclosing: Vec::new(),
        depth: 0,
    }];
    while let Some(Frame {
        stamp,
        is_root,
        namespace,
        enclosing,
        depth,
    }) = stack.pop()
    {
        // A valid entity graph is a tree whose depth the tycon table bounds;
        // deeper is a cycle.
        // A valid entity graph is a tree whose depth no compiler takes past
        // the projector's own bound; deeper is a cycle or corrupt, and its
        // paths would cost memory cubic in the depth.
        if depth > MAX_NESTING_DEPTH {
            return Err(format!(
                "the pickle's entity graph is cyclic or deeper than {MAX_NESTING_DEPTH} at stamp {stamp}"
            ));
        }
        let entity = pickled
            .tables
            .tycons
            .get(stamp as usize)
            .ok_or_else(|| format!("entity stamp {stamp} out of range"))?;
        let (child_namespace, child_enclosing) = if is_root {
            (namespace.clone(), enclosing.clone())
        } else {
            let mut full = namespace.clone();
            full.extend(enclosing.iter().cloned());
            full.push(entity.logical_name.clone());
            paths[stamp as usize] = Some(full);
            order.push((stamp, namespace.clone(), enclosing.clone()));
            if kind_of(entity) == PickledEntityKind::Namespace {
                let mut ns = namespace.clone();
                ns.push(entity.logical_name.clone());
                (ns, enclosing.clone())
            } else {
                let mut chain = enclosing.clone();
                chain.push(entity.logical_name.clone());
                (namespace.clone(), chain)
            }
        };
        for &child in entity.module_type.entities.iter().rev() {
            stack.push(Frame {
                stamp: child,
                is_root: false,
                namespace: child_namespace.clone(),
                enclosing: child_enclosing.clone(),
                depth: depth + 1,
            });
        }
    }
    let carries = |attribs: &[PickledAttribute], target: &[&str; 4]| {
        attribs.iter().any(|a| {
            let path: Option<Vec<&str>> = match &a.tcref {
                PickledTcRef::NonLocal(index) => {
                    pickled.header.nlerefs.get(*index as usize).map(|nle| {
                        nle.path
                            .iter()
                            .filter_map(|&i| {
                                pickled.header.strings.get(i as usize).map(String::as_str)
                            })
                            .collect()
                    })
                }
                PickledTcRef::Local(stamp) => paths
                    .get(*stamp as usize)
                    .and_then(Option::as_ref)
                    .map(|p| p.iter().map(String::as_str).collect()),
            };
            path.is_some_and(|p| p == target)
        })
    };
    Ok(order
        .into_iter()
        .map(|(stamp, namespace, enclosing)| {
            let entity = &pickled.tables.tycons[stamp as usize];
            PickledEntityRow {
                namespace,
                enclosing,
                logical_name: entity.logical_name.clone(),
                compiled_name: entity
                    .compiled_name
                    .clone()
                    .unwrap_or_else(|| entity.logical_name.clone()),
                kind: kind_of(entity),
                public: entity.access.is_empty(),
                auto_open: carries(&entity.attribs, &AUTO_OPEN),
                extension: carries(&entity.attribs, &EXTENSION),
            }
        })
        .collect())
}

/// FCS's `EntityFlags.IsModuleOrNamespace` bit.
const MODULE_OR_NAMESPACE: i64 = 0b1;

fn kind_of(entity: &PickledEntity) -> PickledEntityKind {
    if entity.flags & MODULE_OR_NAMESPACE != 0 {
        if entity.module_type.is_type == IsType::Namespace {
            PickledEntityKind::Namespace
        } else {
            PickledEntityKind::Module
        }
    } else if entity.type_abbrev.is_some() {
        PickledEntityKind::Abbreviation
    } else if !matches!(entity.exn_repr, PickledExnRepr::None) {
        PickledEntityKind::Exception
    } else if entity.typar_kind == TyparKind::Measure {
        PickledEntityKind::Measure
    } else {
        PickledEntityKind::Type
    }
}
