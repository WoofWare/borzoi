//! The attribute-placement grid of `source_existence_diff`, derived from the
//! grammar: every node of the syntax tree that carries attribute lists
//! (each type with an `attributes()` accessor in `borzoi-cst`'s
//! `syntax/union.rs`), under every attribute a marker may be written as, at
//! every explicit target and with none.
//!
//! [`templates`] holds one producer per node kind, with the attribute's
//! place marked: the fixed ones in [`BASE`], and for every member node the
//! product of the contexts a member sits in ([`MEMBER_CONTEXTS`]: a class,
//! an optional augmentation of a named, tuple or struct-tuple type, an
//! intrinsic augmentation, an exception, an interface implementation) with
//! its snippets, and of every signature node with the shapes a signature's
//! type takes ([`SIGNATURE_TYPES`]). `every_attribute_bearing_node_has_a_template` holds the table to
//! the grammar: a node kind the parser gains attributes on fails it until it
//! has a template, and a template whose attribute does not land on its node
//! kind fails it too. The grid is then the product, graded like every other
//! cell: the normal suite runs it with no target, `deep_` with every target.

use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_cst::syntax::SyntaxKind;
use borzoi_oracle_harness::manifest::Manifest;

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells};

/// Where an attribute goes in one producer: the files, with `{A}` at the
/// attribute's place, and the node kind it must land on.
struct StaticTemplate {
    /// The node type, as `syntax/union.rs` names it.
    node: &'static str,
    /// A label telling apart templates of one node type.
    label: &'static str,
    files: &'static [(&'static str, &'static str)],
}

/// [`StaticTemplate`], built.
struct Template {
    node: &'static str,
    label: String,
    files: Vec<(String, String)>,
}

/// One producer per attribute-bearing node kind, and per context a member
/// kind's attributes mean something different in.
const BASE: &[StaticTemplate] = &[
    StaticTemplate {
        node: "ModuleOrNamespace",
        label: "module_header",
        files: &[("Lib.fs", "{A}\nmodule G.M\nlet x = 1\n")],
    },
    StaticTemplate {
        node: "NestedModuleDecl",
        label: "nested_module",
        files: &[("Lib.fs", "namespace G\n{A}\nmodule M =\n    let x = 1\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "record",
        files: &[("Lib.fs", "namespace G\n{A}\ntype T = { X: int }\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "abbreviation",
        files: &[("Lib.fs", "namespace G\n{A}\ntype T = int\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "abbreviation_or_union",
        files: &[("Lib.fs", "namespace G\n{A}\ntype T = Somewhere\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "abbreviation_self_named",
        files: &[("Lib.fs", "namespace G\n{A}\ntype T = T\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "abbreviation_self_named_generic",
        files: &[(
            "Lib.fs",
            "namespace G\ntype T = { X: int }\n{A}\ntype T<'a> = T\n",
        )],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "class",
        files: &[(
            "Lib.fs",
            "namespace G\n{A}\ntype T() =\n    member _.P = 1\n",
        )],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "measure",
        files: &[("Lib.fs", "namespace G\n{A}\ntype m\n")],
    },
    StaticTemplate {
        node: "TypeDefn",
        label: "optional_augmentation",
        files: &[(
            "Lib.fs",
            "module G\n{A}\ntype System.String with\n    member s.M() = 1\n",
        )],
    },
    StaticTemplate {
        node: "ExceptionDefnDecl",
        label: "exception",
        files: &[("Lib.fs", "namespace G\n{A}\nexception E of string\n")],
    },
    StaticTemplate {
        node: "LetDecl",
        label: "module_let",
        files: &[("Lib.fs", "module G\n{A}\nlet f (s: string) = s\n")],
    },
    StaticTemplate {
        node: "Binding",
        label: "module_let_binding",
        files: &[("Lib.fs", "module G\nlet {A} f (s: string) = s\n")],
    },
    StaticTemplate {
        node: "ExternDecl",
        label: "extern",
        files: &[(
            "Lib.fs",
            "module G\n{A}\n[<System.Runtime.InteropServices.DllImport(\"libc\")>]\nextern int getpid()\n",
        )],
    },
    StaticTemplate {
        node: "ExternArg",
        label: "extern_argument",
        files: &[(
            "Lib.fs",
            "module G\n[<System.Runtime.InteropServices.DllImport(\"libc\")>]\nextern int abs({A} int x)\n",
        )],
    },
    StaticTemplate {
        node: "AutoProperty",
        label: "auto_property",
        files: &[(
            "Lib.fs",
            "module G\ntype T() =\n    {A}\n    member val P = 1 with get, set\n",
        )],
    },
    StaticTemplate {
        node: "ValField",
        label: "val_field",
        files: &[(
            "Lib.fs",
            "module G\ntype T() =\n    {A}\n    [<DefaultValue>]\n    static val mutable private F: int\n",
        )],
    },
    StaticTemplate {
        node: "ImplicitCtor",
        label: "primary_constructor",
        files: &[(
            "Lib.fs",
            "module G\ntype T {A} (x: int) =\n    member _.X = x\n",
        )],
    },
    StaticTemplate {
        node: "MemberLetBindings",
        label: "class_let",
        files: &[(
            "Lib.fs",
            "module G\ntype T() =\n    {A}\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
        )],
    },
    StaticTemplate {
        node: "TyparDecl",
        label: "type_parameter",
        files: &[("Lib.fs", "namespace G\ntype T<{A} 'u> = { X: int }\n")],
    },
    StaticTemplate {
        node: "AttributesDecl",
        label: "standalone",
        files: &[(
            "Lib.fs",
            "namespace G\nmodule M =\n    let x = 1\n{A}\ndo ()\n",
        )],
    },
    StaticTemplate {
        node: "EnumCase",
        label: "enum_case",
        files: &[("Lib.fs", "namespace G\ntype E =\n    | {A} One = 1\n")],
    },
    StaticTemplate {
        node: "UnionCase",
        label: "union_case",
        files: &[(
            "Lib.fs",
            "namespace G\ntype U =\n    | {A} One\n    | Two\n",
        )],
    },
    StaticTemplate {
        node: "RecordFieldDecl",
        label: "record_field",
        files: &[("Lib.fs", "namespace G\ntype R = { {A} X: int }\n")],
    },
    StaticTemplate {
        node: "AttribPat",
        label: "pattern",
        files: &[("Lib.fs", "module G\nlet f ({A} s: string) = s\n")],
    },
    StaticTemplate {
        node: "SignatureParameterType",
        label: "signature_parameter",
        files: &[
            ("Lib.fsi", "module G\nval f: {A} s: string -> string\n"),
            ("Lib.fs", "module G\nlet f s = s\n"),
        ],
    },
];

/// Where a member sits: the file's head, the member's indent, and a value of
/// the declaring type a constructor may return. `None` for a context that
/// takes no constructor.
const MEMBER_CONTEXTS: &[(&str, &str, &str, Option<&str>)] = &[
    ("class", "module G\ntype T() =\n", "    ", Some("T()")),
    (
        "optional_augmentation",
        "module G\ntype System.String with\n",
        "    ",
        Some("\"\""),
    ),
    (
        "tuple_augmentation",
        "module G\ntype (int * int) with\n",
        "    ",
        Some("(1, 2)"),
    ),
    (
        "struct_tuple_augmentation",
        "module G\ntype struct (int * string * bool) with\n",
        "    ",
        Some("struct (1, \"\", true)"),
    ),
    (
        "intrinsic_augmentation",
        "module G\ntype R = { X: int }\ntype R with\n",
        "    ",
        Some("{ X = 1 }"),
    ),
    (
        "exception",
        "module G\nexception E of string\n    with\n",
        "        ",
        None,
    ),
    (
        "interface_implementation",
        "module G\ntype I =\n    abstract M: string -> string\n    abstract P: int\n    abstract Ev: IEvent<int>\ntype T() =\n    interface I with\n",
        "        ",
        None,
    ),
];

/// The member snippets every context takes: the node, a label, and the
/// snippet (`{I}` the indent, `{A}` the attribute, `{C}` the constructor's
/// value).
const MEMBER_SNIPPETS: &[(&str, &str, &str)] = &[
    (
        "MemberMethod",
        "method",
        "{I}{A}\n{I}member x.M(s: string) = s\n",
    ),
    (
        "MemberMethod",
        "static_method",
        "{I}{A}\n{I}static member M(s: string) = s\n",
    ),
    ("MemberMethod", "property", "{I}{A}\n{I}member x.P = 1\n"),
    (
        "MemberMethod",
        "constructor",
        "{I}{A}\n{I}new(s: string) = {C}\n",
    ),
    (
        "GetSetMember",
        "get_set",
        "{I}{A}\n{I}member x.P with get () = 1 and set (v: int) = ()\n",
    ),
    (
        "GetSetAccessor",
        "getter",
        "{I}member x.P with {A} get () = 1 and set (v: int) = ()\n",
    ),
    (
        "GetSetAccessor",
        "setter",
        "{I}member x.P with get () = 1 and {A} set (v: int) = ()\n",
    ),
    (
        "GetSetAccessor",
        "event_getter",
        "{I}member x.Ev with {A} get () = Event<int>().Publish\n",
    ),
    (
        "MemberMethod",
        "event",
        "{I}{A}\n{I}member x.Ev = Event<int>().Publish\n",
    ),
    // A `let` in every context: the type's own, an augmentation's (where
    // FCS rejects it, or for an intrinsic one compiles it into the type).
    (
        "MemberLetBindings",
        "class_let",
        "{I}{A}\n{I}static let f (s: string) = s\n{I}static member UseF = f \"x\"\n",
    ),
];

/// The shapes a signature's type takes, which decide whether its member is
/// a method or a property.
const SIGNATURE_TYPES: &[(&str, &str)] = &[
    ("function", "s: string -> string"),
    ("constrained", "s: 'T -> bool when 'T: equality"),
    ("tupled", "a: int * b: int -> int"),
    ("property", "int"),
    ("property_get_set", "int with get, set"),
];

/// Every template: [`BASE`], each member snippet in each context, and each
/// signature node under each signature type.
fn templates() -> Vec<Template> {
    let mut out: Vec<Template> = BASE
        .iter()
        .map(|t| Template {
            node: t.node,
            label: t.label.to_owned(),
            files: t
                .files
                .iter()
                .map(|(n, f)| ((*n).to_owned(), (*f).to_owned()))
                .collect(),
        })
        .collect();
    for (context, head, indent, ctor) in MEMBER_CONTEXTS {
        for (node, label, snippet) in MEMBER_SNIPPETS {
            let Some(value) = ctor.or(if snippet.contains("{C}") {
                None
            } else {
                Some("")
            }) else {
                continue;
            };
            let body = snippet.replace("{I}", indent).replace("{C}", value);
            out.push(Template {
                node,
                label: format!("{context}_{label}"),
                files: vec![("Lib.fs".to_owned(), format!("{head}{body}"))],
            });
        }
    }
    for (shape, ty) in SIGNATURE_TYPES {
        // A signature file's augmentation: no representation, its `with`
        // directly on the definition, its members signatures.
        out.push(Template {
            node: "MemberSig",
            label: format!("signature_augmentation_{shape}"),
            files: vec![
                (
                    "Lib.fsi".to_owned(),
                    format!("module G\ntype System.String with\n    {{A}}\n    member S: {ty}\n"),
                ),
                (
                    "Lib.fs".to_owned(),
                    "module G\ntype System.String with\n    member s.S = 1\n".to_owned(),
                ),
            ],
        });
        out.push(Template {
            node: "MemberSig",
            label: format!("member_signature_{shape}"),
            files: vec![(
                "Lib.fsi".to_owned(),
                format!("module G\n[<Class>]\ntype T =\n    new: unit -> T\n    {{A}}\n    abstract M: {ty}\n"),
            ), (
                "Lib.fs".to_owned(),
                "module G\n[<AbstractClass>]\ntype T() =\n    abstract M: int\n".to_owned(),
            )],
        });
        out.push(Template {
            node: "AbstractSlot",
            label: format!("abstract_slot_{shape}"),
            files: vec![(
                "Lib.fs".to_owned(),
                format!(
                    "module G\n[<AbstractClass>]\ntype T() =\n    {{A}}\n    abstract M: {ty}\n"
                ),
            )],
        });
        // A module's `val` takes no accessor clause.
        if ty.contains(" with ") {
            continue;
        }
        out.push(Template {
            node: "ValDecl",
            label: format!("signature_val_{shape}"),
            files: vec![
                (
                    "Lib.fsi".to_owned(),
                    format!("module G\n{{A}}\nval f: {ty}\n"),
                ),
                ("Lib.fs".to_owned(), "module G\nlet f = 1\n".to_owned()),
            ],
        });
    }
    out
}

/// Every attribute a marker may be written as (with the argument it reads),
/// and one that is no marker.
const ATTRIBUTES: &[(&str, &str)] = &[
    ("auto_open", "AutoOpen"),
    ("auto_open_path", "AutoOpen(\"G\")"),
    ("extension", "System.Runtime.CompilerServices.Extension"),
    ("measure", "Measure"),
    ("compiled_name", "CompiledName(\"Renamed\")"),
    (
        "type_provider_assembly",
        "Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly",
    ),
    ("cli_event", "CLIEvent"),
    ("other", "System.Obsolete(\"G\")"),
];

/// Every explicit target F# reads (`LongFormAttrTarget`), and none.
const TARGETS: &[&str] = &[
    "",
    "assembly",
    "module",
    "return",
    "field",
    "property",
    "method",
    "param",
    "type",
    "constructor",
    "event",
];

/// An attribute drawn from the placement grid's product: any marker's
/// spelling, or none, at any target (most often none).
pub fn random_attribute(rng: &mut crate::source_existence_gen::Rng) -> String {
    let (_, text) = ATTRIBUTES[rng.below(ATTRIBUTES.len())];
    let target = if rng.chance(60) {
        ""
    } else {
        TARGETS[rng.below(TARGETS.len())]
    };
    if target.is_empty() {
        format!("[<{text}>]")
    } else {
        format!("[<{target}: {text}>]")
    }
}

/// The cell of `template` under `attribute` at `target`.
fn cell(template: &Template, attribute: (&str, &str), target: &str) -> Cell {
    let (label, text) = attribute;
    let written = if target.is_empty() {
        format!("[<{text}>]")
    } else {
        format!("[<{target}: {text}>]")
    };
    let target_label = if target.is_empty() { "none" } else { target };
    let files: Vec<(String, String)> = template
        .files
        .iter()
        .map(|(n, t)| ((*n).to_owned(), t.replace("{A}", &written)))
        .collect();
    let mut cell = Cell::new(
        format!("placement_{}_{label}_{target_label}", template.label),
        &[],
    );
    cell.files = files;
    cell
}

fn grid(targets: &[&str]) -> Vec<Cell> {
    let templates = templates();
    templates
        .iter()
        .flat_map(|t| {
            ATTRIBUTES
                .iter()
                .flat_map(move |&a| targets.iter().map(move |target| cell(t, a, target)))
        })
        .collect()
}

fn run(targets: &[&str], manifest: &str, test: &str) {
    let cells = grid(targets);
    let (entries, failures) = grade_cells(&cells);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let manifest_entries = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(manifest, &manifest_entries, &regenerate(test));
}

/// Every template under every attribute, with no target.
#[test]
fn every_attribute_at_every_node() {
    run(
        &[""],
        "source_existence_placement",
        "source_existence_placement::every_attribute_at_every_node",
    );
}

/// [`every_attribute_at_every_node`] at every explicit target too.
#[test]
#[ignore = "the full product, a few thousand FCS checks; run before touching attribute reading"]
fn deep_every_attribute_at_every_node_and_target() {
    run(
        TARGETS,
        "source_existence_placement_deep",
        "source_existence_placement::deep_every_attribute_at_every_node_and_target",
    );
}

/// The node types `syntax/union.rs` gives an `attributes()` accessor, but
/// the attribute list's own.
fn attribute_bearing_nodes() -> std::collections::BTreeSet<String> {
    let union = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cst/src/syntax/union.rs");
    let text = std::fs::read_to_string(&union).expect("read syntax/union.rs");
    let mut current: Option<&str> = None;
    let mut nodes = std::collections::BTreeSet::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("impl ") {
            current = rest.strip_suffix(" {");
        }
        if line.trim_start().starts_with("pub fn attributes(&self)")
            && let Some(node) = current
            && node != "AttributeList"
        {
            nodes.insert(node.to_owned());
        }
    }
    nodes
}

/// The syntax kind a node type casts from, as its generated `AstNode`
/// impl names it (`MemberMethod` is a `MEMBER_DEFN`).
fn kind_name(node: &str) -> String {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../cst/src/syntax/generated");
    let header = format!("impl AstNode for {node} {{");
    for entry in std::fs::read_dir(&dir).expect("read the generated syntax") {
        let path = entry.expect("a directory entry").path();
        if path.extension().is_none_or(|e| e != "rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("read a generated file");
        if let Some(at) = text.find(&header) {
            let rest = &text[at..];
            let kind = rest
                .split("SyntaxKind::")
                .nth(1)
                .expect("an AstNode impl names its kind");
            return kind
                .chars()
                .take_while(|c| c.is_ascii_uppercase() || *c == '_')
                .collect();
        }
    }
    panic!("no AstNode impl for {node}")
}

/// The templates cover every attribute-bearing node of the grammar, and each
/// template's attribute lands on its node.
#[test]
fn every_attribute_bearing_node_has_a_template() {
    let grammar = attribute_bearing_nodes();
    assert!(grammar.len() > 10, "the scan found {grammar:?}");
    let covered: std::collections::BTreeSet<String> =
        templates().iter().map(|t| t.node.to_owned()).collect();
    assert_eq!(
        grammar, covered,
        "the grammar's attribute-bearing nodes are not the templates'"
    );
    let probe = "[<Probe>]";
    for t in &templates() {
        let mut landed = false;
        for (name, text) in &t.files {
            if !text.contains("{A}") {
                continue;
            }
            let src = text.replace("{A}", probe);
            let kind = if name.ends_with(".fsi") {
                FileKind::Sig
            } else {
                FileKind::Impl
            };
            let p = parse_with_options(
                &src,
                ParseOptions {
                    file_kind: kind,
                    symbols: &Default::default(),
                    // The version the oracle checks at.
                    lang: borzoi_cst::language_version::LanguageVersion::V10_0,
                },
            );
            // A feature gate (a tuple head before preview) keeps the whole tree.
            let broken: Vec<_> = p.errors.iter().filter(|e| e.gate.is_none()).collect();
            assert!(broken.is_empty(), "{}: {broken:?}\n{src}", t.label);
            let want = kind_name(t.node);
            landed |= p
                .root
                .descendants()
                .filter(|n| n.kind() == SyntaxKind::ATTRIBUTE_LIST)
                .filter(|n| n.text().to_string().contains("Probe"))
                .any(|n| {
                    n.parent()
                        .is_some_and(|a| format!("{:?}", a.kind()) == want)
                });
        }
        assert!(
            landed,
            "{}: the attribute does not land on a {}",
            t.label, t.node
        );
    }
}
