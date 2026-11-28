//! **Exhaustive child views** (#1161): for each node type in [`VIEWS`], a
//! closed enum of the children it may hold and a `view()` method that yields
//! every non-trivia child as one of its variants, or an `UnexpectedChild` for
//! a child the table does not declare.
//!
//! A typed accessor filters a node's children by kind and skips the rest
//! silently, so a walk that must decline on a child it does not account for
//! cannot read through accessors alone. It reads through a view instead and
//! matches the variants exhaustively: declaring a new child kind here adds a
//! variant, which is a compile error in every such walk until it handles the
//! kind. A child the table does not declare is an `Err`, which the walk
//! declines on, so a table that lags the parser loses coverage and never
//! soundness; `borzoi-cst`'s `view-reference` test feature holds the table to
//! every parse its suite makes that recovered from nothing.
//!
//! The views are tools for the workspace's own walks, not part of any
//! published surface: they go to their own generated file, outside the
//! union's lock and every facade.
//!
//! A node type is listed only when a walk reads it through its view.

use std::collections::BTreeSet;

use crate::{CATEGORIES, Node, node_kinds, reformat};

/// The repo-relative path of the generated views.
pub const OUTPUT_PATH: &str = "crates/cst/src/syntax/generated/union_views.rs";

/// One node type's view.
pub struct View {
    /// The node type viewed, a [`Node`] of the tables.
    pub node: &'static str,
    /// What reads it through the view, for the doc comment.
    pub reader: &'static str,
    /// The child nodes it may hold, each a node type of the tables that casts
    /// from exactly one `SyntaxKind`, and each a variant of its own name. A
    /// dispatch enum (`Pat`) or a multi-kind node is not one: a kind it came
    /// to take would join the view with no table row, and so no variant, for
    /// a reader to decide.
    pub children: &'static [&'static str],
    /// `(variant, kind)`: the child tokens it may hold, by `SyntaxKind` name.
    /// Trivia is never a child of a view; a zero-width token is a child like
    /// any other.
    pub tokens: &'static [(&'static str, &'static str)],
}

/// Every view, in the order of the generated file.
pub const VIEWS: &[View] = &[
    View {
        node: "LongIdentPat",
        reader: "`borzoi-sema`'s extension-name pass (a member head's name)",
        children: &[
            "LongIdent",
            "ActivePatName",
            "TyparDecls",
            "NamePatPairs",
            // The argument patterns the parser puts under a long-identifier
            // pattern (`view-reference` holds the list to every parse).
            "NamedPat",
            "LongIdentPat",
            "WildcardPat",
            "ParenPat",
            "ConstPat",
            "NullPat",
            "TuplePat",
            "ArrayOrListPat",
            "RecordPat",
            "QuotePat",
            "OptionalValPat",
        ],
        // A zero-width `ERROR` is a layout virtual the lex filter inserted
        // (as before an adjacent argument, `this.M(x)`); one with text is
        // recovery debris.
        tokens: &[("Error", "ERROR")],
    },
    View {
        node: "LongIdent",
        reader: "`borzoi-sema`'s extension-name pass (a member head's name)",
        children: &["ActivePatName"],
        tokens: &[
            ("Ident", "IDENT_TOK"),
            ("Dot", "DOT_TOK"),
            ("New", "NEW_TOK"),
            ("LParen", "LPAREN_TOK"),
            ("RParen", "RPAREN_TOK"),
        ],
    },
];

/// The node type `name` of the tables, if it is one.
fn node(name: &str) -> Option<&'static Node> {
    CATEGORIES
        .iter()
        .find_map(|c| c.nodes.iter().find(|n| n.name == name))
}

/// Whether `name` is a dispatch enum of the tables.
fn is_dispatch_enum(name: &str) -> bool {
    CATEGORIES
        .iter()
        .any(|c| c.enums.iter().any(|e| e.name == name))
}

/// Every child `view` declares, nodes then tokens, in table order: its kind,
/// whether it is a token (a node and a token may share a kind, as an `ERROR`
/// does), and the tag of the variant that holds it ([`tag`]). Panics on a
/// child type [`check`] rejects.
pub fn declared_children(view: &View) -> Vec<(String, bool, String)> {
    view.children
        .iter()
        .map(|ty| {
            let [kind] = node_kinds(node(ty).expect("a node type"))
                .try_into()
                .unwrap_or_else(|kinds: Vec<String>| {
                    panic!("`{ty}` casts from {kinds:?}, not one kind")
                });
            (kind, false, tag(ty, None))
        })
        .chain(
            view.tokens
                .iter()
                .map(|(variant, k)| ((*k).to_string(), true, tag("Token", Some(variant)))),
        )
        .collect()
}

/// How the reference table and a child's `tag()` spell a variant: a node
/// variant's name, or `Token(<token variant>)`.
fn tag(variant: &str, token: Option<&str>) -> String {
    match token {
        Some(token) => format!("{variant}({token})"),
        None => variant.to_string(),
    }
}

/// Why `views` is not a table the generator can emit, if it is not: a view of
/// a type the tables do not declare, or of one type twice; a child that is
/// not a single-kind node type; a child kind two variants claim (the first
/// would take it silently); a variant name used twice.
pub fn check(views: &[View]) -> Result<(), Vec<String>> {
    let mut errors = Vec::new();
    let mut seen = BTreeSet::new();
    for view in views {
        if !seen.insert(view.node) {
            errors.push(format!("`{}` has two views", view.node));
        }
        if node(view.node).is_none() {
            errors.push(format!("`{}` is no node type of the tables", view.node));
            continue;
        }
        let before = errors.len();
        for ty in view.children {
            match node(ty) {
                Some(n) if node_kinds(n).len() == 1 => {}
                Some(n) => errors.push(format!(
                    "`{}`'s view holds `{ty}`, which casts from {:?}: a multi-kind node, \
                     whose every kind needs a row of its own",
                    view.node,
                    node_kinds(n)
                )),
                None if is_dispatch_enum(ty) => errors.push(format!(
                    "`{}`'s view holds `{ty}`, a dispatch enum: list its node types, each a \
                     row of its own",
                    view.node
                )),
                None => errors.push(format!(
                    "`{}`'s view holds `{ty}`, which is no node type",
                    view.node
                )),
            }
        }
        if errors.len() > before {
            continue;
        }
        let mut kinds = BTreeSet::new();
        for (kind, is_token, _) in declared_children(view) {
            if !kinds.insert((kind.clone(), is_token)) {
                errors.push(format!(
                    "`{}`'s view claims `{kind}` in two variants",
                    view.node
                ));
            }
        }
        let mut names = BTreeSet::new();
        // A token is the `Token` variant's, beside the child nodes'.
        let token_variant = (!view.tokens.is_empty()).then_some("Token");
        for name in view.children.iter().copied().chain(token_variant) {
            if !names.insert(name) {
                errors.push(format!(
                    "`{}`'s view names two variants `{name}`",
                    view.node
                ));
            }
        }
        let mut token_names = BTreeSet::new();
        for (name, _) in view.tokens {
            if !token_names.insert(*name) {
                errors.push(format!(
                    "`{}`'s view names two token variants `{name}`",
                    view.node
                ));
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Generate the views file from [`VIEWS`], `rustfmt`-stable. Panics on a
/// table [`check`] rejects.
pub fn generate() -> String {
    if let Err(errors) = check(VIEWS) {
        panic!("the view table is incoherent:\n  {}", errors.join("\n  "));
    }
    let mut out = format!(
        "//! GENERATED by `tools/astgen` — do not edit by hand.\n\
         //! Regenerate with `cargo run -p borzoi-astgen --example generate`; kept honest\n\
         //! by borzoi-astgen's `tests/up_to_date.rs` staleness test.\n\
         //!\n\
         //! The **exhaustive child views** (`tools/astgen/src/views.rs`): for each\n\
         //! node type a walk must read whole, a closed enum of the children it may\n\
         //! hold and a `view()` that yields every non-trivia child as one of them,\n\
         //! or an [`UnexpectedChild`] for any other. Not part of the union's lock or\n\
         //! of any facade.\n\n\
         {imports}\
         use crate::syntax::{{AstNode, NodeOrToken, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, TextRange}};\n\n\
         /// A child a node's view does not declare: a walk reading the view\n\
         /// cannot account for it, so it must decline.\n\
         #[derive(Debug, Clone, PartialEq, Eq, Hash)]\n\
         pub struct UnexpectedChild {{\n\
         /// The viewed node's kind.\n\
         pub parent: SyntaxKind,\n\
         /// The child's kind.\n\
         pub kind: SyntaxKind,\n\
         /// Whether the child is a token.\n\
         pub is_token: bool,\n\
         /// The child's range.\n\
         pub range: TextRange,\n\
         }}\n\n",
        imports = imports(VIEWS),
    );
    for view in VIEWS {
        gen_view(view, &mut out);
    }
    gen_reference(&mut out);
    reformat(&out)
}

/// The category module (`union_pats`, …) declaring the node type `name`.
fn module_of(name: &str) -> &'static str {
    let category = CATEGORIES
        .iter()
        .find(|c| c.nodes.iter().any(|n| n.name == name))
        .unwrap_or_else(|| panic!("`{name}` is in no category"));
    let file = category.path.rsplit('/').next().expect("a path");
    file.strip_suffix(".rs").expect("a Rust file")
}

/// The `use` lines naming every node type `views` names,
/// each from its own category's module.
fn imports(views: &[View]) -> String {
    let mut by_module: std::collections::BTreeMap<&str, BTreeSet<&str>> = Default::default();
    for view in views {
        for name in std::iter::once(view.node).chain(view.children.iter().copied()) {
            by_module.entry(module_of(name)).or_default().insert(name);
        }
    }
    by_module
        .into_iter()
        .map(|(module, names)| {
            let names: Vec<&str> = names.into_iter().collect();
            format!("use super::{module}::{{{}}};\n", names.join(", "))
        })
        .collect()
}

/// The name of `view`'s token enum.
fn token_enum(view: &View) -> String {
    format!("{}Token", view.node)
}

fn gen_view(view: &View, out: &mut String) {
    let node = view.node;
    let child = format!("{node}Child");
    let tokens = token_enum(view);
    let has_tokens = !view.tokens.is_empty();
    out.push_str(&format!(
        "/// A child of a [`{node}`], read through [`{node}::view`] by {reader}.\n\
         #[derive(Debug, Clone, PartialEq, Eq, Hash)]\n\
         pub enum {child} {{\n",
        reader = view.reader
    ));
    for ty in view.children {
        out.push_str(&format!("    {ty}({ty}),\n"));
    }
    if has_tokens {
        out.push_str(&format!("    Token({tokens}, SyntaxToken),\n"));
    }
    out.push_str("}\n\n");
    if has_tokens {
        out.push_str(&format!(
            "/// The kind of a token child of a [`{node}`].\n\
             #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]\n\
             pub enum {tokens} {{\n"
        ));
        for (variant, kind) in view.tokens {
            out.push_str(&format!(
                "    /// [`SyntaxKind::{kind}`].\n    {variant},\n"
            ));
        }
        out.push_str("}\n\n");
    }
    let node_arm = if view.children.is_empty() {
        "NodeOrToken::Node(_) => Err(unexpected),\n".to_string()
    } else {
        let mut casts = String::new();
        for ty in view.children {
            casts.push_str(&format!(
                "if let Some(c) = {ty}::cast(n.clone()) {{ return Ok({child}::{ty}(c)); }}\n"
            ));
        }
        format!("NodeOrToken::Node(n) => {{\n{casts}Err(unexpected)\n}}\n")
    };
    let token_arm = if has_tokens {
        let mut arms = String::new();
        for (variant, kind) in view.tokens {
            arms.push_str(&format!(
                "SyntaxKind::{kind} => Ok({child}::Token({tokens}::{variant}, t)),\n"
            ));
        }
        format!("NodeOrToken::Token(t) => match t.kind() {{\n{arms}_ => Err(unexpected),\n}},\n")
    } else {
        "NodeOrToken::Token(_) => Err(unexpected),\n".to_string()
    };
    let mut element_arms = String::new();
    let mut tag_arms = String::new();
    for ty in view.children {
        element_arms.push_str(&format!(
            "{child}::{ty}(c) => NodeOrToken::Node(c.syntax().clone()),\n"
        ));
        tag_arms.push_str(&format!("{child}::{ty}(_) => \"{}\",\n", tag(ty, None)));
    }
    if has_tokens {
        element_arms.push_str(&format!(
            "{child}::Token(_, t) => NodeOrToken::Token(t.clone()),\n"
        ));
        for (variant, _) in view.tokens {
            tag_arms.push_str(&format!(
                "{child}::Token({tokens}::{variant}, _) => \"{}\",\n",
                tag("Token", Some(variant))
            ));
        }
    }
    out.push_str(&format!(
        "impl {child} {{\n\
         /// The child itself, as the tree holds it.\n\
         pub fn element(&self) -> SyntaxElement {{\n\
         match self {{\n{element_arms}}}\n\
         }}\n\n\
         /// The variant holding the child: its name, or `Token(<token variant>)`.\n\
         pub fn tag(&self) -> &'static str {{\n\
         match self {{\n{tag_arms}}}\n\
         }}\n\n\
         /// Classify one non-trivia child of a `{node}` whose kind is `parent`.\n\
         fn classify(parent: SyntaxKind, el: SyntaxElement) -> Result<Self, UnexpectedChild> {{\n\
         let unexpected = UnexpectedChild {{\n\
         parent,\n\
         kind: el.kind(),\n\
         is_token: matches!(el, NodeOrToken::Token(_)),\n\
         range: el.text_range(),\n\
         }};\n\
         match el {{\n{node_arm}{token_arm}}}\n\
         }}\n\
         }}\n\n\
         impl {node} {{\n\
         /// Every child but trivia, in order, each classified; or the first\n\
         /// child the view does not declare. A walk that must decline on a\n\
         /// child it does not account for reads the node through this, never\n\
         /// through the filtering accessors alone. (Not\n\
         /// [`Parse::view`](crate::parser::Parse::view), which reads a parse\n\
         /// through a facade.)\n\
         pub fn view(&self) -> Result<Vec<{child}>, UnexpectedChild> {{\n\
         let parent = self.0.kind();\n\
         self.0\n\
         .children_with_tokens()\n\
         .filter(|el| !el.kind().is_trivia())\n\
         .map(|el| {child}::classify(parent, el))\n\
         .collect()\n\
         }}\n\
         }}\n\n",
    ));
}

/// The table the `view-reference` check reads: each viewed node kind, with
/// every child its view declares (kind, whether a token, variant tag); and
/// what a node's view yields, by its kind.
fn gen_reference(out: &mut String) {
    let mut table = String::new();
    let mut arms = String::new();
    for view in VIEWS {
        let declared: Vec<String> = declared_children(view)
            .iter()
            .map(|(k, is_token, tag)| format!("(SyntaxKind::{k}, {is_token}, \"{tag}\")"))
            .collect();
        let viewed = node(view.node).expect("checked");
        for kind in node_kinds(viewed) {
            table.push_str(&format!(
                "(SyntaxKind::{kind}, &[{}]),\n",
                declared.join(", ")
            ));
            arms.push_str(&format!(
                "SyntaxKind::{kind} => Some({node}::cast(node.clone()).expect(\"a `{node}` casts from `{kind}`\").view().map(|children| children.iter().map(|c| (c.element(), c.tag())).collect())),\n",
                node = view.node
            ));
        }
    }
    out.push_str(&format!(
        "/// Each viewed node kind, with every child its view declares: its kind,\n\
         /// whether it is a token, and the tag of the variant holding it.\n\
         #[cfg_attr(not(any(test, feature = \"view-reference\")), allow(dead_code))]\n\
         pub(crate) const VIEWED: &[(SyntaxKind, &[(SyntaxKind, bool, &str)])] = &[\n{table}];\n\n\
         /// What `node`'s view yields, each child as the tree holds it with the tag\n\
         /// of the variant holding it, or `None` for a node no view reads.\n\
         #[cfg_attr(not(any(test, feature = \"view-reference\")), allow(dead_code))]\n\
         #[allow(clippy::type_complexity)]\n\
         pub(crate) fn view_of(node: &SyntaxNode) -> Option<Result<Vec<(SyntaxElement, &'static str)>, UnexpectedChild>> {{\n\
         match node.kind() {{\n{arms}_ => None,\n}}\n\
         }}\n"
    ));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_view_table_is_coherent() {
        check(VIEWS).unwrap_or_else(|e| panic!("{}", e.join("\n")));
    }

    /// The generated file imports each type a view names from its own
    /// category's module, whichever category that is.
    #[test]
    fn imports_follow_the_table() {
        let view = View {
            node: "IdentExpr",
            reader: "",
            children: &["NamedPat", "LongIdentType", "LongIdent"],
            tokens: &[],
        };
        assert_eq!(
            imports(std::slice::from_ref(&view)),
            "use super::union_exprs::{IdentExpr};\n\
             use super::union_pats::{NamedPat};\n\
             use super::union_standalone::{LongIdent};\n\
             use super::union_types::{LongIdentType};\n"
        );
    }

    /// Each incoherence [`check`] names is one it rejects.
    #[test]
    fn check_rejects_each_incoherence() {
        let cases: &[(&str, View)] = &[
            (
                "no node type",
                View {
                    node: "NoSuchNode",
                    reader: "",
                    children: &[],
                    tokens: &[],
                },
            ),
            (
                "which is no node type",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &["NoSuchChild"],
                    tokens: &[],
                },
            ),
            (
                "a dispatch enum",
                View {
                    node: "LongIdentPat",
                    reader: "",
                    children: &["Pat"],
                    tokens: &[],
                },
            ),
            (
                // `AppExpr` casts from `APP_EXPR` and `INFIX_APP_EXPR`.
                "a multi-kind node",
                View {
                    node: "ParenExpr",
                    reader: "",
                    children: &["AppExpr"],
                    tokens: &[],
                },
            ),
            (
                "in two variants",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &[],
                    tokens: &[("Dot", "DOT_TOK"), ("Again", "DOT_TOK")],
                },
            ),
            (
                "two variants",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &["ActivePatName", "ActivePatName"],
                    tokens: &[],
                },
            ),
            (
                "two token variants",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &[],
                    tokens: &[("Dot", "DOT_TOK"), ("Dot", "IDENT_TOK")],
                },
            ),
        ];
        for (expected, view) in cases {
            let errors = check(std::slice::from_ref(view)).expect_err(expected);
            assert!(
                errors.iter().any(|e| e.contains(expected)),
                "expected an error naming {expected:?}, got {errors:?}"
            );
        }
        let twice = [
            View {
                node: "LongIdent",
                reader: "",
                children: &[],
                tokens: &[],
            },
            View {
                node: "LongIdent",
                reader: "",
                children: &[],
                tokens: &[],
            },
        ];
        let errors = check(&twice).expect_err("two views");
        assert!(errors.iter().any(|e| e.contains("two views")), "{errors:?}");
    }
}
