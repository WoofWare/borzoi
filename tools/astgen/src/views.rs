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

use crate::{CATEGORIES, Enum, Node, find_node, node_kinds, reformat};

/// The repo-relative path of the generated views.
pub const OUTPUT_PATH: &str = "crates/cst/src/syntax/generated/union_views.rs";

/// One node type's view.
pub struct View {
    /// The node type viewed, a [`Node`] of the tables.
    pub node: &'static str,
    /// What reads it through the view, for the doc comment.
    pub reader: &'static str,
    /// `(variant, type)`: the child nodes it may hold, each a node type or a
    /// dispatch enum of the tables (whose every kind the variant takes).
    pub children: &'static [(&'static str, &'static str)],
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
            ("LongIdent", "LongIdent"),
            ("ActivePatName", "ActivePatName"),
            ("TyparDecls", "TyparDecls"),
            ("NamePatPairs", "NamePatPairs"),
            ("Arg", "Pat"),
        ],
        // A zero-width `ERROR` is a layout virtual the lex filter inserted
        // (as before an adjacent argument, `this.M(x)`); one with text is
        // recovery debris.
        tokens: &[("Error", "ERROR")],
    },
    View {
        node: "LongIdent",
        reader: "`borzoi-sema`'s extension-name pass (a member head's name)",
        children: &[("ActivePatName", "ActivePatName")],
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

/// The dispatch enum `name` of the tables and its category's nodes, if it is
/// one.
fn dispatch_enum(name: &str) -> Option<(&'static Enum, &'static [Node])> {
    CATEGORIES.iter().find_map(|c| {
        c.enums
            .iter()
            .find(|e| e.name == name)
            .map(|e| (e, c.nodes))
    })
}

/// The `SyntaxKind`s a child type takes: a node type's own, or every kind of
/// every variant of a dispatch enum. Panics on a name that is neither.
pub fn child_kinds(ty: &str) -> Vec<String> {
    match (dispatch_enum(ty), node(ty)) {
        (Some((e, nodes)), _) => e
            .variants
            .iter()
            .flat_map(|(_, n)| node_kinds(find_node(nodes, n)))
            .collect(),
        (None, Some(n)) => node_kinds(n),
        (None, None) => panic!("`{ty}` is no node type or dispatch enum of the tables"),
    }
}

/// Every child kind `view` declares, nodes then tokens, in table order.
pub fn declared_kinds(view: &View) -> Vec<String> {
    view.children
        .iter()
        .flat_map(|(_, ty)| child_kinds(ty))
        .chain(view.tokens.iter().map(|(_, k)| (*k).to_string()))
        .collect()
}

/// Why `views` is not a table the generator can emit, if it is not: a view of
/// a type the tables do not declare, or of one type twice; a child type that
/// is neither a node type nor a dispatch enum; a child kind two variants
/// claim (the first would take it silently); a variant name used twice.
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
        let unknown: Vec<&str> = view
            .children
            .iter()
            .map(|(_, ty)| *ty)
            .filter(|ty| dispatch_enum(ty).is_none() && node(ty).is_none())
            .collect();
        for ty in &unknown {
            errors.push(format!(
                "`{}`'s view holds `{ty}`, which is no node type or dispatch enum",
                view.node
            ));
        }
        if !unknown.is_empty() {
            continue;
        }
        let mut kinds = BTreeSet::new();
        for kind in declared_kinds(view) {
            if !kinds.insert(kind.clone()) {
                errors.push(format!(
                    "`{}`'s view claims `{kind}` in two variants",
                    view.node
                ));
            }
        }
        let mut names = BTreeSet::new();
        let variants = view.children.iter().map(|(v, _)| *v);
        // A token is the `Token` variant's, beside the child nodes'.
        let token_variant = (!view.tokens.is_empty()).then_some("Token");
        for name in variants.chain(token_variant) {
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
    let mut out = String::from(
        "//! GENERATED by `tools/astgen` — do not edit by hand.\n\
         //! Regenerate with `cargo run -p borzoi-astgen --example generate`; kept honest\n\
         //! by borzoi-astgen's `tests/up_to_date.rs` staleness test.\n\
         //!\n\
         //! The **exhaustive child views** (`tools/astgen/src/views.rs`): for each\n\
         //! node type a walk must read whole, a closed enum of the children it may\n\
         //! hold and a `view()` that yields every non-trivia child as one of them,\n\
         //! or an [`UnexpectedChild`] for any other. Not part of the union's lock or\n\
         //! of any facade.\n\n\
         use super::union_pats::*;\n\
         use super::union_standalone::*;\n\
         use crate::syntax::{AstNode, NodeOrToken, SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken, TextRange};\n\n\
         /// A child a node's view does not declare: a walk reading the view\n\
         /// cannot account for it, so it must decline.\n\
         #[derive(Debug, Clone, PartialEq, Eq, Hash)]\n\
         pub struct UnexpectedChild {\n\
         /// The viewed node's kind.\n\
         pub parent: SyntaxKind,\n\
         /// The child's kind.\n\
         pub kind: SyntaxKind,\n\
         /// Whether the child is a token.\n\
         pub is_token: bool,\n\
         /// The child's range.\n\
         pub range: TextRange,\n\
         }\n\n",
    );
    for view in VIEWS {
        gen_view(view, &mut out);
    }
    gen_reference(&mut out);
    reformat(&out)
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
    for (variant, ty) in view.children {
        out.push_str(&format!("    {variant}({ty}),\n"));
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
        for (variant, ty) in view.children {
            casts.push_str(&format!(
                "if let Some(c) = {ty}::cast(n.clone()) {{ return Ok({child}::{variant}(c)); }}\n"
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
    out.push_str(&format!(
        "impl {child} {{\n\
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

/// The table the `view-reference` check and the view tests read: each viewed
/// node kind, with every child kind its view declares, and the verdict of a
/// node's view by its kind.
fn gen_reference(out: &mut String) {
    let mut table = String::new();
    let mut arms = String::new();
    for view in VIEWS {
        let declared: Vec<String> = declared_kinds(view)
            .iter()
            .map(|k| format!("SyntaxKind::{k}"))
            .collect();
        let viewed = node(view.node).expect("checked");
        for kind in node_kinds(viewed) {
            table.push_str(&format!(
                "(SyntaxKind::{kind}, &[{}]),\n",
                declared.join(", ")
            ));
            arms.push_str(&format!(
                "SyntaxKind::{kind} => Some({}::cast(node.clone())?.view().map(drop)),\n",
                view.node
            ));
        }
    }
    out.push_str(&format!(
        "/// Each viewed node kind, with every child kind its view declares.\n\
         #[cfg_attr(not(any(test, feature = \"view-reference\")), allow(dead_code))]\n\
         pub(crate) const VIEWED: &[(SyntaxKind, &[SyntaxKind])] = &[\n{table}];\n\n\
         /// The verdict of `node`'s view, or `None` for a node no view reads.\n\
         #[cfg_attr(not(any(test, feature = \"view-reference\")), allow(dead_code))]\n\
         pub(crate) fn view_of(node: &SyntaxNode) -> Option<Result<(), UnexpectedChild>> {{\n\
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

    #[test]
    fn a_dispatch_enum_child_takes_every_kind_of_its_variants() {
        let kinds = child_kinds("Pat");
        assert!(kinds.contains(&"NAMED_PAT".to_string()));
        assert!(kinds.contains(&"LONG_IDENT_PAT".to_string()));
        assert_eq!(child_kinds("LongIdent"), ["LONG_IDENT"]);
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
                "no node type or dispatch enum",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &[("X", "NoSuchChild")],
                    tokens: &[],
                },
            ),
            (
                // `LongIdentPat` is one of `Pat`'s kinds.
                "in two variants",
                View {
                    node: "LongIdentPat",
                    reader: "",
                    children: &[("Head", "LongIdentPat"), ("Arg", "Pat")],
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
                    children: &[("A", "LongIdent"), ("A", "ActivePatName")],
                    tokens: &[],
                },
            ),
            (
                "two variants `Token`",
                View {
                    node: "LongIdent",
                    reader: "",
                    children: &[("Token", "ActivePatName")],
                    tokens: &[("Dot", "DOT_TOK")],
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
