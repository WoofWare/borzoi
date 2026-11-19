//! The reference printer.
//!
//! It favours being obviously right over being readable:
//!
//! * Every expression, pattern and type is parenthesised, so precedence,
//!   associativity and what a trailing construct swallows never arise
//!   (`if c then a else b; d`, `a :: b : T`, a `match` inside a `match`).
//!   Computation-expression statements are the exception: F#'s checker refuses
//!   a control construct in parentheses there, so statements are bare and only
//!   their operands are parenthesised. An expression statement is bare too,
//!   unless bare F# would read it otherwise (an `if` as the statement, `a = b`
//!   in a builder's braces as a record's field), which only a list takes in
//!   parentheses ([`crate::tree::needs_parentheses`]).
//! * Every expression is on one line, so the only columns the offside rule sees
//!   are the starts of declaration lines. A construct that pushes an offside
//!   context at its own column (`|`, `when`, `{ f =`, `[`) never has a second
//!   line to be offside on. Two constructs break lines, in an expression too:
//!   `let rec … and …` (and `let! … and! …`), whose `and` F# accepts only at the
//!   start of a line in its `let`'s column; and a computation expression's
//!   body, whose statements F# separates only by layout, one per line in the
//!   column of the first (a list literal's elements included), with each later
//!   part of a statement (`else`, a `|` clause, `with`, `finally`) starting a
//!   line in the statement's column. A break's column is always past every
//!   context pushed earlier on its line, so only the contexts the break is
//!   meant to end see it, and every line of a body starts at the body's
//!   column, so the output grows linearly with the tree.
//! * Expressions use the verbose forms (`let … in`, `do … done`), which need no
//!   layout.
//!
//! Elsewhere layout matters only between declarations: each starts its own
//! line, and a nested module's declarations are indented two columns past it.

use crate::names::{Ident, LongIdent, Operator, TyparName, ValueName};
use crate::tree::{
    Access, Args, AsAlias, Attribute, AttributeArgs, Binding, BindingHead, Comp, CompClause,
    CompItem, Const, Context, Expr, ForDirection, ForSource, ImplFile, LetBindings, ListBody,
    MatchClause, ModuleDecl, NamespaceName, NestedModule, Pat, Range, Stmt, Type, TypeDefn,
    TypeRepr, UnionField, UseName, needs_parentheses,
};
use crate::version::{Gate, Version};

/// `file` as F# source.
///
/// The output favours being obviously right over being readable. Every
/// expression, pattern and type is parenthesised, every expression sits on one
/// line, and expressions use the verbose forms (`let … in`, `do … done`); the
/// module docs of the printer say why each choice is made.
pub fn print_impl_file<V: Version>(file: &ImplFile<V>) -> String {
    print_file(file).out
}

fn print_file<V: Version>(file: &ImplFile<V>) -> Printer {
    let mut p = Printer {
        out: String::new(),
        counted: 0,
        column_at_counted: 0,
        #[cfg(test)]
        scanned: 0,
    };
    match file {
        ImplFile::AnonModule(decls) => p.decls(decls, 0),
        ImplFile::NamedModule(m) => {
            p.attribute_line(&m.attributes, 0);
            p.out.push_str("module");
            p.access(m.access);
            if m.body.is_rec() {
                p.out.push_str(" rec");
            }
            p.out.push(' ');
            p.long_ident(&m.name);
            p.out.push('\n');
            p.decls(m.body.decls(), 0);
        }
        ImplFile::Namespaces(namespaces) => {
            for ns in namespaces.as_slice() {
                p.out.push_str("namespace");
                if ns.body.is_rec() {
                    p.out.push_str(" rec");
                }
                p.out.push(' ');
                match &ns.name {
                    NamespaceName::Global => p.out.push_str("global"),
                    NamespaceName::Named(name) => p.long_ident(name),
                }
                p.out.push('\n');
                p.decls(ns.body.decls(), 0);
            }
        }
    }
    p
}

struct Printer {
    out: String,
    /// How far into `out` [`Printer::column`] has counted, and the column at
    /// that point: each character is counted once, so asking the column at
    /// every statement of a long line stays linear.
    counted: usize,
    column_at_counted: usize,
    /// How many bytes [`Printer::column`] has scanned in all.
    #[cfg(test)]
    scanned: usize,
}

impl Printer {
    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.out.push_str("  ");
        }
    }

    // ---- declarations: one per line, at `depth` ----

    fn decls<V: Version>(&mut self, decls: &[ModuleDecl<V>], depth: usize) {
        for decl in decls {
            self.decl(decl, depth);
        }
    }

    fn decl<V: Version>(&mut self, decl: &ModuleDecl<V>, depth: usize) {
        if let ModuleDecl::NestedModule(m) = decl {
            return self.nested_module(m, depth);
        }
        self.indent(depth);
        match decl {
            ModuleDecl::Let(bindings) => self.let_bindings(bindings.bindings()),
            ModuleDecl::Expr(e) => self.expr(e),
            ModuleDecl::Open(target) => {
                self.out.push_str("open ");
                self.long_ident(target);
            }
            ModuleDecl::NestedModule(_) => unreachable!("printed above"),
            ModuleDecl::ModuleAbbrev { name, target } => {
                self.out.push_str("module ");
                self.ident(name);
                self.out.push_str(" = ");
                self.long_ident(target);
            }
            ModuleDecl::Types(defns) => {
                for (i, defn) in defns.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push('\n');
                        self.indent(depth);
                        self.out.push_str("and");
                    } else {
                        self.out.push_str("type");
                    }
                    self.type_defn(defn);
                }
            }
            ModuleDecl::Exception(exn) => {
                self.out.push_str("exception ");
                self.case(exn.name().ident(), exn.fields());
            }
        }
        self.out.push('\n');
    }

    fn nested_module<V: Version>(&mut self, m: &NestedModule<V>, depth: usize) {
        self.attribute_line(&m.attributes, depth);
        self.indent(depth);
        self.out.push_str("module");
        self.access(m.access);
        if m.body.is_rec() {
            self.out.push_str(" rec");
        }
        self.out.push(' ');
        self.ident(m.name.ident());
        if m.body.decls().is_empty() {
            self.out.push_str(" = begin end\n");
        } else {
            self.out.push_str(" =\n");
            self.decls(m.body.decls(), depth + 1);
        }
    }

    /// The column the next character lands in, in UTF-16 code units, which is
    /// how FCS's offside rule counts.
    fn column(&mut self) -> usize {
        let fresh = &self.out[self.counted..];
        #[cfg(test)]
        {
            self.scanned += fresh.len();
        }
        self.column_at_counted = match fresh.rfind('\n') {
            Some(i) => fresh[i + 1..].encode_utf16().count(),
            None => self.column_at_counted + fresh.encode_utf16().count(),
        };
        self.counted = self.out.len();
        self.column_at_counted
    }

    /// A `let` group. Each `and` starts a line in the `let`'s column: on the
    /// `let`'s own line, the body's offside context is still open, and F#
    /// rejects the `and`.
    fn let_bindings<V: Version>(&mut self, bindings: &LetBindings<V>) {
        match bindings {
            LetBindings::NonRec(b) => {
                self.out.push_str("let");
                self.binding(b);
            }
            LetBindings::Rec(bs) => {
                let column = self.column();
                for (i, b) in bs.as_slice().iter().enumerate() {
                    if i == 0 {
                        self.out.push_str("let rec");
                    } else {
                        self.out.push('\n');
                        self.out.extend(std::iter::repeat_n(' ', column));
                        self.out.push_str("and");
                    }
                    self.binding(b);
                }
            }
        }
    }

    /// A binding after its `let`/`and` keyword: ` [attrs] [inline] head = body`.
    fn binding<V: Version>(&mut self, b: &Binding<V>) {
        self.attributes(&b.attributes);
        if b.is_inline {
            self.out.push_str(" inline");
        }
        match &b.head {
            BindingHead::Name {
                is_mutable,
                access,
                name,
            } => {
                if *is_mutable {
                    self.out.push_str(" mutable");
                }
                self.access(*access);
                self.out.push(' ');
                self.value_name(name);
            }
            BindingHead::Function {
                access,
                name,
                params,
            } => {
                self.access(*access);
                self.out.push(' ');
                self.value_name(name);
                for p in params.as_slice() {
                    self.out.push(' ');
                    self.pat(p);
                }
            }
            // `_` bare, as F# refuses a parenthesised head in a recursive
            // group (FS3521).
            BindingHead::Pattern(Pat::Wildcard) => self.out.push_str(" _"),
            BindingHead::Pattern(p) => {
                self.out.push(' ');
                self.pat(p);
            }
        }
        self.out.push_str(" = ");
        self.expr(&b.body);
    }

    fn type_defn<V: Version>(&mut self, d: &TypeDefn<V>) {
        self.attributes(d.attributes());
        self.access(d.access());
        self.out.push(' ');
        self.ident(d.name().ident());
        if !d.typars().is_empty() {
            self.out.push('<');
            for (i, t) in d.typars().iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                self.typar(t);
            }
            self.out.push('>');
        }
        self.out.push_str(" = ");
        match d.repr() {
            TypeRepr::Abbrev(ty) => self.ty(ty),
            TypeRepr::Record(fields) => {
                self.out.push_str("{ ");
                for (i, f) in fields.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push_str("; ");
                    }
                    if f.is_mutable {
                        self.out.push_str("mutable ");
                    }
                    self.ident(&f.name);
                    self.out.push_str(" : ");
                    self.ty(&f.ty);
                }
                self.out.push_str(" }");
            }
            TypeRepr::Union(cases) => {
                for (i, case) in cases.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push(' ');
                    }
                    self.out.push_str("| ");
                    self.case(case.name().ident(), case.fields());
                }
            }
        }
    }

    /// A union case or an exception, `name of fields`.
    fn case(&mut self, name: &Ident, fields: &[UnionField]) {
        self.ident(name);
        for (i, field) in fields.iter().enumerate() {
            self.out.push_str(if i == 0 { " of " } else { " * " });
            if let Some(name) = &field.name {
                self.ident(name);
                self.out.push_str(" : ");
            }
            self.ty(&field.ty);
        }
    }

    /// A module's attributes, on a line of their own at `depth`, or nothing.
    /// After the `module` keyword, FCS's offside rule misreads a `let` with
    /// attributes inside an attribute's argument.
    fn attribute_line<V: Version>(&mut self, attrs: &[Attribute<V>], depth: usize) {
        if attrs.is_empty() {
            return;
        }
        self.indent(depth);
        self.attribute_list(attrs);
        self.out.push('\n');
    }

    /// ` [<A; B(arg)>]`, or nothing.
    fn attributes<V: Version>(&mut self, attrs: &[Attribute<V>]) {
        if attrs.is_empty() {
            return;
        }
        self.out.push(' ');
        self.attribute_list(attrs);
    }

    /// `[<A; B(arg)>]`.
    fn attribute_list<V: Version>(&mut self, attrs: &[Attribute<V>]) {
        self.out.push_str("[<");
        for (i, a) in attrs.iter().enumerate() {
            if i > 0 {
                self.out.push_str("; ");
            }
            self.long_ident(&a.name);
            match &a.args {
                AttributeArgs::Value(Expr::Const(Const::Unit)) => {}
                // `argument` parenthesises, so this is `A(arg)`.
                AttributeArgs::Value(e) => self.argument(e),
                AttributeArgs::List(args) => self.args(args),
            }
        }
        self.out.push_str(">]");
    }

    /// ` private`, or nothing.
    fn access(&mut self, access: Option<Access>) {
        self.out.push_str(match access {
            None => "",
            Some(Access::Public) => " public",
            Some(Access::Internal) => " internal",
            Some(Access::Private) => " private",
        });
    }

    // ---- expressions: each `(…)`, on one line ----

    fn expr<V: Version>(&mut self, e: &Expr<V>) {
        self.out.push('(');
        self.expr_bare(e);
        self.out.push(')');
    }

    /// `e` without its own parentheses; its operands keep theirs.
    fn expr_bare<V: Version>(&mut self, e: &Expr<V>) {
        match e {
            Expr::Const(c) => self.constant(c),
            Expr::Null => self.out.push_str("null"),
            Expr::Name(name) => self.long_ident(name),
            Expr::OpValue(op) => self.operator_value(op),
            Expr::App { func, arg } => {
                self.head(func);
                self.out.push(' ');
                self.argument(arg);
            }
            Expr::MethodApp { func, args } => {
                self.head(func);
                self.out.push(' ');
                self.args(args);
            }
            Expr::Infix { op, lhs, rhs } => {
                self.expr(lhs);
                self.out.push(' ');
                self.out.push_str(op.operator().as_str());
                self.out.push(' ');
                self.expr(rhs);
            }
            Expr::Tuple(items) => self.separated(items.as_slice(), ", ", Self::expr),
            Expr::List(body) => self.bracketed("[", body.as_deref(), "]"),
            Expr::Array(body) => self.bracketed("[|", body.as_deref(), "|]"),
            Expr::Record { copy, fields } => {
                self.out.push_str("{ ");
                if let Some(copy) = copy {
                    self.expr(copy);
                    self.out.push_str(" with ");
                }
                for (i, (name, value)) in fields.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push_str("; ");
                    }
                    self.long_ident(name);
                    self.out.push_str(" = ");
                    self.expr(value);
                }
                self.out.push_str(" }");
            }
            Expr::FieldGet { expr, field } => {
                self.expr(expr);
                self.out.push('.');
                self.ident(field);
            }
            Expr::Set { target, value } => {
                self.long_ident(target);
                self.out.push_str(" <- ");
                self.expr(value);
            }
            Expr::Lambda { params, body } => {
                self.out.push_str("fun");
                for p in params.as_slice() {
                    self.out.push(' ');
                    self.pat(p);
                }
                self.out.push_str(" -> ");
                self.expr(body);
            }
            Expr::Function(clauses) => {
                self.out.push_str("function");
                self.clauses(clauses.as_slice());
            }
            Expr::Match { scrutinee, clauses } => {
                self.out.push_str("match ");
                self.expr(scrutinee);
                self.out.push_str(" with");
                self.clauses(clauses.as_slice());
            }
            Expr::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.out.push_str("if ");
                self.expr(cond);
                self.out.push_str(" then ");
                self.expr(then_branch);
                if let Some(e) = else_branch {
                    self.out.push_str(" else ");
                    self.expr(e);
                }
            }
            Expr::LetIn { bindings, body } => {
                self.let_bindings(bindings.bindings());
                self.out.push_str(" in ");
                self.expr(body);
            }
            Expr::Sequential(a, b) => {
                self.expr(a);
                self.out.push_str("; ");
                self.expr(b);
            }
            Expr::Typed { expr, ty } => self.expr_and_type(expr, " : ", ty),
            Expr::TypeTest { expr, ty } => self.expr_and_type(expr, " :? ", ty),
            Expr::Upcast { expr, ty } => self.expr_and_type(expr, " :> ", ty),
            Expr::Downcast { expr, ty } => self.expr_and_type(expr, " :?> ", ty),
            Expr::Cons { head, tail } => {
                self.expr(head);
                self.out.push_str(" :: ");
                self.expr(tail);
            }
            Expr::TryWith { body, clauses } => {
                self.out.push_str("try ");
                self.expr(body);
                self.out.push_str(" with");
                self.clauses(clauses.as_slice());
            }
            Expr::TryFinally { body, finally } => {
                self.out.push_str("try ");
                self.expr(body);
                self.out.push_str(" finally ");
                self.expr(finally);
            }
            Expr::While { cond, body } => {
                self.out.push_str("while ");
                self.expr(cond);
                self.out.push_str(" do ");
                self.expr(body);
                self.out.push_str(" done");
            }
            Expr::For {
                var,
                from,
                direction,
                to,
                body,
            } => {
                self.out.push_str("for ");
                self.ident(var);
                self.out.push_str(" = ");
                self.expr(from);
                self.out.push_str(match direction {
                    ForDirection::To => " to ",
                    ForDirection::Downto => " downto ",
                });
                self.expr(to);
                self.out.push_str(" do ");
                self.expr(body);
                self.out.push_str(" done");
            }
            Expr::ForEach { pat, source, body } => {
                self.out.push_str("for ");
                self.pat(pat);
                self.out.push_str(" in ");
                self.for_source(source);
                self.out.push_str(" do ");
                self.expr(body);
                self.out.push_str(" done");
            }
            Expr::Lazy(e) => self.keyword_expr("lazy ", e),
            Expr::Assert(e) => self.keyword_expr("assert ", e),
            Expr::Do(e) => self.keyword_expr("do ", e),
            Expr::DotLambda { gate: _, path } => {
                self.out.push_str("_.");
                self.long_ident(path);
            }
            Expr::Computation { builder, body } => {
                match &**builder {
                    Expr::Name(name) => self.long_ident(name),
                    other => self.expr(other),
                }
                self.out.push_str(" { ");
                self.comp(body);
                self.out.push_str(" }");
            }
        }
    }

    /// What an application applies. A name or member access is bare: in
    /// parentheses, F#'s checker makes a method a function value before
    /// applying it, which loses its named and optional arguments and its
    /// overloads. Each is atomic, so it needs no parentheses to stay the head.
    fn head<V: Version>(&mut self, func: &Expr<V>) {
        match func {
            Expr::Name(name) => self.long_ident(name),
            Expr::FieldGet { expr, field } => {
                self.expr(expr);
                self.out.push('.');
                self.ident(field);
            }
            _ => self.expr(func),
        }
    }

    /// One argument, passed whole. A tuple takes a second pair of parentheses,
    /// or F#'s checker reads its elements as an argument list.
    /// An argument: a tuple in parentheses of its own, and `()` bare, as F#'s
    /// checker reads `M (())` as a method given one argument and `M ()` as
    /// one given none.
    fn argument<V: Version>(&mut self, e: &Expr<V>) {
        if let Expr::Const(Const::Unit) = e {
            self.out.push_str("()");
        } else if let Expr::Tuple(_) = e {
            self.out.push('(');
            self.expr(e);
            self.out.push(')');
        } else {
            self.expr(e);
        }
    }

    /// `(a, b, x = c)`. A named argument's name is bare, so it is not
    /// parenthesised like every other expression; a positional argument is.
    fn args<V: Version>(&mut self, args: &Args<V>) {
        self.out.push('(');
        match args {
            Args::Positional(items) => self.separated(items.as_slice(), ", ", Self::expr),
            Args::Named { positional, named } => {
                for e in positional {
                    self.expr(e);
                    self.out.push_str(", ");
                }
                for (i, (name, value)) in named.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.ident(name);
                    self.out.push_str(" = ");
                    self.expr(value);
                }
            }
        }
        self.out.push(')');
    }

    /// `open body close`, or `open close` (`[]`, `[||]`) with no body.
    fn bracketed<V: Version>(&mut self, open: &str, body: Option<&ListBody<V>>, close: &str) {
        self.out.push_str(open);
        match body {
            None => {}
            Some(ListBody::Elements(items)) => {
                // Elements on one line share it, `; ` apart; one that may
                // break lines starts a line of its own in the first's column,
                // and so does the element after it. So the elements' starts
                // never drift right with each other's widths, and a list's
                // width is never repeated per element.
                let column = self.column();
                let items = items.as_slice();
                let one_line: Vec<bool> = items.iter().map(prints_on_one_line).collect();
                for (i, e) in items.iter().enumerate() {
                    if i > 0 {
                        if one_line[i - 1] && one_line[i] {
                            self.out.push_str("; ");
                        } else {
                            self.newline_at(column);
                        }
                    }
                    self.expr(e);
                }
            }
            Some(ListBody::Range(r)) => self.range(r),
            Some(ListBody::Comp(c)) => self.comp(c.comp()),
        }
        self.out.push_str(close);
    }

    /// A line break, then spaces to `column`.
    fn newline_at(&mut self, column: usize) {
        self.out.push('\n');
        self.out.extend(std::iter::repeat_n(' ', column));
    }

    /// A computation expression's body, its statements one per line in the
    /// column of the first. On one line, `do! a; b` is `do!` of the sequence,
    /// and `if c then a else b; d` puts `d` in the `else`; F# separates
    /// statements by layout, and by nothing else that keeps them statements.
    /// A list literal's elements are statements too, so each has a line.
    fn comp<V: Version, K: Context>(&mut self, c: &Comp<V, K>) {
        let column = self.column();
        for item in &c.init {
            match item {
                CompItem::Stmt(s) => self.stmt(s),
                CompItem::Let(bindings) => self.let_bindings(bindings.bindings()),
                CompItem::Use(u) => self.use_binding("use ", &u.name, &u.value),
                CompItem::UseBang(u) => self.use_binding("use! ", &u.name, &u.value),
                CompItem::LetBang(b) => {
                    self.out.push_str("let! ");
                    self.pat(&b.pat);
                    self.out.push_str(" = ");
                    self.expr(&b.value);
                    // Like `and` after `let rec`, `and!` starts a line in its
                    // `let!`'s column.
                    for and in &b.ands {
                        self.newline_at(column);
                        self.out.push_str("and! ");
                        self.pat(&and.pat);
                        self.out.push_str(" = ");
                        self.expr(&and.value);
                    }
                }
            }
            self.newline_at(column);
        }
        self.stmt(&c.last);
    }

    /// `use x = e` or `use! _ = e`: the name bare, as F# requires.
    fn use_binding<V: Version, G: Gate>(
        &mut self,
        keyword: &str,
        name: &UseName<G>,
        value: &Expr<V>,
    ) {
        self.out.push_str(keyword);
        match name {
            UseName::Named(name) => self.value_name(name),
            UseName::Discard(_) => self.out.push('_'),
        }
        self.out.push_str(" = ");
        self.expr(value);
    }

    /// A statement. A construct of several parts puts each later part
    /// (`else`, each `|` clause, `with`, `finally`) at the start of a line in
    /// the statement's column, so no part can read as the end of the statement
    /// nested in the part before it. `done` is the exception: at the start of a
    /// line in that column F# reads it as the next statement, and as a closing
    /// keyword it ends whatever is open before it on its line.
    fn stmt<V: Version, K: Context>(&mut self, s: &Stmt<V, K>) {
        let column = self.column();
        match s {
            // Bare, or a builder's checker refuses it as ambiguous; one F#
            // would not read bare as an expression statement keeps its
            // parentheses where the context accepts them.
            Stmt::Expr(e) => {
                if needs_parentheses::<V, K>(e.expr()) {
                    self.expr(e.expr());
                } else {
                    self.expr_bare(e.expr());
                }
            }
            Stmt::DoBang { expr, .. } => self.keyword_expr("do! ", expr),
            Stmt::Return { expr, .. } => self.keyword_expr("return ", expr),
            Stmt::ReturnFrom { expr, .. } => self.keyword_expr("return! ", expr),
            Stmt::Yield(e) => self.keyword_expr("yield ", e),
            Stmt::YieldFrom(e) => self.keyword_expr("yield! ", e),
            Stmt::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.out.push_str("if ");
                self.expr(cond);
                self.out.push_str(" then ");
                self.comp(then_branch);
                if let Some(e) = else_branch {
                    self.newline_at(column);
                    let first = match e.init.first() {
                        Some(CompItem::Stmt(s)) => Some(s),
                        Some(_) => None,
                        None => Some(&e.last),
                    };
                    if let Some(Stmt::IfThenElse { .. }) = first {
                        // F# reads `else if` on one line as `elif`, whose
                        // context is the `else`'s column, so the branch's later
                        // statements, in the `if`'s, would be misread.
                        self.out.push_str("else");
                        self.newline_at(column + 2);
                    } else {
                        self.out.push_str("else ");
                    }
                    self.comp(e);
                }
            }
            Stmt::Match { scrutinee, clauses } => {
                self.keyword_expr("match ", scrutinee);
                self.out.push_str(" with");
                self.comp_clauses(clauses.as_slice(), column);
            }
            Stmt::MatchBang {
                scrutinee, clauses, ..
            } => {
                self.keyword_expr("match! ", scrutinee);
                self.out.push_str(" with");
                self.comp_clauses(clauses.as_slice(), column);
            }
            Stmt::While { cond, body } => self.comp_loop("while ", cond, body),
            Stmt::WhileBang { cond, body, .. } => self.comp_loop("while! ", cond, body),
            Stmt::For {
                var,
                from,
                direction,
                to,
                body,
            } => {
                self.out.push_str("for ");
                self.ident(var);
                self.out.push_str(" = ");
                self.expr(from);
                self.out.push_str(match direction {
                    ForDirection::To => " to ",
                    ForDirection::Downto => " downto ",
                });
                self.expr(to);
                self.out.push_str(" do ");
                self.comp(body);
                self.out.push_str(" done");
            }
            Stmt::ForEach { pat, source, body } => {
                self.out.push_str("for ");
                self.pat(pat);
                self.out.push_str(" in ");
                self.for_source(source);
                self.out.push_str(" do ");
                self.comp(body);
                self.out.push_str(" done");
            }
            Stmt::TryWith { body, clauses, .. } => {
                self.out.push_str("try ");
                self.comp(body);
                self.newline_at(column);
                self.out.push_str("with");
                self.comp_clauses(clauses.as_slice(), column);
            }
            Stmt::TryFinally { body, finally } => {
                self.out.push_str("try ");
                self.comp(body);
                self.newline_at(column);
                self.keyword_expr("finally ", finally);
            }
        }
    }

    fn for_source<V: Version>(&mut self, source: &ForSource<V>) {
        match source {
            ForSource::Expr(e) => self.expr(e),
            ForSource::Range(r) => self.range(r),
        }
    }

    /// `(a) .. (b)` or `(a) .. (s) .. (b)`, bare: in parentheses a range is
    /// an expression, which F# has no range as.
    fn range<V: Version>(&mut self, r: &Range<V>) {
        self.expr(&r.from);
        if let Some(step) = &r.step {
            self.out.push_str(" .. ");
            self.expr(step);
        }
        self.out.push_str(" .. ");
        self.expr(&r.to);
    }

    /// `while c do body done`.
    fn comp_loop<V: Version, K: Context>(
        &mut self,
        keyword: &str,
        cond: &Expr<V>,
        body: &Comp<V, K>,
    ) {
        self.keyword_expr(keyword, cond);
        self.out.push_str(" do ");
        self.comp(body);
        self.out.push_str(" done");
    }

    /// Each `| pat [when guard] -> body` on a line of its own in `column`.
    fn comp_clauses<V: Version, K: Context>(
        &mut self,
        clauses: &[CompClause<V, K>],
        column: usize,
    ) {
        for c in clauses {
            self.newline_at(column);
            self.out.push_str("| ");
            self.pat(&c.pat);
            if let Some(guard) = &c.guard {
                self.out.push_str(" when ");
                self.expr(guard);
            }
            self.out.push_str(" -> ");
            self.comp(&c.body);
        }
    }

    fn keyword_expr<V: Version>(&mut self, keyword: &str, e: &Expr<V>) {
        self.out.push_str(keyword);
        self.expr(e);
    }

    fn expr_and_type<V: Version>(&mut self, e: &Expr<V>, op: &str, ty: &Type) {
        self.expr(e);
        self.out.push_str(op);
        self.ty(ty);
    }

    fn clauses<V: Version>(&mut self, clauses: &[MatchClause<V>]) {
        for c in clauses {
            self.out.push_str(" | ");
            self.pat(&c.pat);
            if let Some(guard) = &c.guard {
                self.out.push_str(" when ");
                self.expr(guard);
            }
            self.out.push_str(" -> ");
            self.expr(&c.result);
        }
    }

    // ---- patterns: each `(…)` ----

    fn pat<V: Version>(&mut self, p: &Pat<V>) {
        self.out.push('(');
        match p {
            Pat::Wildcard => self.out.push('_'),
            Pat::Name(name) => self.long_ident(name),
            Pat::Ctor { name, args } => {
                self.long_ident(name);
                for a in args.as_slice() {
                    self.out.push(' ');
                    self.pat(a);
                }
            }
            Pat::Const(c) => self.constant(c),
            Pat::Null => self.out.push_str("null"),
            Pat::Tuple(items) => self.separated(items.as_slice(), ", ", Self::pat),
            Pat::List(items) => {
                self.out.push('[');
                self.separated(items, "; ", Self::pat);
                self.out.push(']');
            }
            Pat::Array(items) => {
                self.out.push_str("[|");
                self.separated(items, "; ", Self::pat);
                self.out.push_str("|]");
            }
            Pat::Cons { head, tail } => {
                self.pat(head);
                self.out.push_str(" :: ");
                self.pat(tail);
            }
            Pat::Typed { pat, ty } => {
                self.pat(pat);
                self.out.push_str(" : ");
                self.ty(ty);
            }
            Pat::As { pat, alias } => {
                self.pat(pat);
                self.out.push_str(" as ");
                match alias {
                    // Bare: before F# 6, FCS's checker refuses `p as (x)`.
                    AsAlias::Var(name) => self.ident(name.ident()),
                    AsAlias::Pat(alias) => self.pat(alias.pat()),
                }
            }
            Pat::Or(a, b) => {
                self.pat(a);
                self.out.push_str(" | ");
                self.pat(b);
            }
            Pat::Ands(items) => self.separated(items.as_slice(), " & ", Self::pat),
            Pat::Record(fields) => {
                self.out.push_str("{ ");
                for (i, (name, pat)) in fields.as_slice().iter().enumerate() {
                    if i > 0 {
                        self.out.push_str("; ");
                    }
                    self.long_ident(name);
                    self.out.push_str(" = ");
                    self.pat(pat);
                }
                self.out.push_str(" }");
            }
            Pat::IsInst(ty) => {
                self.out.push_str(":? ");
                self.ty(ty);
            }
        }
        self.out.push(')');
    }

    // ---- types: each `(…)` ----

    fn ty(&mut self, t: &Type) {
        self.out.push('(');
        match t {
            Type::Name(name) => self.long_ident(name),
            Type::App { head, args } => {
                // The `<` must touch the name, or it is a less-than.
                self.long_ident(head);
                self.out.push('<');
                self.separated(args.as_slice(), ", ", Self::ty);
                self.out.push('>');
            }
            Type::Var(name) => self.typar(name),
            Type::Fun { arg, ret } => {
                self.ty(arg);
                self.out.push_str(" -> ");
                self.ty(ret);
            }
            Type::Tuple(items) => self.separated(items.as_slice(), " * ", Self::ty),
            Type::Array { rank, elem } => {
                self.ty(elem);
                self.out.push('[');
                for _ in 1..rank.get() {
                    self.out.push(',');
                }
                self.out.push(']');
            }
            Type::Anon => self.out.push('_'),
        }
        self.out.push(')');
    }

    fn separated<T>(&mut self, items: &[T], sep: &str, mut each: impl FnMut(&mut Self, &T)) {
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                self.out.push_str(sep);
            }
            each(self, item);
        }
    }

    // ---- leaves ----

    fn ident(&mut self, id: &Ident) {
        if id.is_plain() {
            self.out.push_str(id.as_str());
        } else {
            self.out.push_str("``");
            self.out.push_str(id.as_str());
            self.out.push_str("``");
        }
    }

    fn long_ident(&mut self, name: &LongIdent) {
        for (i, id) in name.segments().iter().enumerate() {
            if i > 0 {
                self.out.push('.');
            }
            self.ident(id);
        }
    }

    fn typar(&mut self, t: &TyparName) {
        self.out.push('\'');
        self.out.push_str(t.as_str());
    }

    /// `( op )`. The spaces keep `( * )` from opening a comment.
    fn operator_value(&mut self, op: &Operator) {
        self.out.push_str("( ");
        self.out.push_str(op.as_str());
        self.out.push_str(" )");
    }

    fn value_name(&mut self, name: &ValueName) {
        match name {
            ValueName::Ident(id) => self.ident(id),
            ValueName::Operator(op) => self.operator_value(op),
        }
    }

    fn constant(&mut self, c: &Const) {
        use std::fmt::Write;
        let out = &mut self.out;
        // Writing to a `String` cannot fail.
        let _ = match c {
            Const::Unit => write!(out, "()"),
            Const::Bool(b) => write!(out, "{b}"),
            Const::SByte(n) => write!(out, "{n}y"),
            Const::Byte(n) => write!(out, "{n}uy"),
            Const::Int16(n) => write!(out, "{n}s"),
            Const::UInt16(n) => write!(out, "{n}us"),
            Const::Int32(n) => write!(out, "{n}"),
            Const::UInt32(n) => write!(out, "{n}u"),
            Const::Int64(n) => write!(out, "{n}L"),
            Const::UInt64(n) => write!(out, "{n}UL"),
            Const::NativeInt(n) => write!(out, "{n}n"),
            Const::UNativeInt(n) => write!(out, "{n}un"),
            Const::Single(f) => {
                let v = f.value();
                if v.is_finite() {
                    // `{:?}` is the shortest text that reads back as `v`, and
                    // always has a `.` or an exponent, so it lexes as a float.
                    write!(out, "{v:?}f")
                } else {
                    write!(out, "0x{:08X}lf", f.0)
                }
            }
            Const::Double(f) => {
                let v = f.value();
                if v.is_finite() {
                    write!(out, "{v:?}")
                } else {
                    write!(out, "0x{:016X}LF", f.0)
                }
            }
            Const::Char(c) => {
                out.push('\'');
                match char::from_u32(u32::from(*c)) {
                    Some('\'') => out.push_str("\\'"),
                    Some('\\') => out.push_str("\\\\"),
                    Some(ch) if (' '..='~').contains(&ch) => out.push(ch),
                    _ => {
                        let _ = write!(out, "\\u{c:04X}");
                    }
                }
                write!(out, "'")
            }
            Const::String(s) => {
                out.push('"');
                for ch in s.chars() {
                    match ch {
                        '"' => out.push_str("\\\""),
                        '\\' => out.push_str("\\\\"),
                        ' '..='~' => out.push(ch),
                        _ if u32::from(ch) <= 0xFFFF => {
                            let _ = write!(out, "\\u{:04X}", u32::from(ch));
                        }
                        _ => {
                            let _ = write!(out, "\\U{:08X}", u32::from(ch));
                        }
                    }
                }
                write!(out, "\"")
            }
        };
    }
}

/// Whether `e` surely prints without a line break. It may answer no for an
/// expression that does, never yes for one that does not; it looks at no more
/// than a fixed number of nodes, so asking it of every element of every list
/// costs time linear in the tree.
fn prints_on_one_line<V: Version>(e: &Expr<V>) -> bool {
    /// How many nodes one question looks at.
    const BUDGET: usize = 64;
    let mut budget = BUDGET;
    one_line(e, &mut budget)
}

fn one_line<V: Version>(e: &Expr<V>, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    let mut all = |es: &mut dyn Iterator<Item = &Expr<V>>| {
        for e in es {
            if !one_line(e, budget) {
                return false;
            }
        }
        true
    };
    match e {
        // A body breaks lines between its statements and within them, and a
        // recursive group before each `and`.
        Expr::Computation { .. } | Expr::List(Some(_)) | Expr::Array(Some(_)) => match e {
            Expr::List(Some(body)) | Expr::Array(Some(body)) => match &**body {
                ListBody::Elements(items) => all(&mut items.as_slice().iter()),
                ListBody::Range(r) => all(&mut [&r.from, &r.to].into_iter().chain(r.step.as_ref())),
                ListBody::Comp(_) => false,
            },
            _ => false,
        },
        Expr::LetIn { bindings, body } => match bindings.bindings() {
            LetBindings::NonRec(b) => all(&mut [&b.body, &**body].into_iter()),
            LetBindings::Rec(_) => false,
        },
        Expr::Const(_)
        | Expr::Null
        | Expr::Name(_)
        | Expr::OpValue(_)
        | Expr::List(None)
        | Expr::Array(None)
        | Expr::DotLambda { .. } => true,
        Expr::App { func, arg } => all(&mut [&**func, &**arg].into_iter()),
        Expr::MethodApp { func, args } => match args {
            Args::Positional(items) => all(&mut std::iter::once(&**func).chain(items.as_slice())),
            Args::Named { positional, named } => all(&mut std::iter::once(&**func)
                .chain(positional)
                .chain(named.as_slice().iter().map(|(_, e)| e))),
        },
        Expr::Infix { lhs, rhs, .. } => all(&mut [&**lhs, &**rhs].into_iter()),
        Expr::Tuple(items) => all(&mut items.as_slice().iter()),
        Expr::Record { copy, fields } => all(&mut copy
            .as_deref()
            .into_iter()
            .chain(fields.as_slice().iter().map(|(_, e)| e))),
        Expr::FieldGet { expr, .. }
        | Expr::Typed { expr, .. }
        | Expr::TypeTest { expr, .. }
        | Expr::Upcast { expr, .. }
        | Expr::Downcast { expr, .. } => one_line(expr, budget),
        Expr::Set { value, .. } => one_line(value, budget),
        Expr::Lambda { body, .. } | Expr::Lazy(body) | Expr::Assert(body) | Expr::Do(body) => {
            one_line(body, budget)
        }
        Expr::Function(clauses) => clauses_one_line(clauses.as_slice(), None, budget),
        Expr::Match { scrutinee, clauses }
        | Expr::TryWith {
            body: scrutinee,
            clauses,
        } => clauses_one_line(clauses.as_slice(), Some(scrutinee), budget),
        Expr::IfThenElse {
            cond,
            then_branch,
            else_branch,
        } => all(&mut [&**cond, &**then_branch]
            .into_iter()
            .chain(else_branch.as_deref())),
        Expr::Sequential(a, b)
        | Expr::Cons { head: a, tail: b }
        | Expr::TryFinally {
            body: a,
            finally: b,
        }
        | Expr::While { cond: a, body: b } => all(&mut [&**a, &**b].into_iter()),
        Expr::For { from, to, body, .. } => all(&mut [&**from, &**to, &**body].into_iter()),
        Expr::ForEach { source, body, .. } => {
            let source: Vec<&Expr<V>> = match &**source {
                ForSource::Expr(e) => vec![e],
                ForSource::Range(r) => [&r.from, &r.to]
                    .into_iter()
                    .chain(r.step.as_ref())
                    .collect(),
            };
            all(&mut source.into_iter().chain(std::iter::once(&**body)))
        }
    }
}

fn clauses_one_line<V: Version>(
    clauses: &[MatchClause<V>],
    scrutinee: Option<&Expr<V>>,
    budget: &mut usize,
) -> bool {
    scrutinee.is_none_or(|e| one_line(e, budget))
        && clauses.iter().all(|c| {
            c.guard.as_ref().is_none_or(|g| one_line(g, budget)) && one_line(&c.result, budget)
        })
}

/// Worked examples of the printer's spelling choices, one per hazard. The
/// round-trip oracle in `borzoi-cst`'s tests is what checks they are right;
/// these pin what the output looks like.
#[cfg(test)]
mod tests {
    use super::print_impl_file;
    use crate::names::{Ident, LongIdent, Operator, ValueName};
    use crate::tree::{Const, InBuilder, InCollection, ListBody};
    type ForSource = crate::tree::ForSource<DefaultVersion>;
    use crate::vec::{Vec1, Vec2};
    use crate::version::{Available, DefaultVersion};

    type Args = crate::tree::Args<DefaultVersion>;
    type Binding = crate::tree::Binding<DefaultVersion>;
    type BindingHead = crate::tree::BindingHead<DefaultVersion>;
    type Pat = crate::tree::Pat<DefaultVersion>;
    type LetBang = crate::tree::LetBang<DefaultVersion, InBuilder>;
    type Comp = crate::tree::Comp<DefaultVersion, InBuilder>;
    type CompItem = crate::tree::CompItem<DefaultVersion, InBuilder>;
    type Stmt = crate::tree::Stmt<DefaultVersion, InBuilder>;
    type CollectionComp = crate::tree::Comp<DefaultVersion, InCollection>;
    type ListItem = crate::tree::CompItem<DefaultVersion, InCollection>;
    type ListStmt = crate::tree::Stmt<DefaultVersion, InCollection>;
    type StmtExpr<K> = crate::tree::StmtExpr<DefaultVersion, K>;
    type Expr = crate::tree::Expr<DefaultVersion>;
    type ImplFile = crate::tree::ImplFile<DefaultVersion>;
    type LetBindings = crate::tree::LetBindings<DefaultVersion>;
    type ModuleDecl = crate::tree::ModuleDecl<DefaultVersion>;
    type NestedModule = crate::tree::NestedModule<DefaultVersion>;
    type ModuleBindings = crate::tree::ModuleBindings<DefaultVersion>;
    type ModuleBody = crate::tree::ModuleBody<DefaultVersion>;
    use crate::names::EntityName;

    fn id(s: &str) -> Ident {
        Ident::new(s).unwrap()
    }

    fn name(s: &str) -> Expr {
        Expr::Name(LongIdent::single(id(s)))
    }

    fn binding(head: BindingHead, body: Expr) -> Binding {
        Binding {
            attributes: Vec::new(),
            is_inline: false,
            head,
            body,
        }
    }

    fn value(n: &str, body: Expr) -> Binding {
        binding(
            BindingHead::Name {
                is_mutable: false,
                access: None,
                name: ValueName::Ident(id(n)),
            },
            body,
        )
    }

    fn file(decls: Vec<ModuleDecl>) -> String {
        print_impl_file(&ImplFile::AnonModule(decls))
    }

    fn let_x(body: Expr) -> String {
        file(vec![ModuleDecl::Let(
            ModuleBindings::new(LetBindings::NonRec(Box::new(value("x", body)))).unwrap(),
        )])
    }

    #[test]
    fn a_keyword_or_non_ascii_name_is_quoted() {
        assert_eq!(let_x(name("type")), "let x = (``type``)\n");
        assert_eq!(let_x(name("é")), "let x = (``é``)\n");
        assert_eq!(let_x(name("x'")), "let x = (x')\n");
    }

    #[test]
    fn a_string_is_one_escaped_line() {
        let s = Expr::Const(Const::String("a\"\\\n\u{e9}\u{1F600}".to_owned()));
        assert_eq!(
            let_x(s),
            "let x = (\"a\\\"\\\\\\u000A\\u00E9\\U0001F600\")\n"
        );
    }

    #[test]
    fn a_field_access_is_parenthesised_so_a_literal_is_not_a_float() {
        let e = Expr::FieldGet {
            expr: Box::new(Expr::FieldGet {
                expr: Box::new(Expr::Const(Const::Int32(1))),
                field: id("A"),
            }),
            field: id("B"),
        };
        assert_eq!(let_x(e), "let x = (((1).A).B)\n");
    }

    #[test]
    fn a_pattern_binding_is_parenthesised_so_it_does_not_define_a_function() {
        let some_x = Pat::Ctor {
            name: LongIdent::single(id("Some")),
            args: Vec1::new(Pat::Name(LongIdent::single(id("x"))), Vec::new()),
        };
        let decl = ModuleDecl::Let(
            ModuleBindings::new(LetBindings::NonRec(Box::new(binding(
                BindingHead::Pattern(some_x),
                name("y"),
            ))))
            .unwrap(),
        );
        assert_eq!(file(vec![decl]), "let (Some (x)) = (y)\n");
    }

    #[test]
    fn multiplication_is_spaced_so_it_does_not_open_a_comment() {
        assert_eq!(
            let_x(Expr::OpValue(Operator::new("*").unwrap())),
            "let x = (( * ))\n"
        );
    }

    #[test]
    fn a_negative_literal_is_one_token() {
        assert_eq!(let_x(Expr::Const(Const::Int32(-1))), "let x = (-1)\n");
    }

    #[test]
    fn each_and_starts_a_line_in_its_lets_column() {
        let group = LetBindings::Rec(Vec1::new(
            value("f", Expr::Const(Const::Int32(1))),
            vec![value("g", Expr::Const(Const::Int32(2)))],
        ));
        let e = Expr::App {
            func: Box::new(name("é")),
            arg: Box::new(Expr::LetIn {
                bindings: crate::tree::LocalBindings::new(group).unwrap(),
                body: Box::new(name("f")),
            }),
        };
        // `let` is at UTF-16 column 16, though `é` takes two bytes.
        assert_eq!(
            let_x(e),
            "let x = (``é`` (let rec f = (1)\n                and g = (2) in (f)))\n"
        );
    }

    #[test]
    fn a_tuple_argument_is_parenthesised_twice_and_an_argument_list_once() {
        let pair = || Expr::Tuple(Vec2::new(name("a"), name("b"), Vec::new()));
        let one_tuple = Expr::App {
            func: Box::new(name("M")),
            arg: Box::new(pair()),
        };
        assert_eq!(let_x(one_tuple), "let x = (M (((a), (b))))\n");
        let two_args = Expr::MethodApp {
            func: Box::new(name("M")),
            args: Args::Positional(Vec2::new(name("a"), name("b"), Vec::new())),
        };
        assert_eq!(let_x(two_args), "let x = (M ((a), (b)))\n");
    }

    #[test]
    fn a_named_arguments_name_is_bare() {
        let e = Expr::MethodApp {
            func: Box::new(name("M")),
            args: Args::Named {
                positional: vec![name("a")],
                named: Vec1::new((id("type"), name("b")), Vec::new()),
            },
        };
        assert_eq!(let_x(e), "let x = (M ((a), ``type`` = (b)))\n");
    }

    fn ret(s: &str) -> Comp {
        Comp::stmt(Stmt::Return {
            gate: Available,
            expr: name(s),
        })
    }

    fn stmt_expr<K: crate::tree::Context>(e: Expr) -> StmtExpr<K> {
        StmtExpr::new(e).expect("an expression statement")
    }

    fn list_comp(c: CollectionComp) -> ListBody<DefaultVersion> {
        ListBody::Comp(crate::tree::ListComp::<DefaultVersion>::new(c).expect("a list body"))
    }

    fn computation(body: Comp) -> Expr {
        Expr::Computation {
            builder: Box::new(name("async")),
            body: Box::new(body),
        }
    }

    #[test]
    fn a_computation_expressions_statements_are_bare_and_one_per_line() {
        let body = Comp {
            init: vec![
                CompItem::LetBang(LetBang {
                    gate: Available,
                    pat: Pat::Name(LongIdent::single(id("x"))),
                    value: name("a"),
                    ands: Vec::new(),
                }),
                CompItem::Stmt(Stmt::DoBang {
                    gate: Available,
                    expr: name("b"),
                }),
                CompItem::Stmt(Stmt::Expr(stmt_expr(Expr::App {
                    func: Box::new(name("f")),
                    arg: Box::new(name("y")),
                }))),
            ],
            last: Stmt::Return {
                gate: Available,
                expr: name("x"),
            },
        };
        assert_eq!(
            let_x(computation(body)),
            "let x = (async { let! (x) = (a)\n                 do! (b)\n                 f (y)\n                 return (x) })\n"
        );
    }

    #[test]
    fn a_statement_shaped_expression_statement_keeps_its_parentheses() {
        let if_expr = Expr::IfThenElse {
            cond: Box::new(name("c")),
            then_branch: Box::new(name("a")),
            else_branch: Some(Box::new(name("b"))),
        };
        // In a builder it would be refused, and bare it would be the `if`
        // statement.
        assert!(StmtExpr::<InBuilder>::new(if_expr.clone()).is_err());
        let comprehension = Expr::List(Some(Box::new(list_comp(CollectionComp {
            init: vec![ListItem::Stmt(ListStmt::Expr(stmt_expr(if_expr)))],
            last: ListStmt::Yield(name("d")),
        }))));
        assert_eq!(
            let_x(comprehension),
            "let x = ([(if (c) then (a) else (b))\n          yield (d)])\n"
        );
    }

    #[test]
    fn a_do_element_is_parenthesised_and_a_do_statement_bare() {
        let do_u = || Expr::Do(Box::new(name("u")));
        // `[()]`: one element.
        let literal = Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
            do_u(),
            Vec::new(),
        )))));
        assert_eq!(let_x(literal), "let x = ([(do (u))])\n");
        // `[]` with an effect: no element.
        assert!(
            crate::tree::ListComp::<DefaultVersion>::new(CollectionComp::stmt(ListStmt::Expr(
                stmt_expr(name("u"))
            )))
            .is_err()
        );
        let comprehension = Expr::List(Some(Box::new(list_comp(CollectionComp::stmt(
            ListStmt::Expr(stmt_expr(do_u())),
        )))));
        assert_eq!(let_x(comprehension), "let x = ([do (u)])\n");
    }

    #[test]
    fn a_statements_later_parts_start_lines_in_its_column() {
        let inner_if = Stmt::IfThenElse {
            cond: name("d"),
            then_branch: Box::new(ret("a")),
            else_branch: None,
        };
        let body = Comp::stmt(Stmt::IfThenElse {
            cond: name("c"),
            then_branch: Box::new(Comp::stmt(inner_if.clone())),
            else_branch: Some(Box::new(Comp {
                init: vec![CompItem::Stmt(inner_if)],
                last: Stmt::Return {
                    gate: Available,
                    expr: name("b"),
                },
            })),
        });
        // The outer `else` is not the inner `if`'s, and the second branch's
        // `if` is not an `elif`.
        assert_eq!(
            let_x(computation(body)),
            "let x = (async { if (c) then if (d) then return (a)\n                 else\n                   if (d) then return (a)\n                   return (b) })\n"
        );
    }

    #[test]
    fn single_line_elements_share_a_line_and_statements_take_one_each() {
        let literal = Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
            name("a"),
            vec![name("b")],
        )))));
        assert_eq!(let_x(literal), "let x = ([(a); (b)])\n");
        let comprehension = Expr::Array(Some(Box::new(list_comp(CollectionComp::stmt(
            ListStmt::ForEach {
                pat: Pat::Name(LongIdent::single(id("y"))),
                source: ForSource::Expr(name("ys")),
                body: Box::new(CollectionComp {
                    init: vec![ListItem::Stmt(ListStmt::Yield(name("y")))],
                    last: ListStmt::Expr(stmt_expr(name("z"))),
                }),
            },
        )))));
        assert_eq!(
            let_x(comprehension),
            "let x = ([|for (y) in (ys) do yield (y)\n                              z done|])\n"
        );
        assert_eq!(let_x(Expr::Array(None)), "let x = ([||])\n");
    }

    /// A list literal of `n` integers.
    fn long_list(n: i32) -> Expr {
        let items = (1..n).map(|i| Expr::Const(Const::Int32(i))).collect();
        Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
            Expr::Const(Const::Int32(0)),
            items,
        )))))
    }

    /// A list literal of `n` two-line computation expressions.
    fn list_of_computations(n: usize) -> Expr {
        let element = || {
            computation(Comp {
                init: vec![CompItem::Stmt(Stmt::DoBang {
                    gate: Available,
                    expr: name("a"),
                })],
                last: Stmt::Return {
                    gate: Available,
                    expr: name("b"),
                },
            })
        };
        let items = (1..n).map(|_| element()).collect();
        Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
            element(),
            items,
        )))))
    }

    #[test]
    fn a_wide_prefix_is_not_repeated_per_element() {
        // `(s, [0; 0; …])`, the prefix and the list growing together.
        let tuple = |n: usize| {
            let prefix = Expr::Const(Const::String("x".repeat(n)));
            let items = (1..n).map(|_| Expr::Const(Const::Int32(0))).collect();
            let list = Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
                Expr::Const(Const::Int32(0)),
                items,
            )))));
            let_x(Expr::Tuple(Vec2::new(prefix, list, Vec::new()))).len()
        };
        let (small, large) = (tuple(100), tuple(1000));
        assert!(
            large <= 11 * small,
            "{small} bytes for 100, {large} for 1000"
        );
    }

    #[test]
    fn a_list_of_multiline_elements_prints_in_linear_space() {
        let small = let_x(list_of_computations(100)).len();
        let large = let_x(list_of_computations(1000)).len();
        assert!(
            large <= 11 * small,
            "{small} bytes for 100, {large} for 1000"
        );
    }

    #[test]
    fn a_long_list_drops_on_a_small_stack() {
        let list = long_list(256_000);
        std::thread::Builder::new()
            .stack_size(2 << 20)
            .spawn(move || drop(list))
            .expect("spawn")
            .join()
            .expect("the drop does not overflow");
    }

    #[test]
    fn the_column_is_counted_once_per_character() {
        // Each computation asks for its column, on one ever longer line.
        let items: Vec<Expr> = (0..20_000).map(|_| computation(ret("a"))).collect();
        let tuple = Expr::Tuple(Vec2::from_vec(items).expect("two or more"));
        let file = ImplFile::AnonModule(vec![ModuleDecl::Expr(tuple)]);
        let p = super::print_file(&file);
        assert!(p.scanned <= p.out.len(), "{} of {}", p.scanned, p.out.len());
    }

    #[test]
    fn an_accessor_shorthand_is_a_bare_path() {
        let e = Expr::DotLambda {
            gate: Available,
            path: LongIdent(Vec1::new(id("A"), vec![id("type")])),
        };
        assert_eq!(let_x(e), "let x = (_.A.``type``)\n");
    }

    #[test]
    fn a_unit_argument_is_bare() {
        let call = Expr::App {
            func: Box::new(name("f")),
            arg: Box::new(Expr::Const(Const::Unit)),
        };
        assert_eq!(let_x(call), "let x = (f ())\n");
    }

    #[test]
    fn a_nested_modules_declarations_are_indented() {
        let inner = NestedModule {
            attributes: Vec::new(),
            access: None,
            name: EntityName::new(id("N")).unwrap(),
            body: ModuleBody::NonRec(Vec::new()),
        };
        let outer = NestedModule {
            attributes: Vec::new(),
            access: None,
            name: EntityName::new(id("M")).unwrap(),
            body: ModuleBody::NonRec(vec![
                ModuleDecl::NestedModule(inner),
                ModuleDecl::Expr(Expr::Const(Const::Unit)),
            ]),
        };
        assert_eq!(
            file(vec![ModuleDecl::NestedModule(outer)]),
            "module M =\n  module N = begin end\n  (())\n"
        );
    }
}
