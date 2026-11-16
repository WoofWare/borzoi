//! The reference printer.
//!
//! It favours being obviously right over being readable:
//!
//! * Every expression, pattern and type is parenthesised, so precedence,
//!   associativity and what a trailing construct swallows never arise
//!   (`if c then a else b; d`, `a :: b : T`, a `match` inside a `match`).
//! * Every expression is on one line, so the only columns the offside rule sees
//!   are the starts of declaration lines. A construct that pushes an offside
//!   context at its own column (`|`, `when`, `{ f =`, `[`) never has a second
//!   line to be offside on. The exception is `let rec … and …`, whose `and`
//!   F# accepts only at the start of a line in its `let`'s column; the printer
//!   breaks the line there, in an expression too, and nothing pushed earlier on
//!   the line has a later column, so nothing else sees the break.
//! * Expressions use the verbose forms (`let … in`, `do … done`), which need no
//!   layout.
//!
//! The one place layout matters is declarations: each starts its own line, and
//! a nested module's declarations are indented two columns past it.

use crate::names::{Ident, LongIdent, Operator, TyparName, ValueName};
use crate::tree::{
    Access, Attribute, Binding, BindingHead, Const, Expr, ForDirection, ImplFile, LetBindings,
    MatchClause, ModuleDecl, NamespaceName, NestedModule, Pat, Type, TypeDefn, TypeRepr, UnionCase,
};

/// `file` as F# source.
///
/// The output favours being obviously right over being readable. Every
/// expression, pattern and type is parenthesised, every expression sits on one
/// line, and expressions use the verbose forms (`let … in`, `do … done`); the
/// module docs of the printer say why each choice is made.
pub fn print_impl_file(file: &ImplFile) -> String {
    let mut p = Printer { out: String::new() };
    match file {
        ImplFile::AnonModule(decls) => p.decls(decls, 0),
        ImplFile::NamedModule(m) => {
            p.attribute_line(&m.attributes, 0);
            p.out.push_str("module");
            p.access(m.access);
            if m.is_rec {
                p.out.push_str(" rec");
            }
            p.out.push(' ');
            p.long_ident(&m.name);
            p.out.push('\n');
            p.decls(&m.decls, 0);
        }
        ImplFile::Namespaces(namespaces) => {
            for ns in namespaces.as_slice() {
                p.out.push_str("namespace");
                if ns.is_rec {
                    p.out.push_str(" rec");
                }
                p.out.push(' ');
                match &ns.name {
                    NamespaceName::Global => p.out.push_str("global"),
                    NamespaceName::Named(name) => p.long_ident(name),
                }
                p.out.push('\n');
                p.decls(&ns.decls, 0);
            }
        }
    }
    p.out
}

struct Printer {
    out: String,
}

impl Printer {
    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.out.push_str("  ");
        }
    }

    // ---- declarations: one per line, at `depth` ----

    fn decls(&mut self, decls: &[ModuleDecl], depth: usize) {
        for decl in decls {
            self.decl(decl, depth);
        }
    }

    fn decl(&mut self, decl: &ModuleDecl, depth: usize) {
        if let ModuleDecl::NestedModule(m) = decl {
            return self.nested_module(m, depth);
        }
        self.indent(depth);
        match decl {
            ModuleDecl::Let(bindings) => self.let_bindings(bindings),
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
            ModuleDecl::Exception(case) => {
                self.out.push_str("exception ");
                self.union_case(case);
            }
        }
        self.out.push('\n');
    }

    fn nested_module(&mut self, m: &NestedModule, depth: usize) {
        self.attribute_line(&m.attributes, depth);
        self.indent(depth);
        self.out.push_str("module");
        self.access(m.access);
        if m.is_rec {
            self.out.push_str(" rec");
        }
        self.out.push(' ');
        self.ident(&m.name);
        if m.decls.is_empty() {
            self.out.push_str(" = begin end\n");
        } else {
            self.out.push_str(" =\n");
            self.decls(&m.decls, depth + 1);
        }
    }

    /// The column the next character lands in, in UTF-16 code units, which is
    /// how FCS's offside rule counts.
    fn column(&self) -> usize {
        let line_start = self.out.rfind('\n').map_or(0, |i| i + 1);
        self.out[line_start..].encode_utf16().count()
    }

    /// A `let` group. Each `and` starts a line in the `let`'s column: on the
    /// `let`'s own line, the body's offside context is still open, and F#
    /// rejects the `and`.
    fn let_bindings(&mut self, bindings: &LetBindings) {
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
    fn binding(&mut self, b: &Binding) {
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
            BindingHead::Pattern(p) => {
                self.out.push(' ');
                self.pat(p);
            }
        }
        self.out.push_str(" = ");
        self.expr(&b.body);
    }

    fn type_defn(&mut self, d: &TypeDefn) {
        self.attributes(&d.attributes);
        self.access(d.access);
        self.out.push(' ');
        self.ident(&d.name);
        if !d.typars.is_empty() {
            self.out.push('<');
            for (i, t) in d.typars.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                self.typar(t);
            }
            self.out.push('>');
        }
        self.out.push_str(" = ");
        match &d.repr {
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
                    self.union_case(case);
                }
            }
        }
    }

    fn union_case(&mut self, case: &UnionCase) {
        self.ident(&case.name);
        for (i, field) in case.fields.iter().enumerate() {
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
    fn attribute_line(&mut self, attrs: &[Attribute], depth: usize) {
        if attrs.is_empty() {
            return;
        }
        self.indent(depth);
        self.attribute_list(attrs);
        self.out.push('\n');
    }

    /// ` [<A; B(arg)>]`, or nothing.
    fn attributes(&mut self, attrs: &[Attribute]) {
        if attrs.is_empty() {
            return;
        }
        self.out.push(' ');
        self.attribute_list(attrs);
    }

    /// `[<A; B(arg)>]`.
    fn attribute_list(&mut self, attrs: &[Attribute]) {
        self.out.push_str("[<");
        for (i, a) in attrs.iter().enumerate() {
            if i > 0 {
                self.out.push_str("; ");
            }
            self.long_ident(&a.name);
            if a.arg != Expr::Const(Const::Unit) {
                // `expr` parenthesises, so this is `A(arg)`.
                self.expr(&a.arg);
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

    fn expr(&mut self, e: &Expr) {
        self.out.push('(');
        match e {
            Expr::Const(c) => self.constant(c),
            Expr::Null => self.out.push_str("null"),
            Expr::Name(name) => self.long_ident(name),
            Expr::OpValue(op) => self.operator_value(op),
            Expr::App { func, arg } => {
                self.expr(func);
                self.out.push(' ');
                self.expr(arg);
            }
            Expr::Infix { op, lhs, rhs } => {
                self.expr(lhs);
                self.out.push(' ');
                self.out.push_str(op.operator().as_str());
                self.out.push(' ');
                self.expr(rhs);
            }
            Expr::Tuple(items) => self.separated(items.as_slice(), ", ", Self::expr),
            Expr::List(items) => {
                self.out.push('[');
                self.separated(items, "; ", Self::expr);
                self.out.push(']');
            }
            Expr::Array(items) => {
                self.out.push_str("[|");
                self.separated(items, "; ", Self::expr);
                self.out.push_str("|]");
            }
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
                self.let_bindings(bindings);
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
                self.expr(source);
                self.out.push_str(" do ");
                self.expr(body);
                self.out.push_str(" done");
            }
            Expr::Lazy(e) => self.keyword_expr("lazy ", e),
            Expr::Assert(e) => self.keyword_expr("assert ", e),
            Expr::Do(e) => self.keyword_expr("do ", e),
        }
        self.out.push(')');
    }

    fn keyword_expr(&mut self, keyword: &str, e: &Expr) {
        self.out.push_str(keyword);
        self.expr(e);
    }

    fn expr_and_type(&mut self, e: &Expr, op: &str, ty: &Type) {
        self.expr(e);
        self.out.push_str(op);
        self.ty(ty);
    }

    fn clauses(&mut self, clauses: &[MatchClause]) {
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

    fn pat(&mut self, p: &Pat) {
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
                self.pat(alias);
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

/// Worked examples of the printer's spelling choices, one per hazard. The
/// round-trip oracle in `borzoi-cst`'s tests is what checks they are right;
/// these pin what the output looks like.
#[cfg(test)]
mod tests {
    use super::print_impl_file;
    use crate::names::{Ident, LongIdent, Operator, ValueName};
    use crate::tree::{
        Binding, BindingHead, Const, Expr, ImplFile, LetBindings, ModuleDecl, NestedModule, Pat,
    };
    use crate::vec::Vec1;

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
        file(vec![ModuleDecl::Let(LetBindings::NonRec(Box::new(value(
            "x", body,
        ))))])
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
        let decl = ModuleDecl::Let(LetBindings::NonRec(Box::new(binding(
            BindingHead::Pattern(some_x),
            name("y"),
        ))));
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
                bindings: group,
                body: Box::new(name("f")),
            }),
        };
        // `let` is at UTF-16 column 18, though `é` takes two bytes.
        assert_eq!(
            let_x(e),
            "let x = ((``é``) (let rec f = (1)\n                  and g = (2) in (f)))\n"
        );
    }

    #[test]
    fn a_nested_modules_declarations_are_indented() {
        let inner = NestedModule {
            attributes: Vec::new(),
            access: None,
            is_rec: false,
            name: id("N"),
            decls: Vec::new(),
        };
        let outer = NestedModule {
            attributes: Vec::new(),
            access: None,
            is_rec: false,
            name: id("M"),
            decls: vec![
                ModuleDecl::NestedModule(inner),
                ModuleDecl::Expr(Expr::Const(Const::Unit)),
            ],
        };
        assert_eq!(
            file(vec![ModuleDecl::NestedModule(outer)]),
            "module M =\n  module N = begin end\n  (())\n"
        );
    }
}
