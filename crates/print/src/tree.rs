//! The owned syntax tree a program builds and [`crate::print_impl_file`]
//! writes.
//!
//! It models what source *means* to F#'s parser, not how it was laid out:
//! there are no parentheses, no comments and no layout, and two spellings with
//! one parse share one value. Where F#'s grammar has a constraint the parser
//! enforces, the types enforce it too, so every value prints as source F#
//! parses back to that value.
//!
//! The types that can hold a version-gated construct take the F# version the
//! tree targets as a parameter ([`crate::version`]), so a tree holds only what
//! its version has.

use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

use crate::names::{
    CaseName, EntityName, Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName, VarName,
};
use crate::vec::{Vec1, Vec2};
use crate::version::{Available, Gate, Unavailable, Version};

/// An implementation file (`.fs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplFile<V: Version> {
    /// A file with no `module` or `namespace` header.
    AnonModule(Vec<ModuleDecl<V>>),
    /// `module A.B` followed by its declarations.
    NamedModule(NamedModule<V>),
    /// One or more `namespace` sections.
    Namespaces(Vec1<Namespace<V>>),
}

/// A file-level `module A.B`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedModule<V: Version> {
    pub attributes: Vec<Attribute<V>>,
    pub access: Option<Access>,
    pub name: LongIdent,
    pub body: ModuleBody<V>,
}

/// A `namespace` section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Namespace<V: Version> {
    pub name: NamespaceName,
    pub body: ModuleBody<V>,
}

/// What a `namespace` section names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NamespaceName {
    /// `namespace global`
    Global,
    /// `namespace A.B`
    Named(LongIdent),
}

/// An accessibility modifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Access {
    Public,
    Internal,
    Private,
}

/// An attribute, `[<Name(args)>]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute<V: Version> {
    pub name: LongIdent,
    pub args: AttributeArgs<V>,
}

/// What an attribute is applied to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributeArgs<V: Version> {
    /// `[<A(e)>]`: one argument, passed whole, so a tuple is one argument.
    /// [`Const::Unit`] is an attribute written without one, which is how F#
    /// reads `[<A>]` and `[<A()>]` alike.
    Value(Expr<V>),
    /// `[<A(a, b, X = c)>]`: an argument list.
    List(Args<V>),
}

/// A parenthesised argument list, `(a, b, x = c)`, as F#'s checker reads one:
/// each comma-separated element is an argument, and an element `x = c` whose
/// left side is a bare name is the argument named `x`. One positional argument
/// is no list (it is [`Expr::App`]'s argument), and F# requires the named
/// arguments to come last, so the two cases are a list of at least two
/// positional arguments, and positional arguments followed by named ones.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Args<V: Version> {
    /// `(a, b, …)`
    Positional(Vec2<Expr<V>>),
    /// `(a, …, x = c, …)`
    Named {
        positional: Vec<Expr<V>>,
        named: Vec1<(Ident, Expr<V>)>,
    },
}

/// A declaration in a module or namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleDecl<V: Version> {
    /// `let …` or `let rec … and …`.
    Let(ModuleBindings<V>),
    /// An expression evaluated for its effect.
    Expr(Expr<V>),
    /// `open A.B`
    Open(LongIdent),
    /// `module M = …`
    NestedModule(NestedModule<V>),
    /// `module M = A.B`
    ModuleAbbrev { name: Ident, target: LongIdent },
    /// `type A = … and B = …`
    Types(Vec1<TypeDefn<V>>),
    /// `exception E of …`
    Exception(ExceptionDefn),
}

/// A nested `module M =` and its declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedModule<V: Version> {
    pub attributes: Vec<Attribute<V>>,
    pub access: Option<Access>,
    pub name: EntityName,
    pub body: ModuleBody<V>,
}

/// A module's or namespace's declarations, and whether they are one
/// recursive group (`module rec`, `namespace rec`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleBody<V: Version> {
    NonRec(Vec<ModuleDecl<V>>),
    Rec(RecDecls<V>),
}

impl<V: Version> ModuleBody<V> {
    pub fn is_rec(&self) -> bool {
        matches!(self, ModuleBody::Rec(_))
    }

    pub fn decls(&self) -> &[ModuleDecl<V>] {
        match self {
            ModuleBody::NonRec(decls) => decls,
            ModuleBody::Rec(group) => group.decls(),
        }
    }
}

/// The declarations of a recursive module or namespace. Every module of a
/// recursive group, its nested modules' included, must open first (FS3200),
/// then abbreviate modules (FS3201), then declare the rest; and each of its
/// `let`s is recursive, so none may bind a mutable (FS0874) or a pattern
/// other than `_` (FS3521). [`RecDecls::new`] refuses declarations that break
/// a rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecDecls<V: Version>(Vec<ModuleDecl<V>>);

impl<V: Version> RecDecls<V> {
    /// `decls` as a recursive group, or `decls` back if F# refuses them as
    /// one.
    pub fn new(decls: Vec<ModuleDecl<V>>) -> Result<Self, Vec<ModuleDecl<V>>> {
        if rec_group_admits(&decls) {
            Ok(RecDecls(decls))
        } else {
            Err(decls)
        }
    }

    pub fn decls(&self) -> &[ModuleDecl<V>] {
        &self.0
    }

    pub fn into_decls(self) -> Vec<ModuleDecl<V>> {
        self.0
    }
}

/// Whether one module's `decls`, and every module nested in it, keep a
/// recursive group's rules.
fn rec_group_admits<V: Version>(decls: &[ModuleDecl<V>]) -> bool {
    // 0: opens, 1: module abbreviations, 2: the rest.
    let rank = |d: &ModuleDecl<V>| match d {
        ModuleDecl::Open(_) => 0,
        ModuleDecl::ModuleAbbrev { .. } => 1,
        _ => 2,
    };
    let ordered = decls.windows(2).all(|w| rank(&w[0]) <= rank(&w[1]));
    ordered
        && decls.iter().all(|d| match d {
            ModuleDecl::Let(group) => group.bindings().as_slice().iter().all(|b| match &b.head {
                BindingHead::Name { is_mutable, .. } => !is_mutable,
                BindingHead::Function { .. } => true,
                BindingHead::Pattern(p) => matches!(p, Pat::Wildcard),
            }),
            ModuleDecl::NestedModule(m) => match &m.body {
                ModuleBody::NonRec(inner) => rec_group_admits(inner),
                ModuleBody::Rec(_) => true,
            },
            _ => true,
        })
}

/// One `let` group. A non-recursive group has one binding: F# rejects
/// `let a = 1 and b = 2` at module level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetBindings<V: Version> {
    /// `let …`
    NonRec(Box<Binding<V>>),
    /// `let rec … and …`
    Rec(Vec1<Binding<V>>),
}

impl<V: Version> LetBindings<V> {
    pub fn as_slice(&self) -> &[Binding<V>] {
        match self {
            LetBindings::NonRec(b) => std::slice::from_ref(b),
            LetBindings::Rec(bs) => bs.as_slice(),
        }
    }

    /// Whether F# admits the group wherever a `let` group goes: an inline
    /// binding must be a function (FS0832, and FS0829 for a mutable one),
    /// and a recursive group must bind neither a mutable (FS0874) nor a
    /// pattern other than `_`, which is printed parenthesised (FS3521).
    fn admitted_anywhere(&self) -> bool {
        let is_rec = matches!(self, LetBindings::Rec(_));
        self.as_slice().iter().all(|b| match &b.head {
            BindingHead::Name { is_mutable, .. } => !b.is_inline && !(*is_mutable && is_rec),
            BindingHead::Function { .. } => true,
            BindingHead::Pattern(p) => !b.is_inline && !(is_rec && !matches!(p, Pat::Wildcard)),
        })
    }
}

/// A `let` group in a module. F# refuses an inline binding that is not a
/// function (FS0832, and FS0829 for a mutable one), and a recursive group
/// binding a mutable (FS0874) or a pattern (FS3521), so
/// [`ModuleBindings::new`] refuses a group with any of them. A recursive
/// module refuses a mutable binding too, which [`RecDecls`] holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleBindings<V: Version>(LetBindings<V>);

impl<V: Version> ModuleBindings<V> {
    /// `bindings` as a module's group, or `bindings` back if F# refuses it
    /// there.
    pub fn new(bindings: LetBindings<V>) -> Result<Self, Box<LetBindings<V>>> {
        if bindings.admitted_anywhere() {
            Ok(ModuleBindings(bindings))
        } else {
            Err(Box::new(bindings))
        }
    }

    pub fn bindings(&self) -> &LetBindings<V> {
        &self.0
    }

    pub fn into_bindings(self) -> LetBindings<V> {
        self.0
    }
}

/// A `let` group in an expression or a computation expression's body. F#
/// refuses there what it refuses in a module ([`ModuleBindings`]), and also
/// an access modifier (FS0646) and attributes (FS0824), so
/// [`LocalBindings::new`] refuses a group with any of them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalBindings<V: Version>(LetBindings<V>);

impl<V: Version> LocalBindings<V> {
    /// `bindings` as a local group, or `bindings` back if F# refuses it in an
    /// expression.
    pub fn new(bindings: LetBindings<V>) -> Result<Self, Box<LetBindings<V>>> {
        let local = |b: &Binding<V>| {
            let access = match &b.head {
                BindingHead::Name { access, .. } | BindingHead::Function { access, .. } => *access,
                BindingHead::Pattern(_) => None,
            };
            b.attributes.is_empty() && access.is_none()
        };
        if bindings.admitted_anywhere() && bindings.as_slice().iter().all(local) {
            Ok(LocalBindings(bindings))
        } else {
            Err(Box::new(bindings))
        }
    }

    pub fn bindings(&self) -> &LetBindings<V> {
        &self.0
    }

    pub fn into_bindings(self) -> LetBindings<V> {
        self.0
    }
}

/// One binding of a `let` group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding<V: Version> {
    pub attributes: Vec<Attribute<V>>,
    pub is_inline: bool,
    pub head: BindingHead<V>,
    pub body: Expr<V>,
}

/// What a binding binds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingHead<V: Version> {
    /// `let [mutable] [access] x = …`
    Name {
        is_mutable: bool,
        access: Option<Access>,
        name: ValueName,
    },
    /// `let [access] f p1 p2 = …`
    Function {
        access: Option<Access>,
        name: ValueName,
        params: Vec1<Pat<V>>,
    },
    /// `let (p) = …`: a pattern, printed parenthesised so that `Some x`
    /// destructures rather than defining a function called `Some`. `_` is
    /// printed bare, as F# refuses a parenthesised head in a recursive group
    /// (FS3521) but not `let rec _ = …`.
    Pattern(Pat<V>),
}

/// A type definition, one of a `type … and …` group. F#'s checker refuses a
/// type parameter declared twice (FS0037), an abbreviation that does not use
/// every one it declares (FS0035), and a record field or union case declared
/// twice (FS0037), so [`TypeDefn::new`] refuses them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDefn<V: Version> {
    attributes: Vec<Attribute<V>>,
    access: Option<Access>,
    name: EntityName,
    typars: Vec<TyparName>,
    repr: TypeRepr,
}

/// Why F#'s checker refuses a declaration a constructor was handed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclRefusal {
    /// A type parameter is declared twice.
    DuplicateTypar(TyparName),
    /// An abbreviation does not use this type parameter.
    UnusedTypar(TyparName),
    /// A record field, or a union case's or exception's field, is named
    /// twice.
    DuplicateField(Ident),
    /// A union case is declared twice.
    DuplicateCase(Ident),
    /// A union case is named `Tags`, the name of the type F# generates for
    /// the cases' tags (FS1219).
    CaseNamedTags,
    /// A field is named what F# names one of the case's unnamed fields:
    /// `Item`, `Item1`, … in a union case, `Data0`, … in an exception
    /// (FS3176).
    FieldNamedAsGenerated(Ident),
}

impl<V: Version> TypeDefn<V> {
    /// The definition, or why F#'s checker refuses it.
    pub fn new(
        attributes: Vec<Attribute<V>>,
        access: Option<Access>,
        name: EntityName,
        typars: Vec<TyparName>,
        repr: TypeRepr,
    ) -> Result<Self, DeclRefusal> {
        if let Some(t) = first_duplicate(typars.iter()) {
            return Err(DeclRefusal::DuplicateTypar(t.clone()));
        }
        match &repr {
            TypeRepr::Abbrev(ty) => {
                let mut used = Vec::new();
                ty.typars(&mut used);
                if let Some(t) = typars.iter().find(|t| !used.contains(t)) {
                    return Err(DeclRefusal::UnusedTypar(t.clone()));
                }
            }
            TypeRepr::Record(fields) => {
                if let Some(f) = first_duplicate(fields.as_slice().iter().map(|f| &f.name)) {
                    return Err(DeclRefusal::DuplicateField(f.clone()));
                }
            }
            TypeRepr::Union(cases) => {
                if let Some(c) = first_duplicate(cases.as_slice().iter().map(|c| c.name.ident())) {
                    return Err(DeclRefusal::DuplicateCase(c.clone()));
                }
            }
        }
        Ok(TypeDefn {
            attributes,
            access,
            name,
            typars,
            repr,
        })
    }

    pub fn attributes(&self) -> &[Attribute<V>] {
        &self.attributes
    }

    pub fn access(&self) -> Option<Access> {
        self.access
    }

    pub fn name(&self) -> &EntityName {
        &self.name
    }

    pub fn typars(&self) -> &[TyparName] {
        &self.typars
    }

    pub fn repr(&self) -> &TypeRepr {
        &self.repr
    }
}

/// The first item of `items` equal to an earlier one.
fn first_duplicate<'a, T: PartialEq + 'a>(items: impl Iterator<Item = &'a T>) -> Option<&'a T> {
    let mut seen: Vec<&T> = Vec::new();
    for item in items {
        if seen.contains(&item) {
            return Some(item);
        }
        seen.push(item);
    }
    None
}

/// What a type definition defines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeRepr {
    /// `type T = int list`
    Abbrev(Type),
    /// `type T = { A : int }`
    Record(Vec1<RecordField>),
    /// `type T = | A of int | B`
    Union(Vec1<UnionCase>),
}

/// A record type's field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub is_mutable: bool,
    pub name: Ident,
    pub ty: Type,
}

/// A union case. F#'s checker refuses one named `Tags` (FS1219), a field
/// named twice (FS3176), and a field named as F# names an unnamed one
/// (FS3176), so [`UnionCase::new`] refuses them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionCase {
    name: CaseName,
    fields: Vec<UnionField>,
}

impl UnionCase {
    /// The case, or why F#'s checker refuses it.
    pub fn new(name: CaseName, fields: Vec<UnionField>) -> Result<Self, DeclRefusal> {
        if name.as_str() == "Tags" {
            return Err(DeclRefusal::CaseNamedTags);
        }
        // An unnamed field is `Item` in a case of one field, else `Item1`, ….
        let n = fields.len();
        check_fields(&fields, |i| {
            if n == 1 {
                "Item".to_owned()
            } else {
                format!("Item{}", i + 1)
            }
        })?;
        Ok(UnionCase { name, fields })
    }

    pub fn name(&self) -> &CaseName {
        &self.name
    }

    pub fn fields(&self) -> &[UnionField] {
        &self.fields
    }
}

/// An exception's declaration, `exception E of …`. F#'s checker refuses a
/// field named twice (FS3176), and a field named as F# names an unnamed one
/// (FS3176), so [`ExceptionDefn::new`] refuses them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExceptionDefn {
    name: CaseName,
    fields: Vec<UnionField>,
}

impl ExceptionDefn {
    /// The exception, or why F#'s checker refuses it.
    pub fn new(name: CaseName, fields: Vec<UnionField>) -> Result<Self, DeclRefusal> {
        // An unnamed field is `Data0`, `Data1`, ….
        check_fields(&fields, |i| format!("Data{i}"))?;
        Ok(ExceptionDefn { name, fields })
    }

    pub fn name(&self) -> &CaseName {
        &self.name
    }

    pub fn fields(&self) -> &[UnionField] {
        &self.fields
    }
}

/// Whether F# admits `fields`' names, where `generated(i)` names the `i`th
/// field if it is unnamed: no name twice, and none an unnamed field's.
fn check_fields(
    fields: &[UnionField],
    generated: impl Fn(usize) -> String,
) -> Result<(), DeclRefusal> {
    if let Some(f) = first_duplicate(fields.iter().filter_map(|f| f.name.as_ref())) {
        return Err(DeclRefusal::DuplicateField(f.clone()));
    }
    let unnamed: Vec<String> = fields
        .iter()
        .enumerate()
        .filter(|(_, f)| f.name.is_none())
        .map(|(i, _)| generated(i))
        .collect();
    match fields
        .iter()
        .filter_map(|f| f.name.as_ref())
        .find(|n| unnamed.iter().any(|u| u == n.as_str()))
    {
        Some(n) => Err(DeclRefusal::FieldNamedAsGenerated(n.clone())),
        None => Ok(()),
    }
}

/// One field of a union case, `int` or `x : int`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionField {
    pub name: Option<Ident>,
    pub ty: Type,
}

/// A literal constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    /// `()`
    Unit,
    Bool(bool),
    /// `1y`
    SByte(i8),
    /// `1uy`
    Byte(u8),
    /// `1s`
    Int16(i16),
    /// `1us`
    UInt16(u16),
    /// `1`
    Int32(i32),
    /// `1u`
    UInt32(u32),
    /// `1L`
    Int64(i64),
    /// `1UL`
    UInt64(u64),
    /// `1n`
    NativeInt(i64),
    /// `1un`
    UNativeInt(u64),
    /// `1.0f`
    Single(Float32),
    /// `1.0`
    Double(Float64),
    /// A UTF-16 code unit, as F#'s `char` is; a lone surrogate is a value.
    Char(u16),
    String(String),
}

/// An IEEE 754 single, compared by its bits, so every value (`-0.0`, each NaN)
/// is distinct and has a literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Float32(pub u32);

impl Float32 {
    pub fn new(value: f32) -> Self {
        Float32(value.to_bits())
    }

    pub fn value(self) -> f32 {
        f32::from_bits(self.0)
    }
}

/// An IEEE 754 double, compared by its bits, so every value (`-0.0`, each NaN)
/// is distinct and has a literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Float64(pub u64);

impl Float64 {
    pub fn new(value: f64) -> Self {
        Float64(value.to_bits())
    }

    pub fn value(self) -> f64 {
        f64::from_bits(self.0)
    }
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<V: Version> {
    Const(Const),
    /// `null`
    Null,
    /// A name or dotted path, `x` or `A.B.c`.
    Name(LongIdent),
    /// An operator as a value, `( + )`.
    OpValue(Operator),
    /// `f x`: `func` applied to one argument, passed whole, so `f (a, b)`
    /// with a tuple argument is printed `f ((a, b))`. A [`Const::Unit`]
    /// argument is printed `f ()`, which calls a method with no arguments
    /// rather than with `()`.
    App {
        func: Box<Expr<V>>,
        arg: Box<Expr<V>>,
    },
    /// `f (a, b, x = c)`: `func` applied to an argument list, as a method is
    /// called.
    MethodApp {
        func: Box<Expr<V>>,
        args: Args<V>,
    },
    /// `a op b`
    Infix {
        op: InfixOperator,
        lhs: Box<Expr<V>>,
        rhs: Box<Expr<V>>,
    },
    /// `a, b`
    Tuple(Vec2<Expr<V>>),
    /// `[]`, or `[ body ]`.
    List(Option<Box<ListBody<V>>>),
    /// `[||]`, or `[| body |]`, as [`Expr::List`].
    Array(Option<Box<ListBody<V>>>),
    /// `{ A = a }` or `{ r with A = a }`
    Record {
        copy: Option<Box<Expr<V>>>,
        fields: Vec1<(LongIdent, Expr<V>)>,
    },
    /// `(e).f`: a field of an expression's value. `A.B.c` is a [`Expr::Name`].
    FieldGet {
        expr: Box<Expr<V>>,
        field: Ident,
    },
    /// `a.b <- v`
    Set {
        target: LongIdent,
        value: Box<Expr<V>>,
    },
    /// `fun p1 p2 -> e`
    Lambda {
        params: Vec1<Pat<V>>,
        body: Box<Expr<V>>,
    },
    /// `function | p -> e …`
    Function(Vec1<MatchClause<V>>),
    /// `match e with | p -> e …`
    Match {
        scrutinee: Box<Expr<V>>,
        clauses: Vec1<MatchClause<V>>,
    },
    /// `if c then a [else b]`
    IfThenElse {
        cond: Box<Expr<V>>,
        then_branch: Box<Expr<V>>,
        else_branch: Option<Box<Expr<V>>>,
    },
    /// `let … in e`
    LetIn {
        bindings: LocalBindings<V>,
        body: Box<Expr<V>>,
    },
    /// `a; b`
    Sequential(Box<Expr<V>>, Box<Expr<V>>),
    /// `e : t`
    Typed {
        expr: Box<Expr<V>>,
        ty: Type,
    },
    /// `e :? t`
    TypeTest {
        expr: Box<Expr<V>>,
        ty: Type,
    },
    /// `e :> t`
    Upcast {
        expr: Box<Expr<V>>,
        ty: Type,
    },
    /// `e :?> t`
    Downcast {
        expr: Box<Expr<V>>,
        ty: Type,
    },
    /// `h :: t`
    Cons {
        head: Box<Expr<V>>,
        tail: Box<Expr<V>>,
    },
    /// `try e with | p -> e …`
    TryWith {
        body: Box<Expr<V>>,
        clauses: Vec1<MatchClause<V>>,
    },
    /// `try e finally f`
    TryFinally {
        body: Box<Expr<V>>,
        finally: Box<Expr<V>>,
    },
    /// `while c do e done`
    While {
        cond: Box<Expr<V>>,
        body: Box<Expr<V>>,
    },
    /// `for i = a to b do e done`
    For {
        var: Ident,
        from: Box<Expr<V>>,
        direction: ForDirection,
        to: Box<Expr<V>>,
        body: Box<Expr<V>>,
    },
    /// `for p in e do e done`
    ForEach {
        pat: Pat<V>,
        source: Box<ForSource<V>>,
        body: Box<Expr<V>>,
    },
    /// `lazy e`
    Lazy(Box<Expr<V>>),
    /// `assert e`
    Assert(Box<Expr<V>>),
    /// `do e`
    Do(Box<Expr<V>>),
    /// `_.A.B`: a function reading a member path of its argument.
    DotLambda {
        gate: V::AccessorFunctionShorthand,
        path: LongIdent,
    },
    /// `builder { body }`, a computation expression.
    Computation {
        builder: Box<Expr<V>>,
        body: Box<Comp<V, InBuilder>>,
    },
}

/// Where a computation expression's body sits, as a type: in a builder's
/// braces ([`InBuilder`]) or in a list's or array's brackets
/// ([`InCollection`]). F#'s checker translates the two by different rules: a
/// list's body is a sequence expression, which has no `let!` or `return`
/// and, before F# 8, no `try … with`. Each such statement carries a field of
/// the context's gate type, as a version-gated construct carries its
/// version's ([`crate::version`]), so a list cannot hold one.
///
/// `seq { … }` is a sequence expression too, but only because `seq` names
/// FSharp.Core's function, which the tree cannot see: a
/// [`Expr::Computation`] is checked as a builder's, so its builder must not
/// be `seq`.
pub trait Context:
    sealed::Sealed + Debug + Clone + Copy + PartialEq + Eq + Hash + Send + Sync + 'static
{
    /// What only a builder translates: `let!`, `use!`, `do!`, `match!`,
    /// `while!`, `return` and `return!`.
    type Bang: Gate;

    /// `try … with` as a statement.
    type TryWith<V: Version>: Gate;

    /// An expression statement printed in parentheses
    /// ([`needs_parentheses`]): a builder's checker refuses it ("this
    /// construct is ambiguous"), and a list's does in a comprehension before
    /// implicit yields.
    type ParenExpr<V: Version>: Gate;

    /// Whether the body is in braces, where F# reads a first statement
    /// `a = b` as a record's field.
    const BRACED: bool;
}

mod sealed {
    pub trait Sealed {}
}

/// A builder's body, `builder { … }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InBuilder {}

/// A list's or array's body, `[ … ]` or `[| … |]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InCollection {}

impl sealed::Sealed for InBuilder {}
impl Context for InBuilder {
    type Bang = Available;
    type TryWith<V: Version> = Available;
    type ParenExpr<V: Version> = Unavailable;
    const BRACED: bool = true;
}

impl sealed::Sealed for InCollection {}
impl Context for InCollection {
    type Bang = Unavailable;
    type TryWith<V: Version> = V::TryWithInSeqExpression;
    type ParenExpr<V: Version> = V::ImplicitYield;
    const BRACED: bool = false;
}

/// A list's or array's contents. F# reads a body as a literal's elements
/// exactly when each statement is an expression other than a bare `do` (its
/// `SimpleSemicolonSequence`), and as a comprehension otherwise; the two can
/// mean different things (`[(do ())]` is `[()]`, `[do ()]` is `[]`), so
/// they are different values here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ListBody<V: Version> {
    /// `[a; b]`: a literal's elements, each printed in parentheses.
    Elements(Vec1<Expr<V>>),
    /// `[a .. b]`. F# has a range only as a whole list body and as a
    /// `for … in` loop's source; it is not an expression or a statement.
    Range(Range<V>),
    /// A comprehension.
    Comp(ListComp<V>),
}

/// A comprehension: a list's statements, which F# must not read as a
/// literal's elements ([`ListComp::new`]). Before implicit yields (F# 4.7)
/// F#'s checker reads an `if` that yields nothing among expression
/// statements as a literal's element too, and refuses it (FS0035), so such a
/// body has no spelling there; in parentheses the `if` is an element of
/// [`ListBody::Elements`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListComp<V: Version>(Comp<V, InCollection>);

impl<V: Version> ListComp<V> {
    /// `comp` as a comprehension, or `comp` back if F# at `V` would read it
    /// as a literal's elements.
    pub fn new(comp: Comp<V, InCollection>) -> Result<Self, Box<Comp<V, InCollection>>> {
        if is_literal_shaped(&comp) {
            return Err(Box::new(comp));
        }
        Ok(ListComp(comp))
    }

    /// `comp` as a comprehension, unchecked, so an oracle can print a body
    /// [`ListComp::new`] refuses and show that F# refuses it too.
    #[cfg(feature = "test-support")]
    pub fn unchecked(comp: Comp<V, InCollection>) -> Self {
        ListComp(comp)
    }

    pub fn comp(&self) -> &Comp<V, InCollection> {
        &self.0
    }

    pub fn into_comp(self) -> Comp<V, InCollection> {
        self.0
    }
}

/// Whether F# at `V` reads `comp`, printed, as a literal's elements: no
/// binding, and every statement an expression other than a bare `do` or,
/// before implicit yields, an `if` that yields nothing (FCS's
/// `IsSimpleSemicolonSequenceElement`).
fn is_literal_shaped<V: Version>(comp: &Comp<V, InCollection>) -> bool {
    let deprecated_if = V::ImplicitYield::WITNESS.is_none();
    let simple = |s: &Stmt<V, InCollection>| match s {
        Stmt::Expr(e) => !matches!(e.expr(), Expr::Do(_)),
        Stmt::IfThenElse { .. } => deprecated_if && yield_free_stmt(s),
        _ => false,
    };
    comp.init
        .iter()
        .all(|item| matches!(item, CompItem::Stmt(s) if simple(s)))
        && simple(&comp.last)
}

/// Whether `comp` has no `yield`, as F# before implicit yields reckoned it
/// (its `YieldFree`, the only version that asks), which counts `yield!` and a
/// bare `do` as yielding.
fn yield_free<V: Version, K: Context>(comp: &Comp<V, K>) -> bool {
    comp.init.iter().all(|item| match item {
        CompItem::Stmt(s) => yield_free_stmt(s),
        _ => true,
    }) && yield_free_stmt(&comp.last)
}

fn yield_free_stmt<V: Version, K: Context>(s: &Stmt<V, K>) -> bool {
    let clauses = |cs: &Vec1<CompClause<V, K>>| cs.as_slice().iter().all(|c| yield_free(&c.body));
    match s {
        Stmt::Yield(_) | Stmt::YieldFrom(_) => false,
        Stmt::Expr(e) => !matches!(e.expr(), Expr::Do(_)),
        Stmt::DoBang { .. } | Stmt::Return { .. } | Stmt::ReturnFrom { .. } => true,
        Stmt::IfThenElse {
            then_branch,
            else_branch,
            ..
        } => yield_free(then_branch) && else_branch.as_deref().is_none_or(yield_free),
        Stmt::Match { clauses: cs, .. } | Stmt::MatchBang { clauses: cs, .. } => clauses(cs),
        Stmt::While { body, .. }
        | Stmt::WhileBang { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForEach { body, .. }
        | Stmt::TryFinally { body, .. } => yield_free(body),
        Stmt::TryWith {
            body, clauses: cs, ..
        } => yield_free(body) && clauses(cs),
    }
}

/// A computation expression's body: statements and bindings one after
/// another, ending in a statement. Each binding scopes over everything after
/// it, which is how F# nests a block's bindings; the tree keeps the block
/// flat, so a long body (a list literal's elements) is a vector, not a chain.
///
/// Its statements are not expressions. F#'s checker translates a body by its
/// shape, and refuses a control construct in parentheses ("this construct is
/// ambiguous"), so the printer writes statements bare, one per line, and keeps
/// only their operands in parentheses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comp<V: Version, K: Context> {
    /// What comes before the last statement.
    pub init: Vec<CompItem<V, K>>,
    pub last: Stmt<V, K>,
}

impl<V: Version, K: Context> Comp<V, K> {
    /// A body of one statement.
    pub fn stmt(last: Stmt<V, K>) -> Self {
        Comp {
            init: Vec::new(),
            last,
        }
    }
}

/// A statement or binding of a [`Comp`] before its last statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompItem<V: Version, K: Context> {
    Stmt(Stmt<V, K>),
    /// `let …`
    Let(LocalBindings<V>),
    /// `use x = e`
    Use(UseBinding<V>),
    /// `let! p = e`, and any `and! q = f`.
    LetBang(LetBang<V, K>),
    /// `use! x = e`
    UseBang(UseBang<V, K>),
}

/// `use x = e` or `use _ = e`. In a computation expression F# takes the
/// discard at every version; F# 6 added it to `use … in` expressions, which
/// the tree does not have.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseBinding<V: Version> {
    pub name: UseName<Available>,
    pub value: Expr<V>,
}

/// What a `use` or `use!` binds: a name, or nothing, where the version has
/// the discard (`gate`). F# takes no other pattern there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseName<G: Gate> {
    Named(ValueName),
    Discard(G),
}

/// `let! p = e`, and any `and! q = f`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetBang<V: Version, K: Context> {
    pub gate: K::Bang,
    pub pat: Pat<V>,
    pub value: Expr<V>,
    pub ands: Vec<AndBang<V>>,
}

/// `use! x = e` or `use! _ = e`. F# takes no `and!` after it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseBang<V: Version, K: Context> {
    pub gate: K::Bang,
    pub name: UseName<V::UseBangBindingValueDiscard>,
    pub value: Expr<V>,
}

/// `and! p = e`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AndBang<V: Version> {
    pub gate: V::AndBang,
    pub pat: Pat<V>,
    pub value: Expr<V>,
}

/// An expression statement's expression. One that bare F# would not read as
/// an expression statement ([`needs_parentheses`]) is printed in
/// parentheses, which only some contexts and versions accept
/// ([`Context::ParenExpr`]); [`StmtExpr::new`] refuses it elsewhere. An
/// `if`, `match`, `let`, `try`, loop or sequence written as the statement
/// instead (an `if` statement of expression statements) means the same.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StmtExpr<V: Version, K: Context> {
    expr: Expr<V>,
    context: PhantomData<K>,
}

impl<V: Version, K: Context> StmtExpr<V, K> {
    /// `expr` as a statement, or `expr` back if it needs parentheses and `K`
    /// at `V` refuses them.
    pub fn new(expr: Expr<V>) -> Result<Self, Expr<V>> {
        if needs_parentheses::<V, K>(&expr) && K::ParenExpr::<V>::WITNESS.is_none() {
            return Err(expr);
        }
        Ok(StmtExpr {
            expr,
            context: PhantomData,
        })
    }

    pub fn expr(&self) -> &Expr<V> {
        &self.expr
    }

    pub fn into_expr(self) -> Expr<V> {
        self.expr
    }
}

/// Whether `e`, as an expression statement in a body of context `K`, needs
/// parentheses. Bare, F# would read an `if`, `match`, `let`, `try`, loop or
/// sequence as a statement of its own, refuse a type annotation `e : t` and
/// `( * )` (a parenthesised wildcard to F#), and, first in a builder's
/// braces, read `a = b` as a record's field (a builder takes no such
/// statement anywhere).
pub fn needs_parentheses<V: Version, K: Context>(e: &Expr<V>) -> bool {
    match e {
        Expr::IfThenElse { .. }
        | Expr::Match { .. }
        | Expr::LetIn { .. }
        | Expr::Sequential(..)
        | Expr::TryWith { .. }
        | Expr::TryFinally { .. }
        | Expr::While { .. }
        | Expr::For { .. }
        | Expr::ForEach { .. }
        | Expr::Typed { .. } => true,
        Expr::Infix { op, .. } => K::BRACED && op.operator().as_str() == "=",
        // Printed `( * )`, which F# reads as a parenthesised wildcard.
        Expr::OpValue(op) => op.as_str() == "*",
        Expr::Const(_)
        | Expr::Null
        | Expr::Name(_)
        | Expr::App { .. }
        | Expr::MethodApp { .. }
        | Expr::Tuple(_)
        | Expr::List(_)
        | Expr::Array(_)
        | Expr::Record { .. }
        | Expr::FieldGet { .. }
        | Expr::Set { .. }
        | Expr::Lambda { .. }
        | Expr::Function(_)
        | Expr::TypeTest { .. }
        | Expr::Upcast { .. }
        | Expr::Downcast { .. }
        | Expr::Cons { .. }
        | Expr::Lazy(_)
        | Expr::Assert(_)
        | Expr::Do(_)
        | Expr::DotLambda { .. }
        | Expr::Computation { .. } => false,
    }
}

/// A statement of a computation expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt<V: Version, K: Context> {
    /// An expression: a value the builder combines, or an implicit yield.
    Expr(StmtExpr<V, K>),
    /// `do! e`
    DoBang { gate: K::Bang, expr: Expr<V> },
    /// `return e`
    Return { gate: K::Bang, expr: Expr<V> },
    /// `return! e`
    ReturnFrom { gate: K::Bang, expr: Expr<V> },
    /// `yield e`
    Yield(Expr<V>),
    /// `yield! e`
    YieldFrom(Expr<V>),
    /// `if c then a [else b]`
    IfThenElse {
        cond: Expr<V>,
        then_branch: Box<Comp<V, K>>,
        else_branch: Option<Box<Comp<V, K>>>,
    },
    /// `match e with | p -> c …`
    Match {
        scrutinee: Expr<V>,
        clauses: Vec1<CompClause<V, K>>,
    },
    /// `match! e with | p -> c …`
    MatchBang {
        gate: K::Bang,
        scrutinee: Expr<V>,
        clauses: Vec1<CompClause<V, K>>,
    },
    /// `while c do b done`
    While {
        cond: Expr<V>,
        body: Box<Comp<V, K>>,
    },
    /// `while! c do b done`
    WhileBang {
        gate: V::WhileBang,
        bang: K::Bang,
        cond: Expr<V>,
        body: Box<Comp<V, K>>,
    },
    /// `for i = a to b do c done`
    For {
        var: Ident,
        from: Expr<V>,
        direction: ForDirection,
        to: Expr<V>,
        body: Box<Comp<V, K>>,
    },
    /// `for p in e do c done`
    ForEach {
        pat: Pat<V>,
        source: ForSource<V>,
        body: Box<Comp<V, K>>,
    },
    /// `try c with | p -> c …`
    TryWith {
        gate: K::TryWith<V>,
        body: Box<Comp<V, K>>,
        clauses: Vec1<CompClause<V, K>>,
    },
    /// `try c finally e`
    TryFinally {
        body: Box<Comp<V, K>>,
        finally: Expr<V>,
    },
}

/// What a `for … in` loop runs over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForSource<V: Version> {
    Expr(Expr<V>),
    Range(Range<V>),
}

/// `from .. to`, or `from .. step .. to`: a whole list body
/// ([`ListBody::Range`]) or a `for … in` loop's source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Range<V: Version> {
    pub from: Expr<V>,
    pub step: Option<Expr<V>>,
    pub to: Expr<V>,
}

/// `| pat [when guard] -> body` in a computation expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompClause<V: Version, K: Context> {
    pub pat: Pat<V>,
    pub guard: Option<Expr<V>>,
    pub body: Comp<V, K>,
}

/// Which way a `for … to/downto` loop counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ForDirection {
    To,
    Downto,
}

/// `| pat [when guard] -> result`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchClause<V: Version> {
    pub pat: Pat<V>,
    pub guard: Option<Expr<V>>,
    pub result: Expr<V>,
}

/// A pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat<V: Version> {
    /// `_`
    Wildcard,
    /// A name or dotted path, `x`, `None` or `A.B`. Whether it binds a variable
    /// or matches a union case is name resolution's business, not the
    /// parser's.
    Name(LongIdent),
    /// `A.B p1 p2`
    Ctor {
        name: LongIdent,
        args: Vec1<Pat<V>>,
    },
    Const(Const),
    /// `null`
    Null,
    /// `a, b`
    Tuple(Vec2<Pat<V>>),
    /// `[a; b]`
    List(Vec<Pat<V>>),
    /// `[|a; b|]`
    Array(Vec<Pat<V>>),
    /// `h :: t`
    Cons {
        head: Box<Pat<V>>,
        tail: Box<Pat<V>>,
    },
    /// `p : t`
    Typed {
        pat: Box<Pat<V>>,
        ty: Type,
    },
    /// `p as q`
    As {
        pat: Box<Pat<V>>,
        alias: AsAlias<V>,
    },
    /// `p | q`
    Or(Box<Pat<V>>, Box<Pat<V>>),
    /// `p & q`
    Ands(Vec2<Pat<V>>),
    /// `{ A = p }`
    Record(Vec1<(LongIdent, Pat<V>)>),
    /// `:? t`
    IsInst(Type),
}

/// What follows `as` in a pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsAlias<V: Version> {
    /// `p as x`: a variable, the only alias before F# 6.
    Var(VarName),
    /// `p as (q)`: any other pattern (F# 6).
    Pat(AliasPat<V>),
}

/// A pattern after `as` other than a variable. F# reads `p as (x)` as
/// `p as x`, so [`AliasPat::new`] refuses a variable, which is
/// [`AsAlias::Var`]'s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AliasPat<V: Version> {
    gate: V::NonVariablePatternsToRightOfAsPatterns,
    pat: Box<Pat<V>>,
}

impl<V: Version> AliasPat<V> {
    /// `pat` as an alias, or `pat` back if it is a variable.
    pub fn new(
        gate: V::NonVariablePatternsToRightOfAsPatterns,
        pat: Pat<V>,
    ) -> Result<Self, Box<Pat<V>>> {
        let is_var = match &pat {
            Pat::Name(path) => match path.segments() {
                [only] => VarName::new(only.clone()).is_ok(),
                _ => false,
            },
            _ => false,
        };
        if is_var {
            Err(Box::new(pat))
        } else {
            Ok(AliasPat {
                gate,
                pat: Box::new(pat),
            })
        }
    }

    pub fn gate(&self) -> V::NonVariablePatternsToRightOfAsPatterns {
        self.gate
    }

    pub fn pat(&self) -> &Pat<V> {
        &self.pat
    }
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A named type, `int` or `System.String`.
    Name(LongIdent),
    /// A generic type applied to arguments, `Map<int, string>`.
    App { head: LongIdent, args: Vec1<Type> },
    /// A type variable, `'a`.
    Var(TyparName),
    /// `a -> b`
    Fun { arg: Box<Type>, ret: Box<Type> },
    /// `a * b`
    Tuple(Vec2<Type>),
    /// `t[]`, `t[,]`, …
    Array { rank: ArrayRank, elem: Box<Type> },
    /// `_`
    Anon,
}

impl Type {
    /// Push the type variables `self` uses onto `out`.
    fn typars(&self, out: &mut Vec<TyparName>) {
        match self {
            Type::Name(_) | Type::Anon => {}
            Type::Var(t) => out.push(t.clone()),
            Type::App { args, .. } => args.as_slice().iter().for_each(|a| a.typars(out)),
            Type::Fun { arg, ret } => {
                arg.typars(out);
                ret.typars(out);
            }
            Type::Tuple(ts) => ts.as_slice().iter().for_each(|t| t.typars(out)),
            Type::Array { elem, .. } => elem.typars(out),
        }
    }
}

/// An array type's rank: 1 for `t[]`, 2 for `t[,]`, up to 32, .NET's limit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArrayRank(u8);

impl ArrayRank {
    /// `rank`, or `None` outside 1–32.
    pub fn new(rank: u8) -> Option<Self> {
        (1..=32).contains(&rank).then_some(ArrayRank(rank))
    }

    pub fn get(self) -> u8 {
        self.0
    }
}
