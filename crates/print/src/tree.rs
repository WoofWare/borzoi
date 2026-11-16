//! The owned syntax tree a program builds and [`crate::print_impl_file`]
//! writes.
//!
//! It models what source *means* to F#'s parser, not how it was laid out:
//! there are no parentheses, no comments and no layout, and two spellings with
//! one parse share one value. Where F#'s grammar has a constraint the parser
//! enforces, the types enforce it too, so every value prints as source F#
//! parses back to that value.

use crate::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use crate::vec::{Vec1, Vec2};

/// An implementation file (`.fs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplFile {
    /// A file with no `module` or `namespace` header.
    AnonModule(Vec<ModuleDecl>),
    /// `module A.B` followed by its declarations.
    NamedModule(NamedModule),
    /// One or more `namespace` sections.
    Namespaces(Vec1<Namespace>),
}

/// A file-level `module A.B`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedModule {
    pub attributes: Vec<Attribute>,
    pub access: Option<Access>,
    pub is_rec: bool,
    pub name: LongIdent,
    pub decls: Vec<ModuleDecl>,
}

/// A `namespace` section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Namespace {
    pub is_rec: bool,
    pub name: NamespaceName,
    pub decls: Vec<ModuleDecl>,
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

/// An attribute, `[<Name(arg)>]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub name: LongIdent,
    /// The argument; [`Const::Unit`] is an attribute written without one,
    /// which is how F# reads `[<A>]` and `[<A()>]` alike.
    pub arg: Expr,
}

/// A declaration in a module or namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleDecl {
    /// `let …` or `let rec … and …`.
    Let(LetBindings),
    /// An expression evaluated for its effect.
    Expr(Expr),
    /// `open A.B`
    Open(LongIdent),
    /// `module M = …`
    NestedModule(NestedModule),
    /// `module M = A.B`
    ModuleAbbrev { name: Ident, target: LongIdent },
    /// `type A = … and B = …`
    Types(Vec1<TypeDefn>),
    /// `exception E of …`
    Exception(UnionCase),
}

/// A nested `module M =` and its declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedModule {
    pub attributes: Vec<Attribute>,
    pub access: Option<Access>,
    pub is_rec: bool,
    pub name: Ident,
    pub decls: Vec<ModuleDecl>,
}

/// One `let` group. A non-recursive group has one binding: F# rejects
/// `let a = 1 and b = 2` at module level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LetBindings {
    /// `let …`
    NonRec(Box<Binding>),
    /// `let rec … and …`
    Rec(Vec1<Binding>),
}

/// One binding of a `let` group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub attributes: Vec<Attribute>,
    pub is_inline: bool,
    pub head: BindingHead,
    pub body: Expr,
}

/// What a binding binds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingHead {
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
        params: Vec1<Pat>,
    },
    /// `let (p) = …`: a pattern, printed parenthesised so that `Some x`
    /// destructures rather than defining a function called `Some`.
    Pattern(Pat),
}

/// A type definition, one of a `type … and …` group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDefn {
    pub attributes: Vec<Attribute>,
    pub access: Option<Access>,
    pub name: Ident,
    pub typars: Vec<TyparName>,
    pub repr: TypeRepr,
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

/// A union case, or an exception's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionCase {
    pub name: Ident,
    pub fields: Vec<UnionField>,
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
pub enum Expr {
    Const(Const),
    /// `null`
    Null,
    /// A name or dotted path, `x` or `A.B.c`.
    Name(LongIdent),
    /// An operator as a value, `( + )`.
    OpValue(Operator),
    /// `f x`
    App {
        func: Box<Expr>,
        arg: Box<Expr>,
    },
    /// `a op b`
    Infix {
        op: InfixOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `a, b`
    Tuple(Vec2<Expr>),
    /// `[a; b]`
    List(Vec<Expr>),
    /// `[|a; b|]`
    Array(Vec<Expr>),
    /// `{ A = a }` or `{ r with A = a }`
    Record {
        copy: Option<Box<Expr>>,
        fields: Vec1<(LongIdent, Expr)>,
    },
    /// `(e).f`: a field of an expression's value. `A.B.c` is a [`Expr::Name`].
    FieldGet {
        expr: Box<Expr>,
        field: Ident,
    },
    /// `a.b <- v`
    Set {
        target: LongIdent,
        value: Box<Expr>,
    },
    /// `fun p1 p2 -> e`
    Lambda {
        params: Vec1<Pat>,
        body: Box<Expr>,
    },
    /// `function | p -> e …`
    Function(Vec1<MatchClause>),
    /// `match e with | p -> e …`
    Match {
        scrutinee: Box<Expr>,
        clauses: Vec1<MatchClause>,
    },
    /// `if c then a [else b]`
    IfThenElse {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    /// `let … in e`
    LetIn {
        bindings: LetBindings,
        body: Box<Expr>,
    },
    /// `a; b`
    Sequential(Box<Expr>, Box<Expr>),
    /// `e : t`
    Typed {
        expr: Box<Expr>,
        ty: Type,
    },
    /// `e :? t`
    TypeTest {
        expr: Box<Expr>,
        ty: Type,
    },
    /// `e :> t`
    Upcast {
        expr: Box<Expr>,
        ty: Type,
    },
    /// `e :?> t`
    Downcast {
        expr: Box<Expr>,
        ty: Type,
    },
    /// `h :: t`
    Cons {
        head: Box<Expr>,
        tail: Box<Expr>,
    },
    /// `try e with | p -> e …`
    TryWith {
        body: Box<Expr>,
        clauses: Vec1<MatchClause>,
    },
    /// `try e finally f`
    TryFinally {
        body: Box<Expr>,
        finally: Box<Expr>,
    },
    /// `while c do e done`
    While {
        cond: Box<Expr>,
        body: Box<Expr>,
    },
    /// `for i = a to b do e done`
    For {
        var: Ident,
        from: Box<Expr>,
        direction: ForDirection,
        to: Box<Expr>,
        body: Box<Expr>,
    },
    /// `for p in e do e done`
    ForEach {
        pat: Pat,
        source: Box<Expr>,
        body: Box<Expr>,
    },
    /// `lazy e`
    Lazy(Box<Expr>),
    /// `assert e`
    Assert(Box<Expr>),
    /// `do e`
    Do(Box<Expr>),
}

/// Which way a `for … to/downto` loop counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ForDirection {
    To,
    Downto,
}

/// `| pat [when guard] -> result`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchClause {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub result: Expr,
}

/// A pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat {
    /// `_`
    Wildcard,
    /// A name or dotted path, `x`, `None` or `A.B`. Whether it binds a variable
    /// or matches a union case is name resolution's business, not the
    /// parser's.
    Name(LongIdent),
    /// `A.B p1 p2`
    Ctor {
        name: LongIdent,
        args: Vec1<Pat>,
    },
    Const(Const),
    /// `null`
    Null,
    /// `a, b`
    Tuple(Vec2<Pat>),
    /// `[a; b]`
    List(Vec<Pat>),
    /// `[|a; b|]`
    Array(Vec<Pat>),
    /// `h :: t`
    Cons {
        head: Box<Pat>,
        tail: Box<Pat>,
    },
    /// `p : t`
    Typed {
        pat: Box<Pat>,
        ty: Type,
    },
    /// `p as q`
    As {
        pat: Box<Pat>,
        alias: Box<Pat>,
    },
    /// `p | q`
    Or(Box<Pat>, Box<Pat>),
    /// `p & q`
    Ands(Vec2<Pat>),
    /// `{ A = p }`
    Record(Vec1<(LongIdent, Pat)>),
    /// `:? t`
    IsInst(Type),
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
