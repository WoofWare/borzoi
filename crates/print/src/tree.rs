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

use crate::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use crate::vec::{Vec1, Vec2};
use crate::version::Version;

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
    pub is_rec: bool,
    pub name: LongIdent,
    pub decls: Vec<ModuleDecl<V>>,
}

/// A `namespace` section.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Namespace<V: Version> {
    pub is_rec: bool,
    pub name: NamespaceName,
    pub decls: Vec<ModuleDecl<V>>,
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
    Let(LetBindings<V>),
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
    Exception(UnionCase),
}

/// A nested `module M =` and its declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NestedModule<V: Version> {
    pub attributes: Vec<Attribute<V>>,
    pub access: Option<Access>,
    pub is_rec: bool,
    pub name: Ident,
    pub decls: Vec<ModuleDecl<V>>,
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

/// One binding of a `let` group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding<V: Version> {
    pub attributes: Vec<Attribute<V>>,
    pub is_inline: bool,
    pub head: BindingHead,
    pub body: Expr<V>,
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
pub struct TypeDefn<V: Version> {
    pub attributes: Vec<Attribute<V>>,
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
pub enum Expr<V: Version> {
    Const(Const),
    /// `null`
    Null,
    /// A name or dotted path, `x` or `A.B.c`.
    Name(LongIdent),
    /// An operator as a value, `( + )`.
    OpValue(Operator),
    /// `f x`: `func` applied to one argument, passed whole, so `f (a, b)`
    /// with a tuple argument is printed `f ((a, b))`.
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
    /// `[]`, or `[ body ]`: `[a; b]` is the body of two expression
    /// statements ([`Comp::exprs`]), and `[ for x in xs -> f x ]` a
    /// comprehension; F# parses the two alike.
    List(Option<Box<Comp<V>>>),
    /// `[||]`, or `[| body |]`, as [`Expr::List`].
    Array(Option<Box<Comp<V>>>),
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
        params: Vec1<Pat>,
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
        bindings: LetBindings<V>,
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
        pat: Pat,
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
        body: Box<Comp<V>>,
    },
}

/// A computation expression's body: statements one after another, each
/// binding scoping over the statements after it, as F# nests them.
///
/// Its statements are not expressions. F#'s checker translates a body by its
/// shape, and refuses a control construct in parentheses ("this construct is
/// ambiguous"), so the printer writes statements bare, one per line, and keeps
/// only their operands in parentheses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Comp<V: Version> {
    /// The last statement.
    Last(Stmt<V>),
    /// A statement, then the rest.
    Then(Stmt<V>, Box<Comp<V>>),
    /// `let …`, then the rest.
    Let(LetBindings<V>, Box<Comp<V>>),
    /// `use p = e`, then the rest.
    Use(Box<Binding<V>>, Box<Comp<V>>),
    /// `let! p = e` or `use! p = e`, any `and! q = f`, then the rest.
    Bang {
        kind: BangKind,
        pat: Pat,
        value: Expr<V>,
        ands: Vec<AndBang<V>>,
        rest: Box<Comp<V>>,
    },
}

impl<V: Version> Comp<V> {
    /// `a; b; …`: each item an expression statement, as a list literal's
    /// elements are.
    pub fn exprs(items: crate::vec::Vec1<Expr<V>>) -> Self {
        let mut items = items.into_vec();
        let last = items.pop().expect("non-empty");
        items
            .into_iter()
            .rev()
            .fold(Comp::Last(Stmt::Expr(last)), |rest, e| {
                Comp::Then(Stmt::Expr(e), Box::new(rest))
            })
    }
}

/// Whether a bang binding is `let!` or `use!`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BangKind {
    Let,
    Use,
}

/// `and! p = e`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AndBang<V: Version> {
    pub gate: V::AndBang,
    pub pat: Pat,
    pub value: Expr<V>,
}

/// A statement of a computation expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt<V: Version> {
    /// An expression: a value the builder combines, or an implicit yield.
    Expr(Expr<V>),
    /// `do! e`
    DoBang(Expr<V>),
    /// `return e`
    Return(Expr<V>),
    /// `return! e`
    ReturnFrom(Expr<V>),
    /// `yield e`
    Yield(Expr<V>),
    /// `yield! e`
    YieldFrom(Expr<V>),
    /// `if c then a [else b]`
    IfThenElse {
        cond: Expr<V>,
        then_branch: Box<Comp<V>>,
        else_branch: Option<Box<Comp<V>>>,
    },
    /// `match e with | p -> c …`
    Match {
        scrutinee: Expr<V>,
        clauses: Vec1<CompClause<V>>,
    },
    /// `match! e with | p -> c …`
    MatchBang {
        scrutinee: Expr<V>,
        clauses: Vec1<CompClause<V>>,
    },
    /// `while c do b done`
    While { cond: Expr<V>, body: Box<Comp<V>> },
    /// `while! c do b done`
    WhileBang {
        gate: V::WhileBang,
        cond: Expr<V>,
        body: Box<Comp<V>>,
    },
    /// `for i = a to b do c done`
    For {
        var: Ident,
        from: Expr<V>,
        direction: ForDirection,
        to: Expr<V>,
        body: Box<Comp<V>>,
    },
    /// `for p in e do c done`
    ForEach {
        pat: Pat,
        source: ForSource<V>,
        body: Box<Comp<V>>,
    },
    /// `a .. b` or `a .. step .. b`
    Range(Range<V>),
    /// `try c with | p -> c …`
    TryWith {
        body: Box<Comp<V>>,
        clauses: Vec1<CompClause<V>>,
    },
    /// `try c finally e`
    TryFinally {
        body: Box<Comp<V>>,
        finally: Expr<V>,
    },
}

/// What a `for … in` loop runs over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForSource<V: Version> {
    Expr(Expr<V>),
    Range(Range<V>),
}

/// `from .. to`, or `from .. step .. to`. F# has a range only as a
/// computation expression's (or list's) statement and as a `for … in` loop's
/// source; it is not an expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Range<V: Version> {
    pub from: Expr<V>,
    pub step: Option<Expr<V>>,
    pub to: Expr<V>,
}

/// `| pat [when guard] -> body` in a computation expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompClause<V: Version> {
    pub pat: Pat,
    pub guard: Option<Expr<V>>,
    pub body: Comp<V>,
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
    pub pat: Pat,
    pub guard: Option<Expr<V>>,
    pub result: Expr<V>,
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
