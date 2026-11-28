//! The extension-member names a project file declares ([`ExtensionNames`]):
//! what the extension-scope gate (`crates/sema/src/infer/extension_scope.rs`)
//! asks before it lets an intrinsic method group stand for FCS's.
//!
//! An extension member joins only its own name's method group, so the gate
//! needs the names, not the mere presence of a source. A file declares an
//! extension, or something FCS could read as one, in exactly these ways:
//!
//! - a member of a `type … with` augmentation (an optional extension, or an
//!   intrinsic augmentation, which joins the group the same way): its name;
//! - a member under an attribute that may be `[<Extension>]` (a C#-style
//!   extension needs the marker on the method itself —
//!   `IsMethInfoPlainCSharpStyleExtensionMember`): its name;
//! - a type abbreviation under an attribute that may be `[<Extension>]` or
//!   `[<AutoOpen>]`: its target's extensions, which are not enumerated here,
//!   so every name (#831).
//!
//! An attribute anywhere else (on a module `let`, a type that is not an
//! abbreviation, a module, a union case, the assembly) makes nothing an
//! extension: a module value is no member, and a type's marker alone lists
//! no method (`infer_extension_scope_grid` holds FCS to both).
//!
//! The pass is **syntactic** over the whole tree: a declaration the
//! resolver's walk skips is still read. What it cannot read is a reason
//! ([`NamesUnknowable`]) for every name: a member it cannot name, or a
//! directive that brings in assemblies or files the project's references do
//! not include.
//!
//! A file the parser **recovered** from may have dropped text FCS's recovery
//! keeps ([`Damage`]). An extension member FCS recovers is still named by a
//! token of the file, so the names its damaged regions spell bound it, unless
//! a region holds an attribute list, a directive or an active-pattern member,
//! whose effect no single token's name bounds.

use crate::FcsRange as _;
use borzoi_assembly::op_name::compile_op_name;
use borzoi_cst::syntax::{
    AstNode, AttributeList, MemberDefn, Pat, SyntaxKind, SyntaxNode, TextRange, TypeDefn,
    TypeDefnRepr,
};

use super::{id_text, is_any_augmentation};
use crate::hash::HashSet;
use crate::recovery::SyntaxRecovery;

/// The extension-member names declared at or before some point of a project:
/// one file's (read off its syntax by `file_extension_names`), or the union of every file up to
/// one (what the Compile-order fold threads forward).
///
/// [`Self::Known`] is the claim that no member of any other name, of the
/// staticness asked, is one FCS could read as an extension. It ignores scope:
/// an extension in a module nobody opens still names its call, which only
/// declines more.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtensionNames {
    Known {
        /// Names that may join a value receiver's group.
        instance: HashSet<String>,
        /// Names that may join a type-qualified call's group.
        statics: HashSet<String>,
    },
    /// Some extension of an unknown name may be declared.
    Unknowable(NamesUnknowable),
}

/// Why a file's extension names are not known.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NamesUnknowable {
    /// A member of a `type … with` augmentation whose name the pass cannot
    /// read (an active-pattern head, an `inherit`).
    AugmentationMemberName,
    /// A member under an attribute that may be `[<Extension>]`, whose name the
    /// pass cannot read.
    AttributedMemberName,
    /// An attribute on a member or a type abbreviation with no name to ask
    /// about (`[<>]`).
    AttributeShape,
    /// A type abbreviation under an attribute that may be `[<Extension>]` or
    /// `[<AutoOpen>]`: its target's extension members are in scope wherever
    /// it is, and the target is not enumerated (#831).
    AttributedAbbreviation,
    /// The parser recovered from the file, and a damaged region holds an
    /// attribute list, a directive or an active-pattern member, or the
    /// reading kept no errors to bound the damage by (what
    /// `extension_names::damage` reads).
    Recovered,
    /// A `#r`, `#reference`, `#load`, `#I` or `#include` directive: an
    /// assembly or a file outside the project's references.
    HashReference,
}

impl Default for ExtensionNames {
    fn default() -> Self {
        ExtensionNames::Known {
            instance: HashSet::default(),
            statics: HashSet::default(),
        }
    }
}

impl ExtensionNames {
    /// Whether an extension member **named `name`** may be declared, for a
    /// call of the given shape (`is_static`: a type-qualified call).
    pub fn may_have(&self, name: &str, is_static: bool) -> bool {
        match self {
            ExtensionNames::Known { instance, statics } => {
                if is_static {
                    statics.contains(name)
                } else {
                    instance.contains(name)
                }
            }
            ExtensionNames::Unknowable(_) => true,
        }
    }

    /// Why no name is known absent, if that is so.
    pub fn unknowable(&self) -> Option<NamesUnknowable> {
        match self {
            ExtensionNames::Known { .. } => None,
            ExtensionNames::Unknowable(why) => Some(*why),
        }
    }

    /// Add `other`'s names to these. An unknowable side makes the union
    /// unknowable, keeping the first reason met.
    pub(crate) fn absorb(&mut self, other: &ExtensionNames) {
        match (&mut *self, other) {
            (ExtensionNames::Unknowable(_), _) => {}
            (_, ExtensionNames::Unknowable(why)) => *self = ExtensionNames::Unknowable(*why),
            (
                ExtensionNames::Known { instance, statics },
                ExtensionNames::Known {
                    instance: more_instance,
                    statics: more_statics,
                },
            ) => {
                instance.extend(more_instance.iter().cloned());
                statics.extend(more_statics.iter().cloned());
            }
        }
    }

    /// Add a member named `name` to the groups given, under every name F#
    /// compiles it to a method of: its own, and its property and event
    /// accessors' (`get_`, `set_`, `add_`, `remove_`), each of which a call can
    /// spell (`x.add_Changed(h)` binds a `[<CLIEvent>]` member's generated
    /// accessor). Which of them the member really generates is not this
    /// pass's business: a spelling it does not generate only declines more.
    fn add(&mut self, name: &str, instance_group: bool, static_group: bool) {
        if let ExtensionNames::Known { instance, statics } = self {
            for spelled in std::iter::once(name.to_string())
                .chain(ACCESSOR_PREFIXES.iter().map(|p| format!("{p}{name}")))
            {
                if instance_group {
                    instance.insert(spelled.clone());
                }
                if static_group {
                    statics.insert(spelled);
                }
            }
        }
    }

    fn fail(&mut self, why: NamesUnknowable) {
        if matches!(self, ExtensionNames::Known { .. }) {
            *self = ExtensionNames::Unknowable(why);
        }
    }
}

/// The prefixes of the accessor methods F# compiles a property or an event to.
const ACCESSOR_PREFIXES: [&str; 4] = ["get_", "set_", "add_", "remove_"];

/// Which attribute an attribute verdict is asked about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MarkerQuestion {
    /// May it be `[<Extension>]`?
    Extension,
    /// May it be `[<Extension>]` or `[<AutoOpen>]`?
    ExtensionOrAutoOpen,
}

/// The extension names the file rooted at `root` (an implementation or a
/// signature) declares. `recovered` is whether the parser recovered from it.
/// `may_be(range, question)` answers whether the attribute whose written name
/// spans `range` may be the attribute `question` names; it must answer yes
/// for an attribute it has no verdict on.
pub(crate) fn file_extension_names(
    root: &SyntaxNode,
    recovered: bool,
    may_be: &dyn Fn(TextRange, MarkerQuestion) -> bool,
) -> ExtensionNames {
    let mut names = ExtensionNames::default();
    if recovered {
        names.fail(NamesUnknowable::Recovered);
    }
    if root
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::HASH_DIRECTIVE_DECL)
        .any(|d| brings_in_references(&d))
    {
        names.fail(NamesUnknowable::HashReference);
    }
    for range in super::prescan::abbreviation_attributes(root) {
        match range {
            None => names.fail(NamesUnknowable::AttributeShape),
            Some(range) if may_be(range, MarkerQuestion::ExtensionOrAutoOpen) => {
                names.fail(NamesUnknowable::AttributedAbbreviation);
            }
            Some(_) => {}
        }
    }
    for defn in root.descendants_of::<TypeDefn>() {
        if !is_any_augmentation(&defn) {
            continue;
        }
        let mut members: Vec<MemberDefn> = defn.members().collect();
        if let Some(TypeDefnRepr::ObjectModel(om)) = defn.repr() {
            members.extend(om.members());
        }
        for m in &members {
            match augmentation_member(m) {
                AugmentationMember::Named(name, group) => {
                    names.add(&name, group.instance(), group.statics());
                }
                AugmentationMember::Unnamed => names.fail(NamesUnknowable::AugmentationMemberName),
                AugmentationMember::Contributes => {}
            }
        }
    }
    for list in root.descendants_of::<AttributeList>() {
        let Some(member) = list.syntax().ancestors().skip(1).find_map(MemberDefn::cast) else {
            continue;
        };
        let mut marked = false;
        for attr in list.attributes() {
            let toks: Vec<_> = attr
                .type_name()
                .map(|name| name.idents().collect())
                .unwrap_or_default();
            match (toks.first(), toks.last()) {
                (Some(first), Some(last)) => {
                    let range = TextRange::new(first.fcs_range().start(), last.fcs_range().end());
                    marked |= may_be(range, MarkerQuestion::Extension);
                }
                _ => names.fail(NamesUnknowable::AttributeShape),
            }
        }
        if !marked {
            continue;
        }
        match member_name(&member) {
            // Both groups: which a C#-style method joins is not this pass's
            // business.
            MemberName::Named(name) => names.add(&name, true, true),
            MemberName::Unnamed => names.fail(NamesUnknowable::AttributedMemberName),
            MemberName::NotAMember => {}
        }
    }
    names
}

/// What a file the parser recovered from may declare or open beyond what its
/// tree shows: text the parser mis-parsed or dropped, which FCS's recovery
/// may keep.
///
/// An extension member FCS recovers is named by an identifier (or an operator,
/// under its compiled name) written in the file, so [`Self::names`] spells
/// every token of the damaged regions
/// ([`SyntaxRecovery::damaged_regions`]) as a name. An attribute list or a
/// directive in a damaged region may bring names no token spells (an
/// attributed type abbreviation, a `#r`), and so may an active-pattern
/// member, whose name is spelled across tokens: any of them makes the names
/// unknowable. What lies outside the regions parsed intact, and the tree's
/// own pass reads it.
///
/// The names reach the whole file, not only what follows the damage: a
/// member of a recovered declaration is in scope before it wherever F# lets
/// a later declaration be seen earlier (a `rec` module, a `type … and …`
/// group, the members of one type).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Damage {
    /// What the damaged regions may declare.
    pub(crate) names: ExtensionNames,
    /// Whether a damaged region spells `open`: FCS may recover an `open` our
    /// parser dropped, bringing a namespace's extensions into scope.
    pub(crate) opens: bool,
}

/// The keywords without one of which text declares no member: every member
/// (an augmentation's, a C#-style method, an interface's) is introduced by
/// one of them, or sits in a type or object expression one of them opens.
const MEMBER_KEYWORDS: [&str; 10] = [
    "member",
    "override",
    "default",
    "abstract",
    "val",
    "static",
    "new",
    "type",
    "interface",
    "inherit",
];

/// The [`Damage`] of the file rooted at `root` under `recovery`, or `None`
/// when it parsed clean. A reading that kept no errors
/// ([`SyntaxRecovery::Unretained`]) shows no region, so it may declare and
/// open anything.
pub(crate) fn damage(root: &SyntaxNode, recovery: &SyntaxRecovery) -> Option<Damage> {
    if matches!(recovery, SyntaxRecovery::Unretained) {
        return Some(Damage {
            names: ExtensionNames::Unknowable(NamesUnknowable::Recovered),
            opens: true,
        });
    }
    let regions = recovery.damaged_regions(root)?;
    // The regions are sorted and disjoint, so one pass over the tokens with a
    // cursor into them is linear in the file.
    let mut next_region = 0;
    let tokens: Vec<_> = root
        .descendants_with_tokens()
        .filter_map(|el| el.into_token())
        .filter(|t| !t.kind().is_trivia())
        .filter(move |t| {
            let r = t.fcs_range();
            while next_region < regions.len() && regions[next_region].end() <= r.start() {
                next_region += 1;
            }
            regions
                .get(next_region)
                .is_some_and(|region| region.intersect(r).is_some())
        })
        .collect();
    let texts: Vec<&str> = tokens.iter().map(|t| t.text()).collect();
    let mut names = ExtensionNames::default();
    let mut declares_members = false;
    let mut active_pattern = false;
    let mut opens = false;
    for (i, (tok, &text)) in tokens.iter().zip(&texts).enumerate() {
        declares_members |= MEMBER_KEYWORDS.contains(&text);
        opens |= text == "open";
        // By spelling, not kind: in a damaged region the lexer's context may
        // give `#` or `[<` a kind of its own.
        if matches!(
            tok.kind(),
            SyntaxKind::LBRACK_LESS_TOK | SyntaxKind::HASH_TOK
        ) || text.starts_with('#')
            || text.starts_with("[<")
        {
            names.fail(NamesUnknowable::Recovered);
            break;
        }
        // An active pattern's banana clips, however the lexer split them:
        // `(|`, `|)`, or a `(` and a `|` apart.
        let next = texts.get(i + 1).copied().unwrap_or("");
        active_pattern |= text.contains("(|")
            || text.contains("|)")
            || (text.ends_with('(') && next.starts_with('|'))
            || (text.ends_with('|') && next.starts_with(')'));
        let unquoted = text
            .strip_prefix("``")
            .and_then(|t| t.strip_suffix("``"))
            .unwrap_or(text);
        names.add(unquoted, true, true);
        names.add(&compile_op_name(text), true, true);
        if text == ".." {
            // `( .. .. )` is two `..` tokens and compiles to `op_RangeStep`.
            names.add("op_RangeStep", true, true);
        }
        if let Some(operator) = parenthesised_operator(&texts[i..]) {
            names.add(&operator, true, true);
        }
    }
    if active_pattern && declares_members {
        names.fail(NamesUnknowable::Recovered);
    }
    if !declares_members && names.unknowable().is_none() {
        // Text with no keyword that opens a member or a type declares no
        // member at all, whatever names it spells.
        names = ExtensionNames::default();
    }
    Some(Damage { names, opens })
}

/// The compiled name of the operator `texts` opens with a parenthesised
/// spelling of (`(*)`, `( .. .. )`, `( >>= )`): its tokens joined, as F#
/// reads an operator's name. `None` when `texts` opens with none.
fn parenthesised_operator(texts: &[&str]) -> Option<String> {
    /// The most tokens an operator's spelling is joined from.
    const MAX_TOKENS: usize = 6;
    let mut joined = String::from(texts.first()?.strip_prefix('(')?);
    if let Some(inner) = joined.strip_suffix(')') {
        joined = inner.to_string();
    } else {
        let close = texts
            .iter()
            .take(MAX_TOKENS)
            .position(|t| t.ends_with(')'))?;
        for (k, t) in texts.iter().enumerate().take(close + 1).skip(1) {
            joined.push_str(if k == close {
                t.strip_suffix(')').unwrap_or(t)
            } else {
                t
            });
        }
    }
    let is_operator =
        !joined.is_empty() && joined.chars().all(|c| "!%&*+-./<=>?@^|~:$".contains(c));
    if !is_operator {
        return None;
    }
    Some(match joined.as_str() {
        // `(*)` is the multiplication operator, not a comment.
        "*" => "op_Multiply".to_string(),
        "...." => "op_RangeStep".to_string(),
        other => compile_op_name(other).into_owned(),
    })
}

/// Whether a hash directive brings in an assembly or a source file.
fn brings_in_references(directive: &SyntaxNode) -> bool {
    directive
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| t.kind() == SyntaxKind::IDENT_TOK)
        .is_some_and(|t| matches!(t.text(), "r" | "reference" | "load" | "I" | "include"))
}

/// The groups a `type … with` member's name joins.
#[derive(Debug, Clone, Copy)]
enum Group {
    Instance,
    Static,
    Both,
}

impl Group {
    fn instance(self) -> bool {
        matches!(self, Group::Instance | Group::Both)
    }

    fn statics(self) -> bool {
        matches!(self, Group::Static | Group::Both)
    }
}

enum AugmentationMember {
    Named(String, Group),
    /// A member that may join some group under a name the pass cannot read.
    Unnamed,
    /// A member that joins no named group of the augmented type (a
    /// constructor, a class `let`, a `do`, an interface implementation).
    Contributes,
}

/// What one member of a `type … with` augmentation adds to the name sets.
/// Over-approximate where the shape is uncertain: an unknown staticness joins
/// both groups, an `override` counts as an instance name, and a shape FCS
/// rejects in an augmentation still names its name.
fn augmentation_member(m: &MemberDefn) -> AugmentationMember {
    use borzoi_cst::syntax::{MemberLeading, MemberSigLeading};
    let group = match m {
        MemberDefn::Member(mm) if mm.leading_keyword() == MemberLeading::StaticMember => {
            Group::Static
        }
        MemberDefn::Member(_) => Group::Instance,
        MemberDefn::GetSetMember(g) if g.is_static() => Group::Static,
        MemberDefn::AutoProperty(a) if a.is_static() => Group::Static,
        MemberDefn::GetSetMember(_) | MemberDefn::AutoProperty(_) => Group::Instance,
        // A signature's member: `static` makes it a static, anything else
        // (`member`, `abstract`, `override`, `default`) an instance member.
        // A constructor joins no group ([`member_head`]).
        MemberDefn::MemberSig(ms) => match ms.leading_keyword() {
            MemberSigLeading::Static
            | MemberSigLeading::StaticMember
            | MemberSigLeading::StaticAbstract
            | MemberSigLeading::StaticAbstractMember => Group::Static,
            MemberSigLeading::Member
            | MemberSigLeading::Abstract
            | MemberSigLeading::AbstractMember
            | MemberSigLeading::Override
            | MemberSigLeading::Default
            | MemberSigLeading::New => Group::Instance,
        },
        MemberDefn::AbstractSlot(_)
        | MemberDefn::ValField(_)
        | MemberDefn::Inherit(_)
        | MemberDefn::Interface(_)
        | MemberDefn::LetBindings(_)
        | MemberDefn::Do(_) => Group::Both,
    };
    match member_head(m) {
        MemberHead::Named(name) => AugmentationMember::Named(name, group),
        MemberHead::Unnamed => AugmentationMember::Unnamed,
        // An `inherit` pulls the base's members in under names we cannot
        // enumerate.
        MemberHead::Inherit => AugmentationMember::Unnamed,
        // Class-local bindings are lexically private; an interface
        // implementation's members are reachable only through the interface,
        // never the receiver's own name group; a constructor joins none.
        MemberHead::Constructor | MemberHead::Local | MemberHead::Interface => {
            AugmentationMember::Contributes
        }
    }
}

/// What a member's head declares (#1100), read through one exhaustive match
/// over the member's shape. A name is read only where every child of the
/// head is accounted for ([`head_name`]): a head holding anything the match
/// does not name (an active pattern, a named-field group) is `Unnamed`,
/// never the name of some other child.
#[derive(Debug, Clone, PartialEq, Eq)]
enum MemberHead {
    /// The name the member joins its group under: an identifier, or an
    /// operator's compiled name (`op_PlusDot`), which is what `id_text`
    /// gives.
    Named(String),
    /// A member whose name the pass cannot read.
    Unnamed,
    /// `new (…) = …`.
    Constructor,
    /// `inherit Base(…)`.
    Inherit,
    /// A class `let` or `do`.
    Local,
    /// An interface implementation.
    Interface,
}

fn member_head(m: &MemberDefn) -> MemberHead {
    let token = |t: Option<borzoi_cst::syntax::SyntaxToken>| match t {
        Some(t) => MemberHead::Named(id_text(&t).to_string()),
        None => MemberHead::Unnamed,
    };
    match m {
        MemberDefn::Member(mm) => {
            if mm.leading_keyword() == borzoi_cst::syntax::MemberLeading::New {
                return MemberHead::Constructor;
            }
            // `this.Name args`, or a bare name with no receiver.
            match mm.binding().and_then(|b| b.pat()) {
                Some(Pat::LongIdent(l)) => head_name(&l),
                _ => MemberHead::Unnamed,
            }
        }
        // `x.Name with get … and set …`: the head pattern, not
        // `GetSetMember::name`, which is the long identifier alone (the
        // receiver, for `x.(|A|_|)`).
        MemberDefn::GetSetMember(g) => match g.head_pat() {
            Some(l) => head_name(&l),
            None => MemberHead::Unnamed,
        },
        MemberDefn::AutoProperty(a) => token(a.ident()),
        MemberDefn::AbstractSlot(s) => token(s.val_sig().and_then(|v| v.ident())),
        MemberDefn::ValField(v) => token(v.ident()),
        // `new: … -> T`, a signature's constructor, has no identifier.
        MemberDefn::MemberSig(ms)
            if ms.leading_keyword() == borzoi_cst::syntax::MemberSigLeading::New =>
        {
            MemberHead::Constructor
        }
        MemberDefn::MemberSig(ms) => token(ms.val_sig().and_then(|v| v.ident())),
        MemberDefn::Inherit(_) => MemberHead::Inherit,
        MemberDefn::LetBindings(_) | MemberDefn::Do(_) => MemberHead::Local,
        MemberDefn::Interface(_) => MemberHead::Interface,
    }
}

/// The name a member's head pattern (`this.Name args`, `x.Prop`) spells: the
/// last segment of its long identifier, when the pattern's children are
/// exactly that identifier, at most one explicit type-parameter list and
/// argument patterns, and the identifier's are names, dots and an operator's
/// parentheses, none of which changes the name. Any other child (an active
/// pattern's name, a named-field group, a child kind no view declares)
/// leaves the head unnamed.
///
/// Both nodes are read through their exhaustive views, matched without a
/// wildcard: a child kind a view comes to declare is a compile error here
/// until this function decides it, and one no view declares is unnamed.
#[deny(clippy::wildcard_enum_match_arm)]
fn head_name(l: &borzoi_cst::syntax::LongIdentPat) -> MemberHead {
    use borzoi_cst::syntax::{
        LongIdentChild, LongIdentPatChild, LongIdentPatToken, LongIdentToken,
    };
    let Ok(children) = l.view() else {
        return MemberHead::Unnamed;
    };
    let (mut heads, mut typar_lists) = (Vec::new(), 0);
    for child in children {
        match child {
            LongIdentPatChild::LongIdent(head) => heads.push(head),
            LongIdentPatChild::TyparDecls(_) => typar_lists += 1,
            // An argument pattern is no part of the name.
            LongIdentPatChild::NamedPat(_)
            | LongIdentPatChild::LongIdentPat(_)
            | LongIdentPatChild::WildcardPat(_)
            | LongIdentPatChild::ParenPat(_)
            | LongIdentPatChild::ConstPat(_)
            | LongIdentPatChild::NullPat(_)
            | LongIdentPatChild::TuplePat(_)
            | LongIdentPatChild::ArrayOrListPat(_)
            | LongIdentPatChild::RecordPat(_)
            | LongIdentPatChild::QuotePat(_)
            | LongIdentPatChild::OptionalValPat(_) => {}
            // A zero-width `ERROR` is the lex filter's layout virtual (before
            // an adjacent argument, `this.M(x)`) or a recovery placeholder:
            // it spells nothing, and the head identifier stays the only name.
            // One with text is debris the parser could not place.
            LongIdentPatChild::Token(LongIdentPatToken::Error, t) => {
                if !t.text().is_empty() {
                    return MemberHead::Unnamed;
                }
            }
            LongIdentPatChild::ActivePatName(_) | LongIdentPatChild::NamePatPairs(_) => {
                return MemberHead::Unnamed;
            }
        }
    }
    let ([head], 0 | 1) = (heads.as_slice(), typar_lists) else {
        return MemberHead::Unnamed;
    };
    let Ok(segments) = head.view() else {
        return MemberHead::Unnamed;
    };
    for segment in segments {
        match segment {
            LongIdentChild::Token(
                LongIdentToken::Ident
                | LongIdentToken::Dot
                | LongIdentToken::New
                | LongIdentToken::LParen
                | LongIdentToken::RParen,
                _,
            ) => {}
            LongIdentChild::ActivePatName(_) => return MemberHead::Unnamed,
        }
    }
    match head.idents().last() {
        Some(t) => MemberHead::Named(id_text(&t).to_string()),
        None => MemberHead::Unnamed,
    }
}

enum MemberName {
    Named(String),
    Unnamed,
    /// The attribute sits on a class `let`, a `do`, an `inherit` or an
    /// interface implementation's header: no method of a group.
    NotAMember,
}

/// The name of the member an attribute decorates.
fn member_name(m: &MemberDefn) -> MemberName {
    match member_head(m) {
        MemberHead::Named(name) => MemberName::Named(name),
        MemberHead::Unnamed => MemberName::Unnamed,
        // A constructor is no method of a named group.
        MemberHead::Constructor
        | MemberHead::Inherit
        | MemberHead::Local
        | MemberHead::Interface => MemberName::NotAMember,
    }
}

#[cfg(test)]
mod tests {
    use super::{ExtensionNames, MarkerQuestion, NamesUnknowable, file_extension_names};
    use borzoi_cst::parser::parse;

    /// The names `src` declares when every attribute may be the marker
    /// (`marked`) or none may.
    fn names(src: &str, marked: bool) -> ExtensionNames {
        let parsed = parse(src);
        assert!(parsed.errors.is_empty(), "{src}: {:?}", parsed.errors);
        file_extension_names(&parsed.root, false, &|_, _: MarkerQuestion| marked)
    }

    fn known(n: &ExtensionNames) -> (Vec<String>, Vec<String>) {
        match n {
            ExtensionNames::Known { instance, statics } => {
                let mut i: Vec<String> = instance.iter().cloned().collect();
                let mut s: Vec<String> = statics.iter().cloned().collect();
                i.sort();
                s.sort();
                (i, s)
            }
            ExtensionNames::Unknowable(why) => panic!("unknowable: {why:?}"),
        }
    }

    /// A signature's augmentation puts `with` directly on the definition,
    /// with no representation; its members are extensions all the same.
    #[test]
    fn a_signature_augmentation_names_its_members() {
        let parsed = borzoi_cst::parser::parse_sig(
            "namespace N\ntype System.Collections.Hashtable with\n    member ContainsValue: key: int -> int64\n",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let n = file_extension_names(&parsed.root, false, &|_, _: MarkerQuestion| false);
        assert!(n.may_have("ContainsValue", false), "{n:?}");
    }

    /// A signature's members join the group their keyword names, and its
    /// constructor joins none: a `new` names nothing, rather than making the
    /// names unknowable.
    #[test]
    fn a_signature_augmentation_names_each_member_in_its_group() {
        let parsed = borzoi_cst::parser::parse_sig(
            "namespace N
type T
type T with
    new: unit -> T
    member I: int -> int
    \
             static member S: int -> int
",
        );
        assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
        let n = file_extension_names(&parsed.root, false, &|_, _: MarkerQuestion| false);
        let (instance, statics) = known(&n);
        assert!(instance.contains(&"I".to_owned()), "{n:?}");
        assert!(!instance.contains(&"S".to_owned()), "{n:?}");
        assert!(statics.contains(&"S".to_owned()), "{n:?}");
        assert!(!statics.contains(&"I".to_owned()), "{n:?}");
    }

    #[test]
    fn augmentation_members_name_their_groups() {
        let n = names(
            "module M\ntype System.String with\n    member s.A = 1\n    static member B () = 2\n    member s.C with get () = 3\n",
            false,
        );
        let spellings = |names: &[&str]| {
            let mut all: Vec<String> = names
                .iter()
                .flat_map(|n| {
                    std::iter::once(n.to_string()).chain(
                        super::ACCESSOR_PREFIXES
                            .iter()
                            .map(move |p| format!("{p}{n}")),
                    )
                })
                .collect();
            all.sort();
            all
        };
        assert_eq!(known(&n), (spellings(&["A", "C"]), spellings(&["B"])));
    }

    /// A member head is named through its exhaustive views: type parameters,
    /// argument patterns, the lex filter's zero-width layout virtual before
    /// an adjacent argument (`this.N(x)`), an operator's parentheses and a
    /// quoted name all leave the name readable.
    #[test]
    fn member_heads_are_named_through_their_views() {
        let n = names(
            "module M\ntype System.String with\n    member s.G<'a> (x: 'a) = 1\n    member this.N(x) = x\n    member s.``Q R`` = 1\n    static member (+) (a: string, b: int) = 0\n",
            false,
        );
        let (instance, statics) = known(&n);
        for name in ["G", "N", "Q R"] {
            assert!(instance.contains(&name.to_owned()), "{name}: {n:?}");
        }
        assert!(statics.contains(&"op_Addition".to_owned()), "{n:?}");
    }

    #[test]
    fn a_marked_member_names_both_groups_and_its_accessors() {
        let src = "module M\ntype E =\n    [<Ext>]\n    static member Shout(s: string) = s\n";
        let mut expected: Vec<String> = std::iter::once("Shout".to_string())
            .chain(super::ACCESSOR_PREFIXES.iter().map(|p| format!("{p}Shout")))
            .collect();
        expected.sort();
        assert_eq!(known(&names(src, true)), (expected.clone(), expected));
        assert_eq!(known(&names(src, false)), (vec![], vec![]));
    }

    #[test]
    fn a_marker_off_a_member_names_nothing() {
        for src in [
            "module M\n[<Ext>]\nlet Shout (s: string) = s\n",
            "module M\n[<Ext>]\ntype E =\n    static member Shout(s: string) = s\n",
            "[<Ext>]\nmodule M\nlet x = 1\n",
            "module M\ntype U =\n    | [<Ext>] A\n",
        ] {
            assert_eq!(known(&names(src, true)), (vec![], vec![]), "{src}");
        }
    }

    #[test]
    fn what_cannot_be_named_names_everything() {
        for (src, why) in [
            (
                "module M\ntype T() =\n    member _.X = 1\ntype T with\n    member _.(|Big|_|) x = None\n",
                NamesUnknowable::AugmentationMemberName,
            ),
            // A get/set property's active-pattern head: its long identifier
            // is the receiver (#1100).
            (
                "module M\ntype T() =\n    member _.X = 1\ntype T with\n    member x.(|Big|_|) with get () = None\n",
                NamesUnknowable::AugmentationMemberName,
            ),
            (
                "module M\n[<AutoOpen>]\ntype A = System.String\n",
                NamesUnknowable::AttributedAbbreviation,
            ),
            (
                "module M\n#r \"x.dll\"\nlet x = 1\n",
                NamesUnknowable::HashReference,
            ),
            (
                "module M\n#load \"x.fs\"\nlet x = 1\n",
                NamesUnknowable::HashReference,
            ),
            (
                "module M\n#I \"dir\"\nlet x = 1\n",
                NamesUnknowable::HashReference,
            ),
        ] {
            let parsed = parse(src);
            let n = file_extension_names(&parsed.root, false, &|_, _| true);
            assert_eq!(n.unknowable(), Some(why), "{src}");
        }
        let n = names("module M\n#nowarn \"40\"\nlet x = 1\n", true);
        assert_eq!(known(&n), (vec![], vec![]));
        let parsed = parse("module M\nlet x = 1\n");
        assert_eq!(
            file_extension_names(&parsed.root, true, &|_, _| true).unknowable(),
            Some(NamesUnknowable::Recovered)
        );
    }

    #[test]
    fn absorbing_unions_and_keeps_the_first_reason() {
        let mut a = names(
            "module M\ntype System.String with\n    member s.A = 1\n",
            false,
        );
        a.absorb(&names(
            "module N\ntype System.String with\n    member s.B = 1\n",
            false,
        ));
        assert!(a.may_have("A", false) && a.may_have("B", false), "{a:?}");
        assert!(!a.may_have("C", false) && !a.may_have("A", true), "{a:?}");
        a.absorb(&ExtensionNames::Unknowable(NamesUnknowable::Recovered));
        a.absorb(&ExtensionNames::Unknowable(NamesUnknowable::HashReference));
        assert_eq!(a.unknowable(), Some(NamesUnknowable::Recovered));
        assert!(a.may_have("Anything", true));
    }

    /// The damage of `src`, parsed with its own recovery reading.
    fn damage_of(src: &str) -> Option<super::Damage> {
        let parsed = parse(src);
        let recovery = crate::recovery::SyntaxRecovery::of(&parsed);
        super::damage(&parsed.root, &recovery)
    }

    #[test]
    fn a_damaged_region_declares_what_it_spells() {
        assert_eq!(damage_of("module M\nlet a = 1\n"), None, "a clean file");
        let src = "module M\nlet early = 1\ntype System.String with\n    member s.Shout() = (1 +\nlet later = 2\n";
        let d = damage_of(src).expect("damaged");
        assert!(d.names.may_have("Shout", false), "{d:?}");
        assert!(d.names.may_have("get_Shout", true), "{d:?}");
        assert!(d.names.may_have("op_Addition", false), "{d:?}");
        assert!(
            !d.names.may_have("early", false),
            "an intact declaration: {d:?}"
        );
        assert!(!d.names.may_have("Substring", false), "{d:?}");
        // An intact declaration with an attribute after the damage is the
        // tree's to read; it makes nothing unknowable here.
        let after = "module M\nlet broken = 1 )\nlet ok = 1\n[<System.Obsolete(\"x\")>]\nlet attributed = 2\n";
        let d = damage_of(after).expect("damaged");
        assert_eq!(d.names.unknowable(), None, "{d:?}");
        // Damaged text with no keyword that opens a member declares none.
        assert!(!d.names.may_have("broken", false), "{d:?}");
    }

    #[test]
    fn a_damaged_region_with_an_attribute_or_a_directive_declares_anything() {
        for src in [
            "module M\nlet early = 1\n[<AutoOpen>]\ntype A = Lib.StrExts (\n",
            // A directive in an intact declaration is the tree's to report
            // (`HashReference`); one in damaged text is this bound's.
            "module M\nlet early = 1\nlet broken = (1 +\n#r \"x.dll\"\n",
        ] {
            let d = damage_of(src).expect("damaged");
            assert_eq!(
                d.names.unknowable(),
                Some(NamesUnknowable::Recovered),
                "{src:?}: {d:?}"
            );
        }
    }

    #[test]
    fn a_damaged_operator_member_declares_its_compiled_name() {
        let src = "module M\ntype System.String with\n    = static member (*) (a: string, b: int) = 0L\n    static member ( .. .. ) (a: string, b: int, c: int) = 0L\n    static member ( >>= ) (a: string, b: int) = 0L\nlet mid = 1\n";
        let d = damage_of(src).expect("damaged");
        for name in ["op_Multiply", "op_RangeStep", "op_GreaterGreaterEquals"] {
            assert!(d.names.may_have(name, true), "{name}: {d:?}");
        }
    }

    #[test]
    fn a_damaged_active_pattern_member_declares_anything() {
        for member in [
            "member s.(|Big|_|) (x: int)",
            "member s.( |Big|_| ) (x: int)",
        ] {
            let src = format!(
                "module M\ntype System.String with\n    = {member} = Some 0L\nlet mid = 1\n"
            );
            let d = damage_of(&src).expect("damaged");
            assert_eq!(
                d.names.unknowable(),
                Some(NamesUnknowable::Recovered),
                "{src:?}: {d:?}"
            );
        }
    }

    #[test]
    fn a_damaged_open_is_one_fcs_may_keep() {
        let d = damage_of("module M\nopen System. .Linq\nlet a = 1\n").expect("damaged");
        assert!(d.opens, "{d:?}");
        let d = damage_of("module M\nopen System.Linq\nlet a = 1\nlet b = 2\nlet broken = (1 +\n")
            .expect("damaged");
        assert!(!d.opens, "an intact open is the resolver's: {d:?}");
    }
}
