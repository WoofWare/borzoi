//! `textDocument/completion` — member (`recv.`) completion.
//!
//! Stage 3.3b: when the cursor sits **after a dot** in a member access
//! (`s.`, mid-`s.Le`, `"hi".Le`), offer the **receiver type's public instance
//! members** — fields, non-indexer readable properties, *and* methods. A
//! completion list is a set of genuinely-callable candidates, not a type
//! assertion, so methods belong even though inference (Stage 3.3a) only *types*
//! data members. The receiver type comes from inference: the receiver's type
//! *at the access*, where FCS looks the member up
//! ([`InferredFile::receiver_type_at`]); its [`borzoi_sema::TyKind::Named`] head
//! is resolved through the project's [`AssemblyEnv`] to the entity's member list.
//!
//! **Soundness (D5: silence over noise).** A completion list requires a
//! **ground** receiver type known at the access. An open / deferred receiver (an
//! unannotated parameter nothing fixed before the dot, a receiver inference
//! could not type) offers **nothing** — never a guess, and never the members of
//! the type a later use gives it (`(x.Le, g x)` is FS0072 in FCS, #662's D4).
//! Only *public instance* members are offered; static members (`Empty`)
//! need a type-qualified path, not a value receiver, so they are excluded, and
//! a `private get` / write-only property is excluded (unreadable). No base-class
//! walk yet — exact-entity members only (as Stage 3.3a).
//!
//! **Parse-shape coverage** (probed against the CST — see
//! `docs/sema-phase3-impl-plan.md` §3.3b). The two *partial-member* shapes parse
//! cleanly and are fully covered: `s.Le` is a `LONG_IDENT_EXPR`
//! (`[IDENT s, DOT, IDENT Le]`) and `"hi".Le` a `DOT_GET_EXPR` (receiver
//! expression + member path). The *trailing-dot* `s.` also recovers as a
//! `LONG_IDENT_EXPR` (`[IDENT s, DOT]`) whose receiver token is still present;
//! inference walks the declaration holding it for the receiver types up to it
//! when it is the file's first recovery. A later dot (`s.Length.`) has its own
//! receiver (`s.Length`), recorded as the head's is. The literal trailing-dot `"hi".`
//! is **scoped out**: under error recovery its `DOT_GET_EXPR` collapses — the
//! receiver becomes a bare sibling `CONST_EXPR` and the `DOT` an orphan — so no
//! member-access node survives to anchor the receiver (a parser-side follow-up,
//! not hacked here).

use crate::uri::UriExt as _;
use borzoi_cst::syntax::TextSize;
use borzoi_cst::syntax::{
    AstNode, DotGetExpr, Expr, ImplFile, LongIdentExpr, ModuleOrNamespace, NestedModuleDecl,
    SyntaxKind, SyntaxNode, SyntaxToken,
};
use borzoi_sema::{
    AssemblyEnv, InferredFile, InferredProject, Resolution, ResolvedFile, Ty, TyKind,
};
use lsp_types::{CompletionItem, CompletionParams, CompletionResponse, Position};

use crate::inbox::{Superseded, Watch, never_superseded};
use crate::paths::{lexically_normalize, paths_equal};
use crate::position::position_to_offset;
use crate::server::State;

/// Run the completion handler. Returns member candidates for a `recv.`
/// member-access position whose receiver has a **ground** inferred type resolving
/// to a referenced-assembly entity; `None` for every other position (D5: silence
/// over noise). Project-only in v1 — member completion needs the project's
/// `AssemblyEnv` to enumerate members, which an orphan buffer has no way to build.
pub fn handle(state: &mut State, params: CompletionParams) -> Option<CompletionResponse> {
    never_superseded(handle_watched(state, params, &Watch::unwatched()))
}

/// [`handle`], stopping at a checkpoint once `watch` sees a notification
/// ([`crate::inbox`]).
pub fn handle_watched(
    state: &mut State,
    params: CompletionParams,
    watch: &Watch,
) -> Result<Option<CompletionResponse>, Superseded> {
    let pos = params.text_document_position.position;
    let uri = params.text_document_position.text_document.uri.clone();
    let Some(text) = state.docs.get(&uri).cloned() else {
        return Ok(None);
    };
    let Some(names) = member_candidates(state, &uri, &text, pos, watch)? else {
        return Ok(None);
    };
    if names.is_empty() {
        return Ok(None);
    }
    // No `kind` icon is claimed: the candidate set mixes fields, properties, and
    // methods, and we do not carry the per-member kind here (a later enrichment —
    // `member_kind_for` — could set it). A wrong icon is worse than none.
    let items = names
        .into_iter()
        .map(|name| CompletionItem {
            label: name,
            ..CompletionItem::default()
        })
        .collect();
    Ok(Some(CompletionResponse::Array(items)))
}

/// The public instance member names offered at `pos`, or `None` when the position
/// is not a completable `recv.` member access against a ground receiver type in an
/// evaluated project.
fn member_candidates(
    state: &mut State,
    uri: &lsp_types::Uri,
    text: &str,
    pos: Position,
    watch: &Watch,
) -> Result<Option<Vec<String>>, Superseded> {
    let Ok(path) = uri.to_file_path() else {
        return Ok(None);
    };
    let Some(project) = state.workspace.owning_project_watched(&path, watch)? else {
        return Ok(None);
    };
    watch.check()?;
    let State {
        semantic,
        workspace,
        docs,
        ..
    } = state;
    // Size the fold to this file's Compile index *first*, so we fold only the
    // prefix up to it: F# is order-sensitive, so the receiver's type and every
    // in-scope member candidate are declared at an index `<= file_idx` — the
    // suffix fold can't add a candidate this file can see.
    let Some(parses) = semantic.parses_for_project_watched(&project, workspace, docs, watch)?
    else {
        return Ok(None);
    };
    let parses = parses.clone();
    let Some(file_idx) = parses
        .paths
        .iter()
        .position(|p| paths_equal(&lexically_normalize(p), &lexically_normalize(&path)))
    else {
        return Ok(None);
    };
    // Completion needs the file's implementation tree; a `.fsi` Compile slot
    // is inert in Stage 1, so decline (no member completion on signatures).
    let Some(impl_file) = parses.files[file_idx].file.as_impl() else {
        return Ok(None);
    };

    let byte = position_to_offset(text, pos);
    // Find the receiver expression whose member is being completed at `byte`.
    let Some(access) = receiver_at(impl_file, byte) else {
        return Ok(None);
    };

    // Inference gives the receiver's ground type. It folds the prefix in
    // Compile order (a receiver may be an earlier file's value), against the
    // env the fold resolved against.
    let Some((resolved, env, inferred_project)) =
        semantic.inferred_prefix_watched(&project, file_idx, workspace, docs, watch)?
    else {
        return Ok(None);
    };
    let file = resolved.file(file_idx);
    let Some(inferred) = inferred_project.file(file_idx) else {
        return Ok(None);
    };

    // A ground `TyKind::Named` receiver resolves to an entity; anything else (open,
    // an array / tuple / function head, a generic named type) offers nothing.
    Ok(receiver_type(&access, file, inferred, &inferred_project)
        .and_then(|recv_ty| members_of(&env, &recv_ty))
        .map(|names| names.into_iter().map(str::to_string).collect()))
}

/// The member access being completed at `byte` — the dot after its receiver,
/// in `recv.<member-being-typed>` — or `None` for every other position (not
/// a member access, or the scoped-out literal trailing-dot). See the module
/// docs for the shape survey.
fn receiver_at(file: &ImplFile, byte: usize) -> Option<Access> {
    let byte = TextSize::try_from(byte).ok()?;
    let root = file.syntax();
    // The token just left of the cursor anchors the position: completion fires
    // when it is the dot itself (`s.`) or a member ident following a dot
    // (`s.Le`). `token_at_offset` yields both sides at a boundary; prefer the one
    // that ends *at* the cursor (the token we are completing after).
    //
    // A **trivia** left token means the cursor is not adjacent to any code. The
    // only completable position reached *through* trivia is a trailing dot
    // (`s. |` — the dot is still the member-access edit point); an ident behind
    // the trivia (`let n = s.Length |`, or the next line) is a **completed**
    // access the cursor has left, and offering the receiver's members there is
    // noise, not help (a codex round-3 finding) — decline (silence over noise).
    let raw_left = raw_token_left_of(root, byte)?;
    let left = if raw_left.kind().is_trivia() {
        let tok = prev_non_trivia(&raw_left)?;
        if tok.kind() != SyntaxKind::DOT_TOK {
            return None;
        }
        tok
    } else {
        raw_left
    };
    match left.kind() {
        // Trailing dot (`s.`) or partial member (`s.Le`): the anchoring dot is
        // `left` itself, or the dot immediately preceding the member ident.
        SyntaxKind::DOT_TOK => access_at_dot(left),
        SyntaxKind::IDENT_TOK => {
            // The member ident being typed — its immediately-preceding non-trivia
            // sibling in the path must be a dot, else this is a bare name (not a
            // member access) and completion does not fire here.
            let dot = prev_non_trivia(&left)?;
            if dot.kind() != SyntaxKind::DOT_TOK {
                return None;
            }
            access_at_dot(dot)
        }
        _ => None,
    }
}

/// A member access being completed: the dot after its receiver, which is
/// what inference keys the receiver's type at the access by
/// ([`InferredFile::receiver_type_at`]).
struct Access {
    dot: SyntaxToken,
    /// The receiver's binder token, when the receiver is a plain name: the
    /// head of a `LONG_IDENT_EXPR` before its first dot (`s` in `s.Le`), or a
    /// `DOT_GET_EXPR`'s receiver once transparent parentheses are peeled
    /// (`(s).Le`). Read only where nothing is recorded at the dot
    /// ([`receiver_type`]).
    binder: Option<SyntaxToken>,
}

/// The member access anchored by a member-access `dot` token. The dot always
/// lives inside a `LONG_IDENT`, whose parent is the access: a
/// `LONG_IDENT_EXPR` (`s.Le`, `s.`, `s.Length.`) or a `DOT_GET_EXPR`
/// (`"hi".Le`, `"hi".Length.To`). Any dot of the path anchors one; the
/// receiver before a later dot (`s.Length`) is as much the access's as the
/// head is, and inference records each.
///
/// `None` if the dot is not inside either shape (or the shape is malformed).
fn access_at_dot(dot: SyntaxToken) -> Option<Access> {
    let long_ident = dot.parent()?;
    if long_ident.kind() != SyntaxKind::LONG_IDENT {
        return None;
    }
    let first_dot = long_ident
        .children_with_tokens()
        .filter_map(|el| el.into_token())
        .find(|t| t.kind() == SyntaxKind::DOT_TOK)?;
    let path_parent = long_ident.parent()?;
    let binder = match path_parent.kind() {
        SyntaxKind::LONG_IDENT_EXPR => {
            let long_ident_expr = LongIdentExpr::cast(path_parent)?;
            (first_dot == dot)
                .then(|| {
                    long_ident_expr
                        .long_ident()?
                        .syntax()
                        .children_with_tokens()
                        .filter_map(|el| el.into_token())
                        .find(|t| t.kind() == SyntaxKind::IDENT_TOK)
                })
                .flatten()
        }
        SyntaxKind::DOT_GET_EXPR => {
            let dot_get = DotGetExpr::cast(path_parent)?;
            if first_dot == dot {
                binder_of_expr(dot_get.expr()?)
            } else {
                None
            }
        }
        _ => return None,
    };
    Some(Access { dot, binder })
}

/// The binder token of a `DOT_GET_EXPR` receiver *expression* that is a plain
/// name once transparent **parentheses** are peeled (`(s).Le`), or `None`.
fn binder_of_expr(mut expr: Expr) -> Option<SyntaxToken> {
    loop {
        match expr {
            Expr::Paren(p) => expr = p.inner()?,
            Expr::Ident(ident) => return ident.ident(),
            _ => return None,
        }
    }
}

/// The receiver's type where the member is looked up, or `None` (D5
/// silence): never the type a later use gives the receiver (#662's D4).
///
/// - What inference recorded at the access: the receiver's type when FCS
///   reaches the dot ([`InferredFile::receiver_type_at`]).
/// - Where it recorded nothing — an access inference does not walk, such as
///   one in a member body — and the receiver is a plain name, the binder's
///   type, but only where it was published before the access's declaration
///   group began ([`group_start`]): an earlier file's value, or an earlier
///   declaration's binder, whose type FCS had fixed before it began checking
///   the access's group. A binder of the same group (a `let rec` sibling, a
///   `module rec`'s other declarations) has a published type that is its
///   type at the group's end, which FCS may not know at the access (FS0072).
fn receiver_type(
    access: &Access,
    file: &ResolvedFile,
    inferred: &InferredFile,
    project: &InferredProject,
) -> Option<Ty> {
    if let Some(ty) = inferred.receiver_type_at(access.dot.text_range()) {
        return Some(*ty);
    }
    let head = access.binder.as_ref()?;
    let res = file.resolution_at(head.text_range())?;
    match (file.resolved_def_id(res), res) {
        (Some(def), _) if file.def(def).range.end() <= group_start(head) => {
            inferred.def_type(def).copied()
        }
        (Some(_), _) => None,
        // An earlier file's top-level value: the type that file published.
        (None, Resolution::Item(id)) if !file.owns_item(id) => project.item_type(id).ok().copied(),
        (None, _) => None,
    }
}

/// Where the declaration group holding `token` begins: the outermost
/// recursive module or namespace around it (`module rec`, `namespace rec`,
/// whose declarations FCS checks as one group), else the module-level
/// declaration holding it (a `let rec … and …` or `type … and …` is one).
fn group_start(token: &SyntaxToken) -> TextSize {
    let mut declaration = None;
    let mut recursive = None;
    for node in token.parent_ancestors() {
        let holder = node.parent().map(|p| p.kind());
        if declaration.is_none()
            && matches!(
                holder,
                Some(SyntaxKind::MODULE_OR_NAMESPACE | SyntaxKind::NESTED_MODULE_DECL)
            )
        {
            declaration = Some(node.text_range().start());
        }
        let is_rec = ModuleOrNamespace::cast(node.clone()).is_some_and(|m| m.is_rec())
            || NestedModuleDecl::cast(node.clone()).is_some_and(|m| m.is_rec());
        if is_rec {
            recursive = Some(node.text_range().start());
        }
    }
    recursive.or(declaration).unwrap_or_default()
}

/// The public instance member names of a ground `TyKind::Named` receiver, resolved
/// through `env`. `None` (offer nothing) for a non-`Named` head, a generic /
/// nested named type we cannot resolve to an arity-0 entity, or an entity absent
/// from the env. Duplicates (overloaded method names) are already deduplicated by
/// [`AssemblyEnv::public_instance_member_names`].
fn members_of<'e>(env: &'e AssemblyEnv, ty: &Ty) -> Option<Vec<&'e str>> {
    let TyKind::Named { path, args } = ty.kind(env) else {
        return None;
    };
    // Arity 0 — a non-generic receiver, exactly Stage 3.3a's `HasMember` lookup.
    // A generic application's members are instantiation-dependent and the lookup
    // is not, so it offers nothing rather than a wrongly-typed member list.
    if !args.is_empty() {
        return None;
    }
    let path: Vec<String> = path.segments(env).into_iter().map(str::to_owned).collect();
    let (type_name, namespace) = path.split_last()?;
    let handle = env.lookup_type(namespace, type_name, 0)?;
    Some(env.public_instance_member_names(handle))
}

/// The **raw** token ending at or containing `byte`, preferring the one whose
/// range ends exactly at the cursor (the token we completed after). May be
/// trivia — the caller ([`receiver_at`]) decides whether trivia is skippable
/// (only toward a trailing dot). `None` at the very start of the file.
fn raw_token_left_of(root: &SyntaxNode, byte: TextSize) -> Option<SyntaxToken> {
    // `token_at_offset` returns up to two tokens at a boundary. Take the token to
    // the *left* (ending at `byte`); if the cursor is inside a token, that token.
    match root.token_at_offset(byte) {
        borzoi_cst::syntax::TokenAtOffset::None => None,
        borzoi_cst::syntax::TokenAtOffset::Single(t) => Some(t),
        borzoi_cst::syntax::TokenAtOffset::Between(left, _right) => Some(left),
    }
}

/// The nearest preceding non-trivia token in the whole tree, if any.
fn prev_non_trivia(tok: &SyntaxToken) -> Option<SyntaxToken> {
    let mut cur = tok.prev_token();
    while let Some(t) = cur {
        if !t.kind().is_trivia() {
            return Some(t);
        }
        cur = t.prev_token();
    }
    None
}
