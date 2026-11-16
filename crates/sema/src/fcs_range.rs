//! The range a token stands for in what sema and the LSP report.
//!
//! Every range sema records or looks up is FCS's: a definition's, a use's, a
//! decline's. FCS ranges a name over its token, except the glued `(*)`, which
//! the tree spells as three tokens and FCS names over all three
//! ([`borzoi_cst::syntax::fcs_ident_range`]). So a token's range is read through
//! [`FcsRange::fcs_range`], never `text_range`, which the crate's
//! `clippy.toml` bans (and the LSP's). Were one site to read the raw range, a
//! glued `(*)` would be keyed apart at it: a binder its uses could not find, a
//! doc comment hover could not pair.

use borzoi_cst::syntax::{SyntaxToken, TextRange, fcs_ident_range};

/// A token's range as FCS reports it: the range every definition, use and
/// decline sema records is keyed by. It is the token's own range except for
/// the `*` of a glued `(*)` ([`fcs_ident_range`]); `clippy.toml` bans
/// `text_range` in sema and the LSP so that no site keys that `*` apart.
pub trait FcsRange {
    /// The range FCS gives this token: its own, except the `*` of a glued
    /// `(*)`, which spans the parentheses.
    fn fcs_range(&self) -> TextRange;
}

impl FcsRange for SyntaxToken {
    fn fcs_range(&self) -> TextRange {
        fcs_ident_range(self)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    /// Clippy reads only the nearest `clippy.toml`, so the crate's replaces
    /// the workspace's: it must carry every one of the workspace's settings,
    /// or this crate silently loses a ban every other crate keeps.
    #[test]
    fn clippy_config_repeats_the_workspace_bans() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let workspace = std::fs::read_to_string(manifest.join("../../clippy.toml")).unwrap();
        let crate_config = std::fs::read_to_string(manifest.join("clippy.toml")).unwrap();
        let crate_lines: Vec<&str> = crate_config.lines().collect();
        let settings: Vec<&str> = workspace
            .lines()
            .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
            .collect();
        assert!(
            settings
                .iter()
                .any(|line| line.contains("std::process::Command::spawn")),
            "the workspace's clippy.toml no longer holds the spawn ban: {workspace}"
        );
        for line in settings {
            assert!(
                crate_lines.contains(&line),
                "crates/sema/clippy.toml is missing the workspace's {line:?}"
            );
        }
    }
}
