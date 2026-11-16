//! The friend declarations (`[<assembly: InternalsVisibleTo>]`,
//! `borzoi_assembly::friends`) of the SDK's reference packs, pinned exactly.
//!
//! A referencing project whose name one of these declarations may match sees
//! that assembly's internals, which the env grades as unread
//! (`borzoi_sema::Friendship`). So what the packs declare decides which
//! project names darken their whole assembly surface, and an entry the reader
//! stops certifying (an [`FriendEntry::Unread`]) darkens it for every project
//! whose name is untrusted. The manifest lists every entry per DLL, so either
//! movement fails with a line diff.
//!
//! The end-to-end grading against FCS is `borzoi-sema`'s
//! `friend_assembly_grid`, which compiles assemblies declaring friends in
//! each spelling the reader distinguishes.

use std::path::{Path, PathBuf};

use borzoi_assembly::{Ecma335Assembly, EcmaView, FriendEntry};
use borzoi_oracle_harness::manifest::{Manifest, UPDATE_ENV, check};

use crate::common::sdk_targeting_pack_dir;

fn entries_of(pack: &str) -> Vec<String> {
    let dir = sdk_targeting_pack_dir(pack);
    let mut dlls: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "dll"))
        .collect();
    dlls.sort();
    let mut out = Vec::new();
    for dll in &dlls {
        let bytes = std::fs::read(dll).unwrap_or_else(|e| panic!("read {dll:?}: {e}"));
        let view = Ecma335Assembly::parse(&bytes).unwrap_or_else(|e| panic!("parse {dll:?}: {e}"));
        let name = dll.file_name().expect("file name").to_string_lossy();
        for (i, entry) in view.friend_declarations().entries.iter().enumerate() {
            let rendered = match entry {
                FriendEntry::Named(n) => format!("named {n}"),
                FriendEntry::Unread(why) => format!("unread {why}"),
            };
            out.push(format!("{pack}/{name}#{i}\t{rendered}"));
        }
    }
    out
}

#[test]
fn reference_pack_friend_declarations_are_pinned() {
    let mut entries = entries_of("Microsoft.NETCore.App.Ref");
    entries.extend(entries_of("Microsoft.AspNetCore.App.Ref"));
    let manifest = Manifest::from_entries(entries).expect("manifest entries");
    check(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/manifests/friend_declarations.txt"),
        &manifest,
        &format!(
            "{UPDATE_ENV}=1 nix develop -c cargo test -p borzoi-assembly --test all \
             friend_declarations::"
        ),
    );
}
