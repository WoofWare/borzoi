//! An FCS-free census of `source_existence` over the pinned F# corpus: each
//! file walked alone as a one-file producer, under a certificate by spelling
//! and under `Unknown`, its verdict tallied by reason. It gates nothing: it
//! measures what the walk declines on real source, and why, so a
//! classifier that accounts for too few children (a decline real code
//! meets) shows up as a count with its witnesses.
//!
//! ```text
//! nix develop -c cargo test -p borzoi-sema --test all source_existence_census:: -- --ignored --nocapture
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use borzoi_oracle_harness::par_map::par_map;
use borzoi_sema::{MarkerRoutes, SourceExistence};

use crate::source_existence_diff::{Cell, ours};

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_symlink() {
            continue;
        }
        if path.is_dir() {
            collect(&path, out);
        } else if matches!(
            path.extension().and_then(|s| s.to_str()),
            Some("fs" | "fsi")
        ) {
            out.push(path);
        }
    }
}

/// The verdict's reason, with its leaf or index elided.
fn reason(r: &SourceExistence) -> String {
    match r {
        SourceExistence::Read(_) => "read".to_owned(),
        SourceExistence::Unread(why) => {
            let text = format!("{why:?}");
            // `Unreadable(3, TypeDefinition)` keeps its leaf; an index alone
            // is elided.
            match text.split_once('(') {
                Some(("Unreadable", rest)) => {
                    format!(
                        "Unreadable({}",
                        rest.split_once(", ").map_or(rest, |(_, l)| l)
                    )
                }
                Some((head, _)) => head.to_owned(),
                None => text,
            }
        }
    }
}

#[test]
#[ignore = "walks the pinned corpus; a measurement, not a gate"]
fn decline_census_over_the_corpus() {
    let Some(root) = std::env::var_os("BORZOI_CORPUS") else {
        eprintln!("BORZOI_CORPUS unset; run under `nix develop`");
        return;
    };
    let mut files = Vec::new();
    collect(Path::new(&root), &mut files);
    files.sort();
    let verdicts = par_map(files.len(), |i| {
        let path = &files[i];
        let Ok(text) = std::fs::read_to_string(path) else {
            return None;
        };
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let cell = Cell::new("census", &[(name.as_str(), text.as_str())]);
        let certified = reason(&ours(&cell, None).0);
        let unknown = reason(&ours(&cell, Some(&MarkerRoutes::Unknown)).0);
        Some((certified, unknown))
    });
    let mut census: BTreeMap<(String, String), Vec<&Path>> = BTreeMap::new();
    for (path, v) in files.iter().zip(&verdicts) {
        if let Some((c, u)) = v {
            census.entry((c.clone(), u.clone())).or_default().push(path);
        }
    }
    eprintln!("{} files", files.len());
    for ((c, u), paths) in &census {
        eprintln!("{:6}  certified: {c}; unknown: {u}", paths.len());
        if c != "read" && c != "Recovered" {
            for p in paths.iter().take(3) {
                eprintln!("          {}", p.display());
            }
        }
    }
}
