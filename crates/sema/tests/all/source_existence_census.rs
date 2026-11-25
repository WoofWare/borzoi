//! An FCS-free census of `source_existence` over the pinned F# corpus: each
//! file walked alone as a one-file producer, its verdict tallied by reason,
//! and the most any read file charged the budget. It gates nothing: it
//! measures what the walk declines on real source, and why, which is the
//! skeleton's decline cost and the worklist of the widenings that follow it.
//!
//! ```text
//! nix develop -c cargo test -p borzoi-sema --test all source_existence_census:: -- --ignored --nocapture
//! ```

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use borzoi_oracle_harness::par_map::par_map;
use borzoi_sema::{ExistenceUnread, SourceExistence};

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

/// The verdict's reason, with its file index elided.
fn reason(r: &SourceExistence) -> String {
    match r {
        SourceExistence::Read(_) => "read".to_owned(),
        SourceExistence::Unread(why) => match why {
            ExistenceUnread::Declined(_, form) => format!("declined {form:?}"),
            ExistenceUnread::Unreadable(_, leaf) => format!("unreadable {leaf:?}"),
            ExistenceUnread::Recovered(_) => "recovered".to_owned(),
            ExistenceUnread::TypeProvider(_) => "type provider".to_owned(),
            ExistenceUnread::UnreadableItem(_) => "unreadable item".to_owned(),
            ExistenceUnread::Budget(_) => "budget".to_owned(),
        },
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
        let text = std::fs::read_to_string(path).ok()?;
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let read = ours(&Cell::new("census", &[(name.as_str(), text.as_str())]));
        let charged = match &read {
            SourceExistence::Read(s) => Some(s.charged),
            SourceExistence::Unread(_) => None,
        };
        Some((reason(&read), charged))
    });
    let mut census: BTreeMap<String, Vec<&Path>> = BTreeMap::new();
    let mut most = (0usize, 0usize);
    for (path, v) in files.iter().zip(&verdicts) {
        if let Some((r, charged)) = v {
            census.entry(r.clone()).or_default().push(path);
            if let Some(c) = charged {
                most = (most.0.max(c.rows), most.1.max(c.bytes));
            }
        }
    }
    eprintln!(
        "{} files; the most a read file charged: {} rows, {} bytes",
        files.len(),
        most.0,
        most.1
    );
    let mut by_count: Vec<(&String, &Vec<&Path>)> = census.iter().collect();
    by_count.sort_by_key(|(_, paths)| std::cmp::Reverse(paths.len()));
    for (r, paths) in by_count {
        eprintln!("{:6}  {r}", paths.len());
        if r != "read" {
            for p in paths.iter().take(2) {
                eprintln!("          {}", p.display());
            }
        }
    }
}
