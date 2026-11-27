//! `mutants-manifest SET OUT_DIR REPO`: checks a mutation run's exact
//! manifest in the checkout at `REPO`, which the launcher names: the binary
//! may have been built from another checkout, or none.
//!
//! `OUT_DIR/run` is what `tools/mutants/inner.sh SET OUT_DIR/run` left:
//! cargo-mutants' `mutants.out/`, the `--list` output it graded against
//! (`listed.txt`), and the run's `run-info.tsv`. This reads them, with
//! `tools/mutants/sets.tsv` and `tools/mutants/equivalent.tsv`, into the set's
//! manifest ([`borzoi_oracle_harness::mutants`]) and compares it with
//! `REPO/tools/mutants/manifests/SET.txt`, or rewrites that file under
//! `BORZOI_UPDATE_MANIFESTS`. The run must be of the commit checked out now,
//! with no uncommitted change to a tracked file, and of the set `sets.tsv`
//! declares now, scope and all, or it is no pin of either.
//!
//! It runs outside the sandbox, after it, on files the sandboxed run could
//! write: everything under `OUT_DIR`, which the launcher made and the sandbox
//! could not replace. So it reads each of them only as a regular file of
//! bounded size, reached from `OUT_DIR` through real directories: never
//! through a symbolic link, and never a FIFO or device that could block it.
//!
//! Exits 0 when the manifest matches (or was rewritten), 1 when it moved, and
//! 2 when the run cannot be a manifest: a failed or missing baseline, a vacuous
//! run, a graded set that is not the listed one, or a stale `equivalent.tsv`
//! row.

use std::io::Read;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use borzoi_oracle_harness::manifest::{compare_described, compare_text, update_requested};
use borzoi_oracle_harness::mutants::{
    attach_sites, declared_sets, equivalence_files, manifest_items, parse_equivalents,
    parse_outcomes, scope_of, set_scope, tally,
};

/// The most a run's artifact may hold. A real `outcomes.json` is a few
/// kilobytes per mutant.
const ARTIFACT_LIMIT: u64 = 64 << 20;

/// The checkout `repo` names, absolute: it must be the root of a working tree,
/// so a path inside one is no substitute.
fn repo_root(repo: &Path) -> Result<PathBuf, String> {
    let root = repo
        .canonicalize()
        .map_err(|e| format!("the repository {}: {e}", repo.display()))?;
    let mut cmd = git_in(&root)?;
    cmd.args(["rev-parse", "--show-toplevel"]);
    let out = borzoi_spawn::BoundedCommand::new(cmd)
        .run()
        .map_err(|e| format!("git rev-parse --show-toplevel: {e}"))?;
    let top = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let top = Path::new(&top).canonicalize().ok();
    if !out.status.success() || top.as_deref() != Some(root.as_path()) {
        return Err(format!(
            "{} is not the root of a Git checkout",
            root.display()
        ));
    }
    Ok(root)
}

fn read(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))
}

/// Reads `base/rel` as UTF-8, where the sandboxed run could have written it:
/// every directory between `base` and the file must be a real directory, the
/// file a regular file (not a link), and its size at most [`ARTIFACT_LIMIT`].
/// The file is opened with `O_NOFOLLOW | O_NONBLOCK`, and re-checked once open.
fn read_artifact(base: &Path, rel: &str) -> Result<String, String> {
    let mut at = base.to_path_buf();
    let parts: Vec<&str> = rel.split('/').collect();
    if parts
        .iter()
        .any(|p| p.is_empty() || *p == "." || *p == "..")
    {
        return Err(format!(
            "{rel:?} is not a plain relative path under {}",
            base.display()
        ));
    }
    let (file, dirs) = parts.split_last().expect("split yields one part");
    for dir in dirs {
        at.push(dir);
        let meta = std::fs::symlink_metadata(&at).map_err(|e| format!("{}: {e}", at.display()))?;
        if !meta.file_type().is_dir() {
            return Err(format!("{} is not a directory", at.display()));
        }
    }
    at.push(file);
    let refuse = |why: &str| Err(format!("{}: {why}", at.display()));
    let meta = std::fs::symlink_metadata(&at).map_err(|e| format!("{}: {e}", at.display()))?;
    if !meta.file_type().is_file() {
        return refuse("not a regular file");
    }
    let f = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(&at)
        .map_err(|e| format!("open {}: {e}", at.display()))?;
    let open_meta = f.metadata().map_err(|e| format!("{}: {e}", at.display()))?;
    if !open_meta.file_type().is_file() {
        return refuse("not a regular file");
    }
    if open_meta.len() > ARTIFACT_LIMIT {
        return refuse("larger than the artifact limit");
    }
    let mut bytes = Vec::new();
    f.take(ARTIFACT_LIMIT + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("read {}: {e}", at.display()))?;
    if bytes.len() as u64 > ARTIFACT_LIMIT {
        return refuse("larger than the artifact limit");
    }
    String::from_utf8(bytes).map_err(|_| format!("{}: not UTF-8", at.display()))
}

/// Git's repository-local variables (`GIT_DIR`, `GIT_INDEX_FILE`, …), as
/// `git rev-parse --local-env-vars` names them.
fn git_local_env_vars() -> Result<Vec<String>, String> {
    let mut cmd = std::process::Command::new("git");
    cmd.args(["rev-parse", "--local-env-vars"]);
    let out = borzoi_spawn::BoundedCommand::new(cmd)
        .run()
        .map_err(|e| format!("git rev-parse --local-env-vars: {e}"))?;
    if !out.status.success() {
        return Err("git rev-parse --local-env-vars failed".into());
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_string)
        .collect())
}

/// `git -C root`, with Git's repository-local variables cleared: one
/// inherited from a hook or a caller would point it at another repository.
fn git_in(root: &Path) -> Result<std::process::Command, String> {
    let mut cmd = std::process::Command::new("git");
    for var in git_local_env_vars()? {
        cmd.env_remove(var);
    }
    cmd.arg("-C").arg(root);
    Ok(cmd)
}

/// `Ok` when the checkout at `root` is `commit`, with no uncommitted change to
/// a tracked file; otherwise why not.
fn checkout_is(root: &Path, commit: &str) -> Result<(), String> {
    let git = |args: &[&str]| -> Result<String, String> {
        let mut cmd = git_in(root)?;
        cmd.args(args);
        let out = borzoi_spawn::BoundedCommand::new(cmd)
            .run()
            .map_err(|e| format!("git {}: {e}", args.join(" ")))?;
        if !out.status.success() {
            return Err(format!(
                "git {}: {}",
                args.join(" "),
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    let head = git(&["rev-parse", "HEAD"])?;
    if head != commit {
        return Err(format!(
            "the run graded commit {commit}, but the checkout is at {head}; \
             check the run from a clean checkout of {commit}"
        ));
    }
    if !git(&["status", "--porcelain", "--untracked-files=no"])?.is_empty() {
        return Err(format!(
            "the checkout has uncommitted changes to tracked files, so it is not commit \
             {commit} the run graded"
        ));
    }
    Ok(())
}

/// `run-info.tsv`: `key<TAB>value…` lines `inner.sh` writes.
struct RunInfo {
    set: String,
    commit: String,
    package: String,
    files: String,
    skips: Vec<(String, String)>,
}

fn parse_run_info(text: &str) -> Result<RunInfo, String> {
    let (mut set, mut commit, mut package, mut files) = (None, None, None, None);
    let mut skips = Vec::new();
    for line in text.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["set", v] => set = Some(v.to_string()),
            ["commit", v] => commit = Some(v.to_string()),
            ["package", v] => package = Some(v.to_string()),
            ["files", v] => files = Some(v.to_string()),
            ["skip", filter, reason] => skips.push((filter.to_string(), reason.to_string())),
            _ => return Err(format!("run-info.tsv: unexpected line {line:?}")),
        }
    }
    let need = |v: Option<String>, k: &str| v.ok_or_else(|| format!("run-info.tsv: no {k}"));
    Ok(RunInfo {
        set: need(set, "set")?,
        commit: need(commit, "commit")?,
        package: need(package, "package")?,
        files: need(files, "files")?,
        skips,
    })
}

/// Whether `set` may name a set, as `tools/mutants/sets.sh`'s
/// `mutants_set_name_ok` decides: one plain path component, since it names
/// the manifest file this writes.
fn set_name_ok(set: &str) -> bool {
    let mut chars = set.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
        && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

fn run(set: &str, out_dir: &Path, repo: &Path) -> Result<Result<(), String>, String> {
    if !set_name_ok(set) {
        return Err(format!("{set:?} is not a set name"));
    }
    let info = parse_run_info(&read_artifact(out_dir, "run/run-info.tsv")?)?;
    if info.set != set {
        return Err(format!(
            "{} is a run of set {:?}, not {set:?}",
            out_dir.display(),
            info.set
        ));
    }
    let root = repo_root(repo)?;
    checkout_is(&root, &info.commit)?;
    let sets_tsv = read(&root.join("tools/mutants/sets.tsv"))?;
    let scope = scope_of(&info.package, &info.files, &info.skips);
    match set_scope(&sets_tsv, set) {
        None => return Err(format!("sets.tsv declares no set {set:?}")),
        Some(declared) if declared != scope => {
            return Err(format!(
                "the run's scope {scope:?} is not the one sets.tsv declares now, \
                 {declared:?}; run the set again"
            ));
        }
        Some(_) => {}
    }
    let mut outcomes = parse_outcomes(&read_artifact(out_dir, "run/mutants.out/outcomes.json")?)?;
    let equivalents = parse_equivalents(&read(&root.join("tools/mutants/equivalent.tsv"))?)?;
    // A site matters only to an equivalence row, so only the files the set's
    // rows name are read, each once, from the checkout `checkout_is` has held
    // to the graded commit; and each line's site is made once and shared. The
    // files are named by the repository's own `equivalent.tsv`, but read as an
    // artifact is (a plain relative path to a bounded regular file).
    let mut sources = std::collections::BTreeMap::new();
    for file in equivalence_files(set, &equivalents) {
        sources.insert(file, read_artifact(&root, file)?);
    }
    attach_sites(&mut outcomes.mutants, &sources);
    let listed: Vec<String> = read_artifact(out_dir, "run/listed.txt")?
        .lines()
        .filter(|l| !l.is_empty())
        .map(str::to_string)
        .collect();
    let declared = declared_sets(&sets_tsv);
    let manifest = manifest_items(set, &outcomes, &listed, &scope, &declared, &equivalents)
        .map_err(|e| e.to_string())?;

    let counts = tally(&manifest)
        .iter()
        .map(|(name, n)| format!("{n} {name}"))
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!(
        "mutants-manifest: set {set} at commit {}: {} mutants; {counts}",
        info.commit,
        outcomes.mutants.len()
    );
    // The header holds nothing that moves: a merge reads it as one value, so a
    // commit, a count or a tally there would conflict whenever two branches
    // regenerate the manifest. They go to the run's report above.
    let description = format!(
        "Mutation set {set}: one `caught`, `missed`, `timeout`, `unviable` or\n\
         `equivalent: <reason>` line per mutant, and the run's `scope:` lines.\n\
         Tests its mutants never face: doctests (`tools/mutants/inner.sh` passes\n\
         `--tests`), every #[ignore]d test, and the `scope: skip` filters."
    );
    let rel = format!("tools/mutants/manifests/{set}.txt");
    let path = root.join(&rel);
    let regenerate = format!("BORZOI_UPDATE_MANIFESTS=1 tools/mutants/run.sh {set}");
    if !update_requested() {
        // A check pins the set to the manifest the graded commit holds: its
        // blob, read from the commit, not whatever the working tree has at
        // that path (an untracked file, a link, or bytes Git was told to
        // ignore).
        let origin = format!("{rel} at {}", info.commit);
        return Ok(match committed_manifest(&root, &info.commit, &rel)? {
            Some(text) => compare_text(&text, &origin, &manifest, &regenerate),
            None => Err(format!(
                "commit {} has no regular file {rel}, so no manifest for {set}; commit \
                 one, or regenerate with:\n  {regenerate}",
                info.commit
            )),
        });
    }
    regeneration_destination(&path)?;
    Ok(compare_described(
        &path,
        &manifest,
        &description,
        &regenerate,
        true,
    ))
}

/// `Ok` when a regeneration may write `path`: it is absent (a new set's
/// manifest) or a regular file, never a link, FIFO, device or directory, which
/// the write would follow, block on or fail at.
fn regeneration_destination(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(meta) if !meta.file_type().is_file() => Err(format!(
            "{} exists and is not a regular file",
            path.display()
        )),
        Ok(_) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(format!("{}: {e}", path.display())),
    }
}

/// The text of `rel` as commit `commit` of the checkout at `root` holds it,
/// if the commit has it as a regular file (mode `100644` or `100755`, not a
/// link or a submodule) of at most [`ARTIFACT_LIMIT`] bytes of UTF-8.
fn committed_manifest(root: &Path, commit: &str, rel: &str) -> Result<Option<String>, String> {
    let git = |args: &[&str]| -> Result<(bool, Vec<u8>), String> {
        let mut cmd = git_in(root)?;
        cmd.args(args);
        let out = borzoi_spawn::BoundedCommand::new(cmd)
            .run()
            .map_err(|e| format!("git {}: {e}", args.join(" ")))?;
        Ok((out.status.success(), out.stdout))
    };
    let (ok, listing) = git(&["ls-tree", "-z", commit, "--", rel])?;
    if !ok {
        return Err(format!("git ls-tree {commit}: failed"));
    }
    // `<mode> <type> <object>\t<path>\0`: exactly one entry, for exactly `rel`.
    let entries: Vec<&[u8]> = listing
        .split(|b| *b == 0)
        .filter(|e| !e.is_empty())
        .collect();
    let [entry] = entries.as_slice() else {
        return Ok(None);
    };
    let entry = String::from_utf8_lossy(entry);
    let Some((meta, path)) = entry.split_once('\t') else {
        return Ok(None);
    };
    let fields: Vec<&str> = meta.split(' ').collect();
    let [mode, "blob", object] = fields.as_slice() else {
        return Ok(None);
    };
    if path != rel || !matches!(*mode, "100644" | "100755") {
        return Ok(None);
    }
    let (ok, size) = git(&["cat-file", "-s", object])?;
    let size: u64 = String::from_utf8_lossy(&size)
        .trim()
        .parse()
        .unwrap_or(u64::MAX);
    if !ok || size > ARTIFACT_LIMIT {
        return Err(format!("{rel} at {commit} is over {ARTIFACT_LIMIT} bytes"));
    }
    let (ok, bytes) = git(&["cat-file", "blob", object])?;
    if !ok {
        return Err(format!("git cat-file blob {object}: failed"));
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| format!("{rel} at {commit} is not UTF-8"))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [set, out_dir, repo] = args.as_slice() else {
        eprintln!("usage: mutants-manifest SET OUT_DIR REPO");
        return ExitCode::from(2);
    };
    match run(set, Path::new(out_dir), Path::new(repo)) {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(moved)) => {
            eprintln!("mutants-manifest: {moved}");
            ExitCode::from(1)
        }
        Err(e) => {
            eprintln!("mutants-manifest: set {set}: {e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_what_inner_sh_writes() {
        let info = parse_run_info(
            "set\ts\ncommit\tabc\npackage\tp\nfiles\ta.rs b/*.rs\n\
             skip\tnet_\treaches nuget.org\n",
        )
        .unwrap();
        assert_eq!(
            (
                info.set.as_str(),
                info.commit.as_str(),
                info.package.as_str(),
                info.files.as_str()
            ),
            ("s", "abc", "p", "a.rs b/*.rs")
        );
        assert_eq!(
            info.skips,
            vec![("net_".to_string(), "reaches nuget.org".to_string())]
        );
    }

    #[test]
    fn git_runs_without_the_callers_repository_variables() {
        let cmd = git_in(Path::new("/nowhere")).unwrap();
        let cleared: Vec<_> = cmd
            .get_envs()
            .filter(|(_, v)| v.is_none())
            .map(|(k, _)| k.to_string_lossy().into_owned())
            .collect();
        for var in [
            "GIT_DIR",
            "GIT_INDEX_FILE",
            "GIT_WORK_TREE",
            "GIT_OBJECT_DIRECTORY",
        ] {
            assert!(
                cleared.iter().any(|c| c == var),
                "{var} not cleared: {cleared:?}"
            );
        }
    }

    #[test]
    fn a_regeneration_writes_only_a_new_or_regular_file() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path();
        assert!(regeneration_destination(&base.join("new.txt")).is_ok());
        std::fs::write(base.join("regular.txt"), "x").unwrap();
        assert!(regeneration_destination(&base.join("regular.txt")).is_ok());
        std::os::unix::fs::symlink(base.join("regular.txt"), base.join("link.txt")).unwrap();
        assert!(regeneration_destination(&base.join("link.txt")).is_err());
        let fifo = base.join("fifo.txt");
        let c = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(c.as_ptr(), 0o600) }, 0);
        assert!(regeneration_destination(&fifo).is_err());
        std::fs::create_dir(base.join("dir.txt")).unwrap();
        assert!(regeneration_destination(&base.join("dir.txt")).is_err());
    }

    #[test]
    fn set_names_are_one_plain_path_component() {
        for ok in ["a", "nuget-regular-file", "0x"] {
            assert!(set_name_ok(ok), "{ok}");
        }
        for bad in ["", "../a", "a/b", ".", "..", "-a", "A", "a b", "a.b"] {
            assert!(!set_name_ok(bad), "{bad}");
        }
    }

    #[test]
    fn refuses_unknown_lines_and_missing_fields() {
        assert!(parse_run_info("set\ts\nbogus\tx\n").is_err());
        let missing = parse_run_info("set\ts\ncommit\tabc\nfiles\ta.rs\n");
        assert!(missing.err().unwrap().contains("package"));
    }

    #[test]
    fn the_checkout_must_be_the_graded_commit_and_clean() {
        let dir = tempfile::tempdir().unwrap();
        let repo = dir.path();
        let git = |args: &[&str]| {
            let mut cmd = git_in(repo).unwrap();
            cmd.args(["-c", "user.name=t", "-c", "user.email=t@t", "-c"])
                .arg("commit.gpgsign=false")
                .args(args);
            let out = borzoi_spawn::BoundedCommand::new(cmd).run().unwrap();
            assert!(out.status.success(), "git {args:?}");
            String::from_utf8(out.stdout).unwrap().trim().to_string()
        };
        git(&["init", "-q"]);
        std::fs::write(repo.join("f"), "1").unwrap();
        git(&["add", "f"]);
        git(&["commit", "-q", "-m", "one"]);
        let first = git(&["rev-parse", "HEAD"]);
        // The checkout is named by its root, and only by its root.
        let canonical = repo.canonicalize().unwrap();
        assert_eq!(repo_root(repo), Ok(canonical.clone()));
        std::fs::create_dir(repo.join("sub")).unwrap();
        assert!(repo_root(&repo.join("sub")).is_err());
        assert!(repo_root(&repo.join("absent")).is_err());
        assert_eq!(checkout_is(repo, &first), Ok(()));
        std::fs::write(repo.join("f"), "2").unwrap();
        assert!(
            checkout_is(repo, &first)
                .unwrap_err()
                .contains("uncommitted")
        );
        git(&["commit", "-q", "-am", "two"]);
        assert!(
            checkout_is(repo, &first)
                .unwrap_err()
                .contains("clean checkout")
        );
        // An untracked file is not part of what the run graded.
        let second = git(&["rev-parse", "HEAD"]);
        std::fs::write(repo.join("untracked"), "").unwrap();
        assert_eq!(checkout_is(repo, &second), Ok(()));
        // And it is no manifest a check can pin to; a committed regular file
        // is, as the commit holds it, and a committed link is not.
        assert_eq!(committed_manifest(repo, &second, "untracked"), Ok(None));
        assert_eq!(committed_manifest(repo, &second, "f"), Ok(Some("2".into())));
        assert_eq!(committed_manifest(repo, &first, "f"), Ok(Some("1".into())));
        std::os::unix::fs::symlink("untracked", repo.join("link")).unwrap();
        git(&["add", "link"]);
        git(&["commit", "-q", "-m", "link"]);
        let third = git(&["rev-parse", "HEAD"]);
        assert_eq!(committed_manifest(repo, &third, "link"), Ok(None));
        assert_eq!(committed_manifest(repo, &third, "absent"), Ok(None));
        // Bytes Git was told not to look at are not the commit's.
        git(&["update-index", "--assume-unchanged", "f"]);
        std::fs::write(repo.join("f"), "edited").unwrap();
        assert_eq!(checkout_is(repo, &third), Ok(()));
        assert_eq!(committed_manifest(repo, &third, "f"), Ok(Some("2".into())));
    }

    #[test]
    fn artifacts_are_bounded_regular_files_behind_real_directories() {
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path();
        std::fs::create_dir(base.join("out")).unwrap();
        std::fs::write(base.join("out/ok.txt"), "fine").unwrap();
        assert_eq!(read_artifact(base, "out/ok.txt").unwrap(), "fine");

        std::os::unix::fs::symlink(base.join("out/ok.txt"), base.join("out/link.txt")).unwrap();
        assert!(read_artifact(base, "out/link.txt").is_err());

        std::os::unix::fs::symlink(base.join("out"), base.join("linked")).unwrap();
        assert!(read_artifact(base, "linked/ok.txt").is_err());

        let fifo = base.join("out/fifo");
        let c = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(c.as_ptr(), 0o600) }, 0);
        assert!(read_artifact(base, "out/fifo").is_err());

        let big = std::fs::File::create(base.join("out/big")).unwrap();
        big.set_len(ARTIFACT_LIMIT + 1).unwrap();
        assert!(read_artifact(base, "out/big").is_err());

        std::fs::write(base.join("out/bytes"), [0xff, 0xfe]).unwrap();
        assert!(read_artifact(base, "out/bytes").is_err());

        // Paths that would leave `base`, or name it oddly, are refused before
        // any read.
        for rel in [
            "../out/ok.txt",
            "out/../out/ok.txt",
            "/etc/hosts",
            "out//ok.txt",
            "./out/ok.txt",
        ] {
            assert!(read_artifact(base, rel).is_err(), "{rel}");
        }
    }
}
