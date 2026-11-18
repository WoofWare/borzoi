//! `MSBuildStartupDirectory`, seeded from the `startup_directory` an
//! evaluation of a launched process supplies ([`crate::parse_fsproj_probed`]).
//! What it reads is held to MSBuild by `tests/startup_directory_diff.rs`; this
//! module holds the rules that differential cannot reach: the name is
//! reserved, so neither a global nor the environment displaces the seed, the
//! seed's resolution is in the read set, and a directory the walk cannot
//! resolve seeds nothing.

use super::*;
use crate::observed::soundness::{Why, sweep};
use tempfile::TempDir;

/// The project's copy of the name.
const COPY: &str =
    "<Project><PropertyGroup><Seen>$(MSBuildStartupDirectory)</Seen></PropertyGroup></Project>";

/// `source` evaluated as `project`, started in `startup_directory`.
fn started_in(
    project: &Path,
    source: &str,
    environment: &HashMap<String, String>,
    startup_directory: Option<&Path>,
) -> ParsedProject {
    crate::parse_fsproj_probed(
        &crate::ProjectFile::buffer(project, source)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        environment,
        None,
        None,
        startup_directory,
        None,
    )
    .expect("well-formed XML parses")
    .project
}

/// `Seen`, when the walk commits it.
fn committed_seen(result: &ParsedProject) -> Option<&str> {
    let value = result.properties.get("Seen")?;
    result
        .property("Seen")
        .untrusted_cause()
        .is_none()
        .then_some(value.as_str())
}

#[cfg(unix)]
#[test]
fn the_seed_is_the_resolved_directory_and_the_environment_does_not_displace_it() {
    let tmp = TempDir::new().unwrap();
    let project = write_at(tmp.path(), "proj/App.proj", COPY);
    let start = tmp.path().join("start");
    std::fs::create_dir_all(&start).unwrap();
    let expected = canon(&start);
    // MSBuild filters a reserved name out of the environment.
    let spoofed = HashMap::from([(
        "MSBuildStartupDirectory".to_string(),
        "/spoofed".to_string(),
    )]);
    for environment in [HashMap::new(), spoofed] {
        let result = started_in(&project, COPY, &environment, Some(&start));
        assert_eq!(
            committed_seen(&result),
            Some(expected.to_str().unwrap()),
            "{environment:?}"
        );
    }
}

#[test]
fn without_a_startup_directory_the_name_stays_unset() {
    let tmp = TempDir::new().unwrap();
    let project = write_at(tmp.path(), "proj/App.proj", COPY);
    let spoofed = HashMap::from([(
        "MSBuildStartupDirectory".to_string(),
        "/spoofed".to_string(),
    )]);
    for environment in [HashMap::new(), spoofed] {
        let result = started_in(&project, COPY, &environment, None);
        assert_eq!(committed_seen(&result), None, "{environment:?}");
    }
}

#[test]
fn a_directory_the_walk_cannot_resolve_seeds_nothing() {
    let tmp = TempDir::new().unwrap();
    let project = write_at(tmp.path(), "proj/App.proj", COPY);
    for dir in [
        tmp.path().join("missing"),
        // Relative to this process's working directory, which is not the
        // launched process's.
        PathBuf::from("proj"),
    ] {
        let result = started_in(&project, COPY, &HashMap::new(), Some(&dir));
        assert_eq!(committed_seen(&result), None, "{}", dir.display());
    }
}

/// The startup directory reached through a link: retargeting the link moves
/// what the evaluation seeds, so the link's resolution must be in the read
/// set, or the sweep panics.
#[cfg(unix)]
#[test]
fn retargeting_the_startup_directory_s_link_invalidates_the_evaluation() {
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let project = write_at(&root, "proj/App.proj", COPY);
    std::fs::create_dir_all(root.join("one")).unwrap();
    std::fs::create_dir_all(root.join("two")).unwrap();
    let start = root.join("start");
    std::os::unix::fs::symlink(root.join("one"), &start).unwrap();
    // A second link for the sweep to retarget the first to.
    std::os::unix::fs::symlink(root.join("two"), root.join("other")).unwrap();
    let evaluate = || started_in(&project, COPY, &HashMap::new(), Some(&start));
    assert_eq!(
        committed_seen(&evaluate()),
        Some(root.join("one").to_str().unwrap())
    );
    let tally = sweep(&root, &evaluate, &[]);
    assert!(tally.moved(Why::Relink) > 0, "{tally:?}");
}

/// An import the startup directory selects, then the self-default idiom over
/// a name the imported file writes. MSBuild started beside the file reads the
/// file's value and skips the default, and started anywhere else takes the
/// default (`fsproj_global_perturbation_diff`'s `startup-selected-self-default`
/// holds both to the oracle). So a served evaluation, which has no startup
/// directory, cannot know which branch the default takes, while one started in
/// a directory commits what MSBuild reads there.
#[cfg(unix)]
#[test]
fn a_self_default_after_an_import_the_startup_directory_selects_commits_only_with_the_directory() {
    const SOURCE: &str = "<Project>\n  \
        <Import Project=\"$(MSBuildStartupDirectory)/x.props\" \
        Condition=\"Exists('$(MSBuildStartupDirectory)/x.props')\" />\n  \
        <PropertyGroup><Seen Condition=\"'$(Seen)' == ''\">default</Seen></PropertyGroup>\n\
        </Project>";
    let tmp = TempDir::new().unwrap();
    let root = canon(tmp.path());
    let project = write_at(&root, "proj/App.proj", SOURCE);
    write_at(
        &root,
        "beside/x.props",
        "<Project><PropertyGroup><Seen>imported</Seen></PropertyGroup></Project>",
    );
    std::fs::create_dir_all(root.join("elsewhere")).unwrap();
    let served = started_in(&project, SOURCE, &HashMap::new(), None);
    assert_eq!(committed_seen(&served), None, "{:?}", served.diagnostics);
    let beside = started_in(
        &project,
        SOURCE,
        &HashMap::new(),
        Some(&root.join("beside")),
    );
    assert_eq!(committed_seen(&beside), Some("imported"));
    let elsewhere = started_in(
        &project,
        SOURCE,
        &HashMap::new(),
        Some(&root.join("elsewhere")),
    );
    assert_eq!(committed_seen(&elsewhere), Some("default"));
}
