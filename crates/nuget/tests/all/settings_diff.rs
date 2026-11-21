//! `borzoi_nuget::settings::global_packages_folder` against NuGet's own
//! `SettingsUtility.GetGlobalPackagesFolder(Settings.LoadDefaultSettings(…))`,
//! over generated config hierarchies, held to *certain-implies-exact*: where
//! the model commits, NuGet loads the same config files, in the same order,
//! and names the same folder; where NuGet throws, the model declined.
//!
//! The generator varies what the model's domain is stated over, layer by
//! layer: which folders of the walk hold a config file and under which
//! spelling, the user config and the user's additional configs, (on Linux)
//! the machine-wide folder; the bytes (a byte order mark), the declaration,
//! the root's name, sections and their repetition, the `config` section's
//! items, element-name and key case, duplicates, `clear`s, attribute order,
//! stray attributes and text, truncation; and the value (relative, absolute,
//! `%NAME%` set, empty and unset, characters outside the domain), with
//! `NUGET_PACKAGES` unset, empty, absolute and relative.
//!
//! It also draws the hostile values of `borzoi_oracle_harness::hostile` (the
//! census `settings`): what sits where NuGet looks for a config file (a FIFO,
//! a dangling link, a directory: [`hostile::fs`]), the names of the folders
//! of the walk and of the files in the folder NuGet lists ([`name`]), how a
//! config file spells its value and the text between its items ([`xml`]),
//! and the variables of the environment ([`env`]). Each is enumerated once
//! per run ([`cover`]) and mixed into the generator at [`hostile::RATE`]. A
//! FIFO where NuGet opens a config file makes NuGet wait for a writer, so
//! there is no answer to be exact with: NuGet is not asked, and the model
//! must decline.
//!
//! Every case runs both sides under one controlled environment: the oracle
//! child inherits this process's environment with the variables NuGet reads
//! for this purpose fixed (the home, the machine-wide override) or removed,
//! and each request sets the per-case ones (`NUGET_PACKAGES` and the
//! variables values name) for itself. The model is handed exactly that map.
//! NuGet reads the home and the machine-wide folder once per process, which
//! is why those are per-oracle, and .NET reads the culture when it starts,
//! which is why a hostile locale is set in the oracle's own process.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::Duration;

use borzoi_nuget::settings::{
    FolderOrigin, GlobalPackagesFolder, GlobalPackagesFolderDecline, global_packages_folder,
};
use borzoi_oracle_harness::hostile::census::Census;
use borzoi_oracle_harness::hostile::fs::{State, Unmakeable};
use borzoi_oracle_harness::hostile::name::{self, Name, Rendered};
use borzoi_oracle_harness::hostile::{self, Dimension, Entry, env, xml};
use serde_json::json;

use crate::common::{EnvironmentChange, Oracle, SplitMix64};

/// The census of hostile values this harness runs.
const CENSUS: &str = "settings";

/// The command that regenerates the census's manifest.
const REGENERATE: &str = "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-nuget --test all settings_diff::";

/// The variables a case sets for its own request; every request names all of
/// them, so none leaks from one case into the next.
const CASE_VARIABLES: &[&str] = &[
    "NUGET_PACKAGES",
    "BORZOI_GPF_A",
    "BORZOI_GPF_B",
    "BORZOI_GPF_EMPTY",
];

/// The variables NuGet reads to find the folders, fixed per oracle.
const FIXED_VARIABLES: &[&str] = &[
    "DOTNET_CLI_HOME",
    "HOME",
    "NUGET_PACKAGES",
    "NUGET_COMMON_APPLICATION_DATA",
];

/// The variables NuGet reads once per process: a hostile value of one is set
/// for an oracle of its own, never for a single request.
const PROCESS_VARIABLES: &[&str] = &["DOTNET_CLI_HOME", "HOME", "NUGET_COMMON_APPLICATION_DATA"];

/// Why NuGet gives no answer where it opens a FIFO as a config file.
const OPENS_A_FIFO: &str = "NuGet opens the FIFO as a config file and waits for a writer";

/// One oracle and the scratch tree its cases are written into.
struct Harness {
    oracle: Oracle,
    /// The environment the oracle child holds before a request's changes.
    environment: BTreeMap<OsString, OsString>,
    base: PathBuf,
    /// Makes the hostile file-system states, under `base`.
    hostile: hostile::fs::HostileFs,
    _dir: tempfile::TempDir,
}

impl Harness {
    /// An oracle whose home is `<base>/home`, or `<base>/cli-home` through
    /// `DOTNET_CLI_HOME` when `cli_home` holds, and whose machine-wide folder
    /// on Linux is under `<base>/common`.
    fn spawn(cli_home: bool) -> Harness {
        Harness::spawn_with(cli_home, &[], &[])
    }

    /// [`Self::spawn`], with `fixed` set after the per-oracle variables (so a
    /// hostile one replaces them), and `process` set in the oracle's own
    /// process environment, which is what .NET reads when it starts.
    fn spawn_with(
        cli_home: bool,
        fixed: &[(&'static str, &'static str)],
        process: &[(&'static str, &'static str)],
    ) -> Harness {
        let dir = tempfile::tempdir().expect("temp dir");
        let root = std::fs::canonicalize(dir.path()).expect("canonical temp dir");
        let (base, aside) = (root.join("b"), root.join("aside"));
        std::fs::create_dir(&base).expect("create the base");
        std::fs::create_dir(&aside).expect("create the directory aside");
        let text = |path: PathBuf| path.to_str().expect("UTF-8 temp dir").to_owned();
        let home = text(base.join("home"));
        let cli = text(base.join("cli-home"));
        let common = text(base.join("common"));
        let mut changes: Vec<EnvironmentChange<'_>> = FIXED_VARIABLES
            .iter()
            .chain(CASE_VARIABLES)
            .map(|name| EnvironmentChange::Unset(name))
            .collect();
        changes.push(EnvironmentChange::Set("HOME", &home));
        changes.push(EnvironmentChange::Set(
            "NUGET_COMMON_APPLICATION_DATA",
            &common,
        ));
        if cli_home {
            changes.push(EnvironmentChange::Set("DOTNET_CLI_HOME", &cli));
        }
        changes.extend(
            fixed
                .iter()
                .map(|(name, value)| EnvironmentChange::Set(name, value)),
        );
        let mut environment: BTreeMap<OsString, OsString> = std::env::vars_os().collect();
        for change in &changes {
            match change {
                EnvironmentChange::Set(name, value) => {
                    environment.insert(OsString::from(name), OsString::from(value));
                }
                EnvironmentChange::Unset(name) => {
                    environment.remove(OsStr::new(name));
                }
            }
        }
        for (name, value) in process {
            environment.insert(OsString::from(name), OsString::from(value));
        }
        let oracle = if process.is_empty() {
            Oracle::spawn_with_changes(&changes)
        } else {
            // Every change in the process environment too, applied in order
            // before the process's own variables: an oracle started this way
            // makes no change from inside.
            let mut all: Vec<(String, Option<String>)> = changes
                .iter()
                .map(|change| match change {
                    EnvironmentChange::Set(name, value) => {
                        ((*name).to_owned(), Some((*value).to_owned()))
                    }
                    EnvironmentChange::Unset(name) => ((*name).to_owned(), None),
                })
                .collect();
            all.extend(
                process
                    .iter()
                    .map(|(name, value)| ((*name).to_owned(), Some((*value).to_owned()))),
            );
            Oracle::spawn_with_process_environment(&all)
        };
        Harness {
            oracle,
            environment,
            hostile: hostile::fs::HostileFs::over(&base, &aside),
            base,
            _dir: dir,
        }
    }
}

/// A hostile state to make at a name in a folder (relative to the harness
/// base) before the case's files are written.
#[derive(Debug, Clone)]
struct Placement {
    dir: String,
    name: Rendered,
    state: State,
    /// What a regular file there holds, or the file a link there points at.
    content: Vec<u8>,
}

/// A generated case: the files to write (relative to the harness base), the
/// per-case variables, and the project folder.
#[derive(Debug, Clone)]
struct Case {
    files: Vec<(String, Vec<u8>)>,
    /// Whether a file holds something NuGet throws on in a section the model
    /// does not read: outside the model's claim, which is conditional on
    /// NuGet's loading the settings.
    unread_fault: bool,
    /// Folders made (empty) before the files are written: whether the home
    /// exists decides whether .NET hands NuGet `HOME` at all.
    folders: Vec<&'static str>,
    variables: Vec<(&'static str, Option<String>)>,
    root: String,
    /// The hostile states, made before everything else.
    placements: Vec<Placement>,
    /// The hostile dimensions drawn into the case.
    hostile: BTreeSet<Dimension>,
    /// Why NuGet gives no answer at all (it waits for ever, or works in a
    /// folder the test does not own), if it does not: NuGet is then not
    /// asked, and the model must decline.
    unanswerable: Option<&'static str>,
    /// Where NuGet opens the user config, under the harness's base. The
    /// case may have written it there, or under a spelling that is this file
    /// only where the file system ignores case, or put a hostile state
    /// there, or nothing.
    user_config: String,
}

impl Case {
    /// A case whose one config file is a user config naming no folder (where
    /// there is none NuGet writes one, which the model declines), in the
    /// folder `tree/l0`.
    fn empty() -> Case {
        Case {
            files: vec![(USER_CONFIG.to_owned(), b"<configuration />\n".to_vec())],
            unread_fault: false,
            folders: vec!["home"],
            variables: vec![
                ("NUGET_PACKAGES", None),
                ("BORZOI_GPF_A", None),
                ("BORZOI_GPF_B", Some("sub".to_owned())),
                ("BORZOI_GPF_EMPTY", Some(String::new())),
            ],
            root: "tree/l0".to_owned(),
            placements: Vec::new(),
            hostile: BTreeSet::new(),
            unanswerable: None,
            user_config: USER_CONFIG.to_owned(),
        }
    }

    /// Set `name` for the case's request, replacing a value it had.
    fn set_variable(&mut self, name: &'static str, value: Option<String>) {
        self.variables.retain(|(existing, _)| *existing != name);
        self.variables.push((name, value));
    }

    fn describe(&self) -> String {
        let files: Vec<String> = self
            .files
            .iter()
            .map(|(path, bytes)| format!("--- {path}\n{}", String::from_utf8_lossy(bytes)))
            .collect();
        format!(
            "root {}\nvariables {:?}\nhostile {:?}\nplacements {:?}\n{}",
            self.root,
            self.variables,
            self.hostile,
            self.placements,
            files.join("\n")
        )
    }
}

/// What grading one case found.
#[derive(Debug)]
enum Verdict {
    Committed(GlobalPackagesFolder),
    /// The model committed and NuGet threw on a section the model does not
    /// read, where the model's claim is silent.
    CommittedWhereNuGetThrewOnAnUnreadSection,
    /// The model declined; NuGet's answer (`None`), or the type and start of
    /// the message of what it threw.
    Declined {
        decline: GlobalPackagesFolderDecline,
        nuget_threw: Option<String>,
    },
    /// The model declined a case NuGet gives no answer to.
    DeclinedUnanswerable,
    /// The platform could not make a hostile state of the case.
    Unmade(Unmakeable),
}

/// The model's answer, computed on a thread of its own, or a panic when none
/// comes within two minutes: a read that opens a FIFO fails the test rather
/// than hangs it.
fn model_within_deadline(
    root: PathBuf,
    environment: BTreeMap<OsString, OsString>,
) -> Result<GlobalPackagesFolder, GlobalPackagesFolderDecline> {
    let (sender, receiver) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = sender.send(global_packages_folder(&root, &environment));
    });
    match receiver.recv_timeout(Duration::from_secs(120)) {
        Ok(answer) => answer,
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!("the model did not answer within two minutes: some read blocked")
        }
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => panic!("the model panicked"),
    }
}

/// Write `case` into a clean tree, ask both sides, and assert the contract.
/// Returns the verdict, and whether the case has a user config: a regular
/// file where NuGet opens one, before NuGet was asked.
fn grade(harness: &mut Harness, case: &Case) -> (Verdict, bool) {
    for folder in ["tree", "home", "cli-home", "common"] {
        let path = harness.base.join(folder);
        if path.exists() {
            std::fs::remove_dir_all(&path).expect("clean the case tree");
        }
    }
    for placement in &case.placements {
        if let Err(refusal) = harness.hostile.place(
            &placement.dir,
            &placement.name,
            placement.state,
            &placement.content,
        ) {
            return (Verdict::Unmade(refusal), false);
        }
    }
    std::fs::create_dir_all(harness.base.join(&case.root)).expect("create the root");
    for folder in &case.folders {
        std::fs::create_dir_all(harness.base.join(folder)).expect("create a folder");
    }
    for (path, bytes) in &case.files {
        let path = harness.base.join(path);
        std::fs::create_dir_all(path.parent().expect("a file has a folder")).expect("mkdir");
        std::fs::write(&path, bytes).expect("write a config file");
    }
    let root = harness.base.join(&case.root);
    let mut environment = harness.environment.clone();
    for (name, value) in &case.variables {
        match value {
            Some(value) => environment.insert(OsString::from(name), OsString::from(value)),
            None => environment.remove(OsStr::new(name)),
        };
    }
    // The model first: NuGet writes a default user config where there is none.
    let ours = model_within_deadline(root.clone(), environment);
    // NuGet writes a user config where there is none, and answers. The model
    // does not know that NuGet can write one, so no agreement with NuGet's
    // answer makes a commit there sound. Asked of the tree as it is laid
    // out, since which spelling is the file depends on the file system. A
    // case that moves the home is one NuGet has no answer for, and must
    // decline for that.
    let user_config = harness.base.join(&case.user_config).is_file();
    assert!(
        user_config || ours.is_err(),
        "the model committed where there is no user config: {ours:?}\n{}",
        case.describe()
    );
    if let Some(why) = case.unanswerable {
        assert!(
            ours.is_err(),
            "the model committed to {ours:?} where NuGet gives no answer ({why})\n{}",
            case.describe()
        );
        return (Verdict::DeclinedUnanswerable, user_config);
    }
    let request = json!({
        "op": "globalPackagesFolder",
        "root": root.to_str().expect("UTF-8"),
        "environment": case.variables.iter().map(|(name, value)| json!([name, value])).collect::<Vec<_>>(),
    });
    let theirs = harness.oracle.request(&request);
    let describe = || format!("{}\nNuGet: {theirs}", case.describe());
    let answered = theirs["ok"].as_bool().expect("ok is a bool");
    let verdict = match ours {
        Ok(committed) => {
            if !answered {
                assert!(
                    case.unread_fault,
                    "the model committed to {committed:?} where NuGet threw\n{}",
                    describe()
                );
                return (
                    Verdict::CommittedWhereNuGetThrewOnAnUnreadSection,
                    user_config,
                );
            }
            let folder = normalise(theirs["folder"].as_str().expect("folder"));
            assert_eq!(
                committed.folder,
                folder,
                "the model committed to another folder\n{}",
                describe()
            );
            let files: Vec<PathBuf> = theirs["configFilePaths"]
                .as_array()
                .expect("configFilePaths")
                .iter()
                .map(|path| PathBuf::from(path.as_str().expect("a path")))
                .collect();
            assert_eq!(
                committed.config_files,
                files,
                "the model loads other config files\n{}",
                describe()
            );
            Verdict::Committed(committed)
        }
        Err(decline) => Verdict::Declined {
            decline,
            nuget_threw: (!answered).then(|| {
                let message = theirs["message"].as_str().unwrap_or("");
                let message: String = message.chars().take(60).collect();
                format!(
                    "{}: {message}",
                    theirs["exceptionType"].as_str().unwrap_or("?")
                )
            }),
        },
    };
    (verdict, user_config)
}

/// An absolute path made lexically normal, without a trailing separator: the
/// currency both sides are compared in.
fn normalise(path: &str) -> PathBuf {
    let mut out = PathBuf::from("/");
    for component in Path::new(path).components() {
        match component {
            std::path::Component::Normal(name) => out.push(name),
            std::path::Component::ParentDir => {
                out.pop();
            }
            _ => {}
        }
    }
    out
}

// ----------------------------------------------------------------------------
// The generator
// ----------------------------------------------------------------------------

/// The spellings a config file is written under in a folder of the walk: the
/// three NuGet looks for on a case-sensitive volume, and two it never does.
const WALK_SPELLINGS: &[&str] = &[
    "nuget.config",
    "NuGet.config",
    "NuGet.Config",
    "NUGET.CONFIG",
    "nuget.Config",
];

/// Names in the user's additional config folder (and the machine-wide one).
const LISTED_NAMES: &[&str] = &[
    "a.config",
    "b.Config",
    "C.config",
    "_u.config",
    "d.CONFIG",
    "nuget.config",
    "e.config.bak",
    "f.txt",
];

/// The user config under the home `home`, relative to the harness base.
const USER_CONFIG: &str = "home/.nuget/NuGet/NuGet.Config";

/// The user's additional config folder, under the home `home`.
fn listed_folder(home: &str) -> String {
    format!("{home}/.nuget/NuGet/config")
}

/// A plain name: `stem` and `ext`, nothing hostile.
fn plain(stem: &str, ext: &str) -> Rendered {
    Name {
        parts: name::PLAIN,
        twin: None,
    }
    .render(stem, ext)
}

/// The name NuGet opens a config file under wherever it looks: the user
/// config's name, and in a folder of the walk the one spelling every platform
/// looks for when it is the folder's only one.
fn opened_name() -> Rendered {
    plain("NuGet", ".Config")
}

/// Whether NuGet reads the content of a config file in `state`: a file whose
/// content it does not read cannot be what it throws on.
fn content_is_read(state: State) -> bool {
    matches!(
        state,
        State::Regular | State::Symlink | State::SymlinkOutOfTree | State::ReadOnly
    )
}

/// The hostile names a folder of the walk can take: text (the root is sent
/// to NuGet as JSON), and not the plain name.
fn walk_folder_names() -> &'static [Entry<Name>] {
    static NAMES: OnceLock<Vec<Entry<Name>>> = OnceLock::new();
    NAMES.get_or_init(|| {
        name::alphabet()
            .filtered(|e| e.value.varies("d", "") && e.value.render("d", "").to_str().is_some())
    })
}

/// The hostile environments a single request can carry: those that set no
/// variable NuGet reads once per process, and no culture, which .NET reads
/// when it starts.
fn request_environments() -> &'static [Entry<env::Variables>] {
    static ENVIRONMENTS: OnceLock<Vec<Entry<env::Variables>>> = OnceLock::new();
    ENVIRONMENTS.get_or_init(|| env::alphabet().filtered(|e| own_oracle(e).is_none()))
}

/// What an oracle of its own must be started with to grade `entry`, if a
/// single request cannot carry it: the per-oracle variables it sets, and the
/// process variables.
#[allow(clippy::type_complexity)]
fn own_oracle(
    entry: &Entry<env::Variables>,
) -> Option<(
    Vec<(&'static str, &'static str)>,
    Vec<(&'static str, &'static str)>,
)> {
    let fixed: Vec<_> = entry
        .value
        .iter()
        .copied()
        .filter(|(name, _)| PROCESS_VARIABLES.contains(name))
        .collect();
    let process: Vec<_> = if entry.dimension == Dimension::Locale {
        entry.value.to_vec()
    } else {
        Vec::new()
    };
    (!fixed.is_empty() || !process.is_empty()).then_some((fixed, process))
}

fn gen_value(rng: &mut SplitMix64, base: &Path) -> String {
    let absolute = base.join("abs").join(format!("g{}", rng.below(3)));
    let absolute = absolute.to_str().expect("UTF-8");
    let values: [String; 22] = [
        "pkgs".into(),
        "./pkgs".into(),
        "../pkgs".into(),
        "a/../b".into(),
        "pkgs/".into(),
        "deep//er/./pkgs".into(),
        String::new(),
        "%BORZOI_GPF_A%".into(),
        "%BORZOI_GPF_A%/x".into(),
        "%BORZOI_GPF_B%/y".into(),
        "%BORZOI_GPF_UNSET%".into(),
        "%BORZOI_GPF_EMPTY%".into(),
        absolute.to_owned(),
        format!("{absolute}/"),
        format!("{absolute}/../h"),
        " pkgs".into(),
        "pk gs".into(),
        "c:pkgs".into(),
        "pk\\gs".into(),
        "~/pkgs".into(),
        "pkgs#1".into(),
        "%%".into(),
    ];
    // Bias towards values inside the domain.
    if rng.below(3) == 0 {
        rng.pick(&values).clone()
    } else {
        values[rng.below(15)].clone()
    }
}

/// One item of a `config`-like section, and whether NuGet throws on it. A
/// hostile spelling of the value adds its dimension to `hostile`.
fn gen_item(
    rng: &mut SplitMix64,
    base: &Path,
    mix: bool,
    hostile: &mut BTreeSet<Dimension>,
) -> (String, bool) {
    let key = *rng.pick(&[
        "globalPackagesFolder",
        "globalPackagesFolder",
        "globalPackagesFolder",
        "GlobalPackagesFolder",
        "GLOBALPACKAGESFOLDER",
        " globalPackagesFolder",
    ]);
    let value = gen_value(rng, base);
    // The generated values hold no markup, so each is its own plain
    // spelling, which a hostile one replaces.
    let drawn = if mix {
        xml::alphabet().sample(rng.next())
    } else {
        None
    };
    let spelt = drawn.and_then(|entry| {
        xml::spell(&value, entry.value, xml::Place::Attribute).map(|s| (entry.dimension, s.xml))
    });
    let (value, spelling) = match spelt {
        Some((dimension, spelt)) => (spelt, Some(dimension)),
        None => (value, None),
    };
    let item = match rng.below(80) {
        20..=21 => format!("<add value=\"{value}\" key=\"{key}\" />"),
        22..=23 => format!("<ADD key=\"{key}\" value=\"{value}\" />"),
        24..=25 => "<add key=\"repositoryPath\" value=\"repo\" />".to_owned(),
        26..=27 => "<clear />".to_owned(),
        28 => "<Clear/>".to_owned(),
        29..=30 => format!("<add key=\"{key}\" value=\"{value}\"></add>"),
        31 => "<!-- a comment -->".to_owned(),
        // Inside the vocabulary NuGet reads, outside the one modelled.
        32..=35 => match rng.below(3) {
            0 => format!("<add key=\"{key}\" value=\"{value}\" extra=\"1\" />"),
            1 => "<remove key=\"x\" />".to_owned(),
            _ => "loose text".to_owned(),
        },
        // NuGet throws: its attribute names are exact, and an `add` needs a
        // key and a value.
        36 => {
            if let Some(dimension) = spelling {
                hostile.insert(dimension);
            }
            return (format!("<add Key=\"{key}\" value=\"{value}\" />"), true);
        }
        37 => return (format!("<add key=\"{key}\" />"), true),
        _ => format!("<add key=\"{key}\" value=\"{value}\" />"),
    };
    // A spelling counts where the item keeps the value it spelt.
    if let Some(dimension) = spelling
        && item.contains(&format!("value=\"{value}\""))
    {
        hostile.insert(dimension);
    }
    (item, false)
}

/// A config file's bytes, and whether it holds something NuGet throws on in a
/// section the model does not read (a `Config`, or a `config` hidden by an
/// earlier section of that name in another case). The hostile spellings it
/// holds are added to `hostile`.
fn gen_config(
    rng: &mut SplitMix64,
    base: &Path,
    mix: bool,
    hostile: &mut BTreeSet<Dimension>,
) -> (Vec<u8>, bool) {
    // The spellings drawn into this file, which count only if the file keeps
    // them: a truncated one may not.
    let mut drawn = BTreeSet::new();
    // At most one fault per file, so most cases are clean enough to commit.
    let fault = if rng.below(16) == 0 {
        1 + rng.below(6)
    } else {
        0
    };
    let declaration = match fault {
        1 => *rng.pick(&[
            "<?xml version=\"1.0\" encoding=\"utf-16\"?>\n",
            "<?xml version=\"1.1\"?>\n",
        ]),
        _ => *rng.pick(&[
            "",
            "",
            "<?xml version=\"1.0\"?>\n",
            "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n",
            "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n",
        ]),
    };
    let root = if fault == 2 {
        "settings"
    } else {
        *rng.pick(&[
            "configuration",
            "configuration",
            "configuration",
            "Configuration",
            "CONFIGURATION",
        ])
    };
    let mut body = String::new();
    let mut unread_fault = false;
    let mut config_like = false;
    for _ in 0..rng.below(4) {
        match rng.below(7) {
            0 => body.push_str(
                "<packageSources><clear /><add key=\"local\" value=\"/nonexistent/feed\" /></packageSources>",
            ),
            1 => {
                let (item, throws) = gen_item(rng, base, mix, &mut drawn);
                unread_fault |= throws;
                config_like = true;
                body.push_str(&format!("<Config>{item}</Config>"));
            }
            _ => {
                body.push_str("<config>");
                for _ in 0..rng.below(5) {
                    let (item, throws) = gen_item(rng, base, mix, &mut drawn);
                    unread_fault |= throws && config_like;
                    body.push_str(&item);
                }
                body.push_str("</config>");
                config_like = true;
            }
        }
    }
    match fault {
        3 => body.push_str("<config foo=\"1\" /><config />"),
        4 => body.push_str("<x:config xmlns:x=\"urn:x\" />"),
        _ => {}
    }
    let mut text = format!("{declaration}<{root}>{body}</{root}>\n");
    if fault == 5 {
        let cut = rng.below(text.len());
        text.truncate(cut);
    } else {
        hostile.extend(drawn);
    }
    let mut bytes = Vec::new();
    if rng.below(6) == 0 {
        bytes.extend_from_slice(b"\xEF\xBB\xBF");
    }
    bytes.extend_from_slice(text.as_bytes());
    if fault == 6 {
        // Not UTF-8.
        bytes.push(0xff);
    }
    (bytes, unread_fault)
}

fn gen_case(rng: &mut SplitMix64, base: &Path, cli_home: bool) -> Case {
    // One case in `RATE` mixes hostile values in, each of its draws then
    // hostile at `RATE` again: drawn at every site of every case, nearly no
    // case would be the generator's own.
    let mix = rng.next().is_multiple_of(hostile::RATE);
    let draw = |rng: &mut SplitMix64| if mix { rng.next() } else { 1 };
    let mut hostile = BTreeSet::new();
    let mut placements = Vec::new();
    let mut unanswerable = None;
    let depth = rng.below(4);
    let mut folders = vec!["tree".to_owned()];
    for level in 0..=depth {
        let parent = folders.last().expect("a folder").clone();
        let component = match hostile::sample(walk_folder_names(), draw(rng)) {
            Some(entry) => {
                let rendered = entry.value.render("d", "");
                let text = rendered
                    .to_str()
                    .expect("a walk folder's name is text")
                    .to_owned();
                hostile.insert(entry.dimension);
                placements.push(Placement {
                    dir: parent.clone(),
                    name: rendered,
                    state: State::Directory,
                    content: Vec::new(),
                });
                text
            }
            None => format!("l{level}"),
        };
        folders.push(format!("{parent}/{component}"));
    }
    let root = folders.last().expect("a folder").clone();
    let mut files = Vec::new();
    let mut unread_fault = false;
    for folder in &folders {
        if rng.below(5) < 2 {
            if let Some(entry) = hostile::fs::alphabet().sample(draw(rng)) {
                // The folder's only file, under the spelling NuGet opens.
                let mut spellings = BTreeSet::new();
                let (bytes, fault) = gen_config(rng, base, mix, &mut spellings);
                if content_is_read(entry.value) {
                    unread_fault |= fault;
                    hostile.extend(spellings);
                }
                hostile.insert(entry.dimension);
                if entry.value == State::Fifo {
                    unanswerable = Some(OPENS_A_FIFO);
                }
                placements.push(Placement {
                    dir: folder.clone(),
                    name: opened_name(),
                    state: entry.value,
                    content: bytes,
                });
                continue;
            }
            let spelling = rng.pick(WALK_SPELLINGS);
            // Two spellings in one folder may be one file (the same pick, or
            // a volume that ignores case), the second written over the
            // first: neither then holds a hostile spelling, which the census
            // would count for bytes no reader saw.
            let two = rng.below(10) == 0;
            let (bytes, fault) = gen_config(rng, base, mix && !two, &mut hostile);
            unread_fault |= fault;
            files.push((format!("{folder}/{spelling}"), bytes));
            if two {
                let other = rng.pick(WALK_SPELLINGS);
                let (bytes, fault) = gen_config(rng, base, false, &mut hostile);
                unread_fault |= fault;
                files.push((format!("{folder}/{other}"), bytes));
            }
        }
    }
    let home = if cli_home { "cli-home" } else { "home" };
    // Mostly present: the model declines where there is no user config,
    // which NuGet would write.
    if rng.below(8) != 0 {
        // Mostly the spelling NuGet loads on every platform: on Linux the
        // other is no user config.
        let spelling = if rng.below(16) == 0 {
            "nuget.config"
        } else {
            "NuGet.Config"
        };
        let state = hostile::fs::alphabet().sample(draw(rng));
        let mut spellings = BTreeSet::new();
        let (bytes, fault) = gen_config(rng, base, mix, &mut spellings);
        match state {
            Some(entry) => {
                if content_is_read(entry.value) {
                    unread_fault |= fault;
                    hostile.extend(spellings);
                }
                hostile.insert(entry.dimension);
                if entry.value == State::Fifo {
                    unanswerable = Some(OPENS_A_FIFO);
                }
                placements.push(Placement {
                    dir: format!("{home}/.nuget/NuGet"),
                    name: opened_name(),
                    state: entry.value,
                    content: bytes,
                });
            }
            None => {
                unread_fault |= fault;
                hostile.extend(spellings);
                files.push((format!("{home}/.nuget/NuGet/{spelling}"), bytes));
            }
        }
    }
    // `read` is whether NuGet lists the folder at all on this platform. Of
    // its files NuGet loads those named `.config` in any case; the content of
    // another is read by no one, so its spellings are no draw and a fault in
    // it explains nothing NuGet throws.
    let mut listed =
        |folder: &str, read: bool, rng: &mut SplitMix64, hostile: &mut BTreeSet<Dimension>| {
            let loaded = |name: &[u8]| read && name.to_ascii_lowercase().ends_with(b".config");
            let mut names = BTreeSet::new();
            // At most one hostile name per folder: two may be one file to a file
            // system that folds case.
            let mut hostile_name = None;
            for _ in 0..=rng.below(3) {
                match name::alphabet().sample(draw(rng)) {
                    Some(entry) if hostile_name.is_none() && entry.value.varies("a", ".config") => {
                        hostile_name = Some((entry.dimension, entry.value.render("a", ".config")));
                    }
                    _ => {
                        names.insert(*rng.pick(LISTED_NAMES));
                    }
                }
            }
            for name in names {
                let mut spellings = BTreeSet::new();
                let (bytes, fault) = gen_config(rng, base, mix, &mut spellings);
                if loaded(name.as_bytes()) {
                    unread_fault |= fault;
                    hostile.extend(spellings);
                }
                files.push((format!("{folder}/{name}"), bytes));
            }
            if let Some((dimension, name)) = hostile_name {
                // Its content holds no hostile spelling: on a volume that ignores
                // case a listed name written after it may be the same file.
                let (bytes, fault) = gen_config(rng, base, false, &mut BTreeSet::new());
                unread_fault |= fault && loaded(name.bytes());
                hostile.insert(dimension);
                placements.push(Placement {
                    dir: folder.to_owned(),
                    name,
                    state: State::Regular,
                    content: bytes,
                });
            }
        };
    if rng.below(4) == 0 {
        listed(&listed_folder(home), true, rng, &mut hostile);
    }
    if rng.below(5) == 0 {
        // The machine-wide folder is here on Linux alone.
        listed(
            "common/NuGet/Config",
            cfg!(target_os = "linux"),
            rng,
            &mut hostile,
        );
    }
    let absolute = base.join("env-abs");
    let absolute = absolute.to_str().expect("UTF-8").to_owned();
    let nuget_packages = match rng.below(8) {
        0 => Some(absolute.clone() + "/np"),
        1 => Some(String::new()),
        2 => Some("relative/np".to_owned()),
        _ => None,
    };
    let a = match rng.below(4) {
        0 => None,
        1 => Some("rel/a".to_owned()),
        2 => Some(String::new()),
        _ => Some(absolute + "/a"),
    };
    let mut made = Vec::new();
    if rng.below(8) != 0 {
        made.push("home");
    }
    if rng.below(2) == 0 {
        made.push("cli-home");
    }
    let mut case = Case {
        files,
        unread_fault,
        folders: made,
        variables: vec![
            ("NUGET_PACKAGES", nuget_packages),
            ("BORZOI_GPF_A", a),
            ("BORZOI_GPF_B", Some("sub".to_owned())),
            ("BORZOI_GPF_EMPTY", Some(String::new())),
        ],
        root,
        placements,
        hostile,
        unanswerable,
        user_config: format!("{home}/.nuget/NuGet/NuGet.Config"),
    };
    if let Some(entry) = hostile::sample(request_environments(), draw(rng)) {
        case.hostile.insert(entry.dimension);
        for (name, value) in entry.value {
            case.set_variable(name, Some((*value).to_owned()));
        }
    }
    case
}

/// A config file whose `config` section sets the folder to `value` (written
/// as it is), with `between` around its item.
fn config_text(value: &str, between: &str) -> Vec<u8> {
    format!(
        "<configuration><config>{between}<add key=\"globalPackagesFolder\" value=\"{value}\" />\
         {between}</config></configuration>\n"
    )
    .into_bytes()
}

/// Where [`cover`] puts a hostile state: each place NuGet opens a config file.
#[derive(Debug, Clone, Copy)]
enum Where {
    /// The only file of a folder of the walk.
    Walk,
    /// The user config.
    User,
    /// A file in the user's additional config folder.
    Listed,
}

/// Every hostile value once: each file-system state at each place NuGet opens
/// a config file, each name as a listed file and as a folder of the walk,
/// each XML spelling of a value and of the text between items, and each
/// environment.
fn cover(census: &Census) {
    let mut harness = Harness::spawn(false);
    let mut tally = Tally::default();
    let one = |dimension: Dimension| BTreeSet::from([dimension]);

    for entry in hostile::fs::alphabet().entries() {
        for place in [Where::Walk, Where::User, Where::Listed] {
            let (dir, name) = match place {
                Where::Walk => ("tree/l0".to_owned(), opened_name()),
                Where::User => ("home/.nuget/NuGet".to_owned(), opened_name()),
                Where::Listed => (listed_folder("home"), plain("a", ".config")),
            };
            let mut case = Case {
                placements: vec![Placement {
                    dir,
                    name,
                    state: entry.value,
                    content: config_text("hostile-state", ""),
                }],
                hostile: one(entry.dimension),
                unanswerable: (entry.value == State::Fifo).then_some(OPENS_A_FIFO),
                ..Case::empty()
            };
            if matches!(place, Where::User) {
                case.files.clear();
            }
            run_case(&mut harness, census, &mut tally, &case);
        }
    }

    for entry in name::alphabet().entries() {
        // As a file in the folder NuGet lists, beside its twin where the file
        // system holds the two apart.
        if entry.value.varies("a", ".config") {
            let rendered = entry.value.render("a", ".config");
            let mut placements = vec![Placement {
                dir: listed_folder("home"),
                name: rendered.clone(),
                state: State::Regular,
                content: config_text("named", ""),
            }];
            let twin = entry.value.twin("a", ".config").filter(|twin| {
                match harness.hostile.holds_apart(&rendered, twin) {
                    Ok(()) => true,
                    Err(refusal) => {
                        census.unmakeable(&refusal);
                        false
                    }
                }
            });
            if let Some(twin) = twin {
                placements.push(Placement {
                    dir: listed_folder("home"),
                    name: twin,
                    state: State::Regular,
                    content: config_text("twin", ""),
                });
            }
            let case = Case {
                placements,
                hostile: one(entry.dimension),
                ..Case::empty()
            };
            run_case(&mut harness, census, &mut tally, &case);
        }
        // As a folder of the walk, holding the config file whose relative
        // value resolves under it.
        let rendered = entry.value.render("d", "");
        if let Some(text) = rendered.to_str().filter(|_| entry.value.varies("d", "")) {
            let mut case = Case {
                root: format!("tree/{text}/l1"),
                placements: vec![Placement {
                    dir: "tree".to_owned(),
                    name: rendered.clone(),
                    state: State::Directory,
                    content: Vec::new(),
                }],
                hostile: one(entry.dimension),
                ..Case::empty()
            };
            case.files
                .push((format!("tree/{text}/NuGet.Config"), config_text("pkgs", "")));
            run_case(&mut harness, census, &mut tally, &case);
        }
    }

    for entry in xml::alphabet().entries() {
        // The value, in its attribute; and the whitespace between the items,
        // which only an element's content can spell as a section or around a
        // comment.
        let value = xml::spell("p\tkgs", entry.value, xml::Place::Attribute)
            .map(|spelt| config_text(&spelt.xml, ""));
        let between = xml::spell("\n\t", entry.value, xml::Place::Element)
            .map(|spelt| config_text("pkgs", &spelt.xml));
        for bytes in [value, between].into_iter().flatten() {
            let case = Case {
                files: vec![(USER_CONFIG.to_owned(), bytes)],
                hostile: one(entry.dimension),
                ..Case::empty()
            };
            run_case(&mut harness, census, &mut tally, &case);
        }
    }

    for entry in env::alphabet().entries() {
        // A config value naming the first variable, so its value is read
        // however little NuGet makes of the variable itself.
        let (first, _) = entry.value[0];
        let mut case = Case {
            hostile: one(entry.dimension),
            ..Case::empty()
        };
        case.files.push((
            "tree/l0/NuGet.Config".to_owned(),
            config_text(&format!("%{first}%/sub"), ""),
        ));
        match own_oracle(entry) {
            None => {
                for (name, value) in entry.value {
                    case.set_variable(name, Some((*value).to_owned()));
                }
                run_case(&mut harness, census, &mut tally, &case);
            }
            Some((fixed, process)) => {
                // A hostile home is a path outside the test's tree: NuGet
                // would write its user config there (or, given a home it
                // cannot read, under the oracle's working folder), and the
                // test owns neither. The path is nowhere, so there is no
                // user config there for the model to read.
                for (name, value) in &fixed {
                    if matches!(*name, "HOME" | "DOTNET_CLI_HOME") {
                        assert!(
                            !Path::new(value).exists(),
                            "{value}, which the hostile environments name as nowhere, exists"
                        );
                        case.unanswerable = Some(
                            "NuGet's home is outside the test's tree, where the test owns \
                             nothing NuGet writes",
                        );
                    }
                }
                let mut own = Harness::spawn_with(false, &fixed, &process);
                run_case(&mut own, census, &mut tally, &case);
            }
        }
    }
    eprintln!("settings_diff cover: {tally:#?}");
}

/// What a sweep saw, for the non-vacuity floors and the tally it prints.
#[derive(Default, Debug)]
struct Tally {
    cases: usize,
    /// The cases of no hostile value that have a user config, and how many
    /// cases of no hostile value committed. That is the generator's own
    /// space where a commit is possible: most hostile values take a case out
    /// of the model's domain, and without a user config the model declines.
    plain_cases: usize,
    plain_committed: usize,
    environment: usize,
    config: usize,
    config_relative: usize,
    config_expanded: usize,
    config_beyond_first: usize,
    default: usize,
    many_files: usize,
    declined_nuget_threw: usize,
    declined_unanswerable: usize,
    unread_faults: usize,
    unmade: usize,
    nuget_threw: BTreeMap<String, usize>,
    declined_nuget_answered: BTreeMap<String, usize>,
}

/// Grade `case`, and record what became of it in the tally and the census.
fn run_case(harness: &mut Harness, census: &Census, tally: &mut Tally, case: &Case) {
    let (verdict, user_config) = grade(harness, case);
    let outcome = match &verdict {
        Verdict::Unmade(refusal) => {
            tally.unmade += 1;
            census.unmakeable(refusal);
            return;
        }
        Verdict::Committed(_) => "commit",
        Verdict::CommittedWhereNuGetThrewOnAnUnreadSection => "commit where NuGet threw elsewhere",
        Verdict::Declined {
            nuget_threw: None, ..
        } => "decline",
        Verdict::Declined {
            nuget_threw: Some(_),
            ..
        } => "decline where NuGet threw",
        Verdict::DeclinedUnanswerable => "decline where NuGet has no answer",
    };
    census.reached(&case.hostile, outcome);
    tally.cases += 1;
    if case.hostile.is_empty() {
        tally.plain_cases += usize::from(user_config);
        tally.plain_committed += usize::from(matches!(verdict, Verdict::Committed(_)));
    }
    match verdict {
        Verdict::Committed(committed) => {
            if committed.config_files.len() >= 3 {
                tally.many_files += 1;
            }
            match &committed.origin {
                FolderOrigin::Environment => tally.environment += 1,
                FolderOrigin::Default => tally.default += 1,
                FolderOrigin::Config { file } => {
                    tally.config += 1;
                    if !committed.folder.starts_with(harness.base.join("abs"))
                        && !committed.folder.starts_with(harness.base.join("env-abs"))
                    {
                        tally.config_relative += 1;
                    }
                    if committed.folder.starts_with(harness.base.join("env-abs"))
                        || committed.folder.ends_with("sub/y")
                    {
                        tally.config_expanded += 1;
                    }
                    if Some(file) != committed.config_files.first() {
                        tally.config_beyond_first += 1;
                    }
                }
            }
        }
        Verdict::CommittedWhereNuGetThrewOnAnUnreadSection => tally.unread_faults += 1,
        Verdict::DeclinedUnanswerable => tally.declined_unanswerable += 1,
        Verdict::Unmade(_) => unreachable!("returned above"),
        Verdict::Declined {
            decline,
            nuget_threw,
        } => match nuget_threw {
            None => {
                let kind = match &decline {
                    GlobalPackagesFolderDecline::ConfigFile { decline, .. } => {
                        let reason = decline.to_string();
                        format!(
                            "ConfigFile: {}",
                            reason.chars().take(50).collect::<String>()
                        )
                    }
                    other => {
                        let kind = format!("{other:?}");
                        kind.split([' ', '{', '(']).next().unwrap_or("").to_owned()
                    }
                };
                *tally.declined_nuget_answered.entry(kind).or_default() += 1;
            }
            Some(threw) => {
                tally.declined_nuget_threw += 1;
                *tally.nuget_threw.entry(threw).or_default() += 1;
            }
        },
    }
}

fn sweep(census: &Census, seed: u64, cases: usize, cli_home: bool) -> Tally {
    let mut harness = Harness::spawn(cli_home);
    let mut rng = SplitMix64(seed);
    let mut tally = Tally::default();
    for _ in 0..cases {
        let case = gen_case(&mut rng, &harness.base.clone(), cli_home);
        run_case(&mut harness, census, &mut tally, &case);
    }
    eprintln!("settings_diff tally (seed {seed}, cli_home {cli_home}): {tally:#?}");
    tally
}

fn cases(default: usize) -> usize {
    std::env::var("BORZOI_SETTINGS_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(default)
}

fn assert_floors(tally: &Tally) {
    assert!(
        tally.plain_committed * 3 >= tally.plain_cases,
        "fewer than a third of the cases of no hostile value and with a user config committed: {tally:#?}"
    );
    for (what, count) in [
        ("from NUGET_PACKAGES", tally.environment),
        ("from a config file", tally.config),
        ("from a relative value", tally.config_relative),
        ("from an expanded value", tally.config_expanded),
        (
            "from a file other than the most significant",
            tally.config_beyond_first,
        ),
        ("from the default", tally.default),
        ("over three or more config files", tally.many_files),
        ("where NuGet threw", tally.declined_nuget_threw),
    ] {
        assert!(count > 0, "no case graded {what}: {tally:#?}");
    }
}

/// The cover and the sweeps, each sweep held to its floors, with the census
/// of hostile values finished over all of them.
fn run(sweeps: &[(u64, usize, bool)]) {
    let census = hostile::coverage::open(file!(), CENSUS, &[]);
    cover(&census);
    for &(seed, cases, cli_home) in sweeps {
        assert_floors(&sweep(&census, seed, cases, cli_home));
    }
    census.finish(REGENERATE);
}

#[test]
fn global_packages_folder_matches_nuget() {
    run(&[
        (0x5e77_1465, cases(300), false),
        (0xc11_4093, cases(150), true),
    ]);
}

#[test]
#[ignore = "deep sweep; run with --ignored"]
fn deep_global_packages_folder_matches_nuget() {
    run(&[
        (1, cases(3000), false),
        (2, cases(3000), true),
        (3, cases(3000), false),
    ]);
}
