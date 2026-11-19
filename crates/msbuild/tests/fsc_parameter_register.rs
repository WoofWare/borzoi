//! The register of what reaches fsc ([`borzoi_msbuild::fsc::FSC_PARAMETERS`],
//! [`borzoi_msbuild::fsc::BUILD_TIME_SITES`]) held to each verified SDK's own
//! targets, so a parameter or an item source nobody accounted for fails here
//! rather than in review.
//!
//! - The SDK invokes fsc once, in `FSharp/Microsoft.FSharp.Targets` (no other
//!   file of it invokes `Fsc`, bare, qualified or registered under another
//!   name), and every parameter that invocation passes is a row, with the row's whole
//!   expression, fed as the row says: by the
//!   item types its value names (`@(…)`, and then it names no property), else
//!   the properties (`$(…)`), else a literal; and every row is a parameter.
//! - Every write a `.targets` or `.props` file of the SDK makes, inside a
//!   `<Target>`, to one of those item types or properties (an item element in
//!   an `<ItemGroup>`, a property element in a `<PropertyGroup>`, or a task's
//!   `<Output ItemName|PropertyName>`) is a site, and every site is such a
//!   write: each with its whole expression (an item's every attribute and
//!   metadata element; a task output's task and inputs) and every condition
//!   it runs under (its target's, its group's or task's, its own), counted, so a second
//!   write in a target the register already names is a new site. A computed
//!   name (holding `%(`, `$(` or `@(`) may stand for any, so it counts for
//!   every one.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use borzoi_msbuild::document::{self, attribute, parse};
use borzoi_msbuild::fsc::{BUILD_TIME_SITES, FSC_PARAMETERS, Feed, SiteKind, verified_sdks};
use borzoi_msbuild::observed::host_fs::{self, HostPath};

/// The version directory of each verified SDK.
fn verified_sdk_dirs() -> Vec<PathBuf> {
    let sdks = common::dotnet_root_from_env().join("sdk");
    verified_sdks()
        .map(|version| {
            let dir = sdks.join(version);
            assert!(
                dir.join("FSharp").host_is_dir(),
                "the verified SDK {version} is not installed under {}",
                sdks.display()
            );
            dir
        })
        .collect()
}

/// The names `value` references with `open` (`@(` or `$(`), in order.
fn referenced(value: &str, open: &str) -> Vec<String> {
    value
        .match_indices(open)
        .map(|(at, _)| {
            value[at + open.len()..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '-')
                .collect::<String>()
        })
        .filter(|name| !name.is_empty())
        .collect()
}

fn text(path: &Path) -> String {
    let text = host_fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    text.trim_start_matches('\u{feff}').to_string()
}

/// Whether the element name `tag` invokes the task `task` (case aside),
/// spelt bare or namespace-qualified (`Microsoft.FSharp.Build.Fsc`).
fn names_task(tag: &str, task: &str) -> bool {
    tag.rsplit('.')
        .next()
        .is_some_and(|last| last.eq_ignore_ascii_case(task))
}

/// The `<Fsc>` invocation's parameters in the SDK at `sdk`: name to value.
/// Every `.targets` and `.props` file of the SDK is searched for an element
/// invoking `Fsc`, or a task a `<UsingTask>` registers under a name ending in
/// `Fsc`, and there must be exactly one, in `FSharp/Microsoft.FSharp.Targets`.
fn fsc_parameters(sdk: &Path) -> BTreeMap<String, String> {
    let mut files = Vec::new();
    msbuild_files(sdk, &mut files);
    let texts: Vec<(PathBuf, String)> = files
        .into_iter()
        .map(|f| {
            let t = text(&f);
            (f, t)
        })
        .collect();
    let docs: Vec<(&Path, roxmltree::Document<'_>)> = texts
        .iter()
        .map(|(file, text)| {
            let doc = parse(text).unwrap_or_else(|e| panic!("{}: unscanned: {e}", file.display()));
            (file.as_path(), doc)
        })
        .collect();
    let mut tasks: BTreeSet<String> = BTreeSet::from(["fsc".to_string()]);
    for (_, doc) in &docs {
        for using in doc
            .descendants()
            .filter(|n| n.is_element() && n.tag_name().name().eq_ignore_ascii_case("UsingTask"))
        {
            if let Some(name) = attribute(using, "TaskName").filter(|n| names_task(n, "Fsc")) {
                tasks.insert(name.rsplit('.').next().unwrap().to_ascii_lowercase());
            }
        }
    }
    let invocations: Vec<_> = docs
        .iter()
        .flat_map(|(file, doc)| {
            doc.descendants()
                .filter(|n| {
                    n.is_element()
                        && !n.tag_name().name().eq_ignore_ascii_case("UsingTask")
                        && tasks
                            .iter()
                            .any(|task| names_task(n.tag_name().name(), task))
                })
                .map(move |n| (*file, n))
        })
        .collect();
    let expected = sdk.join("FSharp").join("Microsoft.FSharp.Targets");
    assert!(
        invocations.len() == 1 && invocations[0].0 == expected,
        "{}: one <Fsc> invocation, in {}; found {:?}",
        sdk.display(),
        expected.display(),
        invocations
            .iter()
            .map(|(file, n)| format!("{} {}", file.display(), n.tag_name().name()))
            .collect::<Vec<_>>()
    );
    parameters_of(invocations[0].1)
}

/// The parameters of the invocation `fsc`, name to value as MSBuild reads it
/// (a literal tab or line break kept, where `roxmltree` makes it a space).
fn parameters_of(fsc: roxmltree::Node<'_, '_>) -> BTreeMap<String, String> {
    fsc.attributes()
        .filter(|a| a.name() != "Condition")
        .map(|a| {
            let value = attribute(fsc, a.name()).expect("an attribute of its own node");
            (a.name().to_string(), value.into_owned())
        })
        .collect()
}

/// A parameter's literal line break is part of what fsc receives, so the
/// register reads it as MSBuild does.
#[test]
fn parameters_are_read_as_msbuild_reads_them() {
    let text = "<Project><Target Name=\"T\"><Fsc A=\"x\ny\" Condition=\"c\" /></Target></Project>";
    let doc = parse(text).unwrap();
    let fsc = doc
        .descendants()
        .find(|n| n.tag_name().name() == "Fsc")
        .unwrap();
    assert_eq!(
        parameters_of(fsc),
        BTreeMap::from([("A".to_string(), "x\ny".to_string())])
    );
}

/// The feed the value `value` names.
fn feed_of(value: &str) -> (Vec<String>, Vec<String>) {
    (referenced(value, "@("), referenced(value, "$("))
}

/// Every `.targets` and `.props` file under `dir`.
fn msbuild_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in host_fs::read_dir(dir).unwrap_or_else(|e| panic!("{}: {e}", dir.display())) {
        let path = entry.unwrap().path();
        if path.host_is_dir() {
            msbuild_files(&path, out);
        } else {
            let lower = path.to_string_lossy().to_ascii_lowercase();
            if lower.ends_with(".targets") || lower.ends_with(".props") {
                out.push(path);
            }
        }
    }
}

/// `(kind, name, file, target, write, conditions)`, as a [`BUILD_TIME_SITES`]
/// row spells them.
type Site = (&'static str, String, String, String, String, Vec<String>);

/// A write as the scan finds it: `(kind, name, target, write, conditions)`,
/// the write `None` for a property value the scan cannot read.
type Write = (&'static str, String, String, Option<String>, Vec<String>);

/// The folded conditions among `conditions`, outermost first, empty ones left
/// out.
fn chain(conditions: &[String]) -> Vec<String> {
    conditions
        .iter()
        .filter(|c| !c.is_empty())
        .cloned()
        .collect()
}

/// `text` exactly: MSBuild hands a task the decoded value as written, and
/// fsc reads a response file a line at a time, so no whitespace in a value is
/// insignificant to the register.
fn fold(text: &str) -> String {
    text.to_string()
}

/// The value of `node`'s attribute `name` as MSBuild decodes it, empty when
/// it has none.
fn folded_attribute(node: roxmltree::Node<'_, '_>, name: &str) -> String {
    attribute(node, name).map_or_else(String::new, |value| fold(&value))
}

/// An item element's write, everything it says but its condition: its
/// operation and value (`Include=@(__Sources)`), then its other attributes
/// sorted by name (` KeepDuplicates=false`), then each metadata element in
/// order (` <Link>=x`, with ` if <condition>` when it has one), all folded.
/// `None` when a metadata element holds anything but text.
fn item_write(item: roxmltree::Node<'_, '_>) -> Option<String> {
    let operation = ["Include", "Remove", "Update"]
        .into_iter()
        .find(|op| attribute(item, op).is_some());
    let mut parts: Vec<String> = operation
        .map(|op| format!("{op}={}", folded_attribute(item, op)))
        .into_iter()
        .collect();
    let mut others: Vec<(String, String)> = item
        .attributes()
        .filter(|a| Some(a.name()) != operation && a.name() != "Condition")
        .map(|a| (a.name().to_string(), folded_attribute(item, a.name())))
        .collect();
    others.sort_by_key(|(name, _)| name.to_ascii_lowercase());
    parts.extend(
        others
            .into_iter()
            .map(|(name, value)| format!("{name}={value}")),
    );
    for metadata in item.children().filter(roxmltree::Node::is_element) {
        let mut part = format!(
            "<{}>={}",
            metadata.tag_name().name(),
            property_write(metadata)?
        );
        let condition = folded_attribute(metadata, "Condition");
        if !condition.is_empty() {
            part.push_str(&format!(" if {condition}"));
        }
        parts.push(part);
    }
    Some(parts.join(" "))
}

/// A task output's write: the task and every input but its condition, sorted
/// by name, then the output parameter
/// (`CreateItem(Include=@(_ProcessedContentItems)) Output=Include`), all
/// folded. The inputs are what justify the output's gate.
fn task_write(task: roxmltree::Node<'_, '_>, output: roxmltree::Node<'_, '_>) -> String {
    let mut inputs: Vec<(String, String)> = task
        .attributes()
        .filter(|a| a.name() != "Condition")
        .map(|a| (a.name().to_string(), folded_attribute(task, a.name())))
        .collect();
    inputs.sort_by_key(|(name, _)| name.to_ascii_lowercase());
    let inputs: Vec<String> = inputs
        .into_iter()
        .map(|(name, value)| format!("{name}={value}"))
        .collect();
    format!(
        "{}({}) Output={}",
        task.tag_name().name(),
        inputs.join(", "),
        folded_attribute(output, "TaskParameter")
    )
}

/// A property element's value, folded; `None` when it holds anything but text,
/// which the scan cannot read.
fn property_write(property: roxmltree::Node<'_, '_>) -> Option<String> {
    let mut value = String::new();
    for child in property.children() {
        value.push_str(&document::text(child)?);
    }
    Some(fold(&value))
}

/// Every build-time write under `node`, in the target `target` (its name and
/// folded condition).
fn writes(node: roxmltree::Node<'_, '_>, target: Option<(&str, &str)>, out: &mut Vec<Write>) {
    let name = (node.tag_name().name() == "Target").then(|| attribute(node, "Name"));
    let condition = folded_attribute(node, "Condition");
    let target = match &name {
        Some(name) => name.as_deref().map(|name| (name, condition.as_str())),
        None => target,
    };
    for child in node.children().filter(roxmltree::Node::is_element) {
        if let Some((target, target_condition)) = target {
            let group_condition = folded_attribute(child, "Condition");
            match child.tag_name().name() {
                "ItemGroup" => {
                    for item in child.children().filter(roxmltree::Node::is_element) {
                        out.push((
                            "Item",
                            item.tag_name().name().to_string(),
                            target.to_string(),
                            item_write(item),
                            chain(&[
                                target_condition.to_string(),
                                group_condition.clone(),
                                folded_attribute(item, "Condition"),
                            ]),
                        ));
                    }
                }
                "PropertyGroup" => {
                    for property in child.children().filter(roxmltree::Node::is_element) {
                        out.push((
                            "Property",
                            property.tag_name().name().to_string(),
                            target.to_string(),
                            property_write(property),
                            chain(&[
                                target_condition.to_string(),
                                group_condition.clone(),
                                folded_attribute(property, "Condition"),
                            ]),
                        ));
                    }
                }
                "Output" => {
                    // `node` is the task the output belongs to.
                    let write = Some(task_write(node, child));
                    // `node` is the task the output belongs to.
                    let condition = chain(&[
                        target_condition.to_string(),
                        folded_attribute(node, "Condition"),
                        folded_attribute(child, "Condition"),
                    ]);
                    if let Some(name) = attribute(child, "ItemName") {
                        out.push((
                            "Item",
                            name.to_string(),
                            target.to_string(),
                            write.clone(),
                            condition.clone(),
                        ));
                    }
                    if let Some(name) = attribute(child, "PropertyName") {
                        out.push((
                            "Property",
                            name.to_string(),
                            target.to_string(),
                            write,
                            condition,
                        ));
                    }
                }
                _ => {}
            }
        }
        writes(child, target, out);
    }
}

#[test]
fn every_fsc_parameter_is_registered_as_the_sdk_feeds_it() {
    let mut failures = Vec::new();
    for sdk in verified_sdk_dirs() {
        let parameters = fsc_parameters(&sdk);
        for (name, value) in &parameters {
            let Some(row) = FSC_PARAMETERS.iter().find(|row| row.name == name) else {
                failures.push(format!(
                    "{}: `{name}=\"{value}\"` has no row",
                    sdk.display()
                ));
                continue;
            };
            if fold(value) != row.expression {
                failures.push(format!(
                    "{}: `{name}=\"{value}\"`, but the row's expression is `{}`",
                    sdk.display(),
                    row.expression
                ));
            }
            let (items, properties) = feed_of(value);
            let fed_as = match row.feed {
                Feed::Literal => items.is_empty() && properties.is_empty(),
                Feed::Items(types) => !items.is_empty() && items == types && properties.is_empty(),
                Feed::Properties(names) => items.is_empty() && properties == names,
            };
            if !fed_as {
                failures.push(format!(
                    "{}: `{name}=\"{value}\"` is not fed as its row says ({:?})",
                    sdk.display(),
                    row.feed
                ));
            }
        }
        for row in FSC_PARAMETERS {
            if !parameters.contains_key(row.name) {
                failures.push(format!(
                    "{}: the row `{}` is no parameter",
                    sdk.display(),
                    row.name
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn every_build_time_source_of_a_parameter_is_registered() {
    let fed_items: BTreeSet<String> = FSC_PARAMETERS
        .iter()
        .flat_map(|row| match row.feed {
            Feed::Items(types) => types.to_vec(),
            _ => Vec::new(),
        })
        .map(str::to_ascii_lowercase)
        .collect();
    let fed_properties: BTreeSet<String> = FSC_PARAMETERS
        .iter()
        .flat_map(|row| match row.feed {
            Feed::Properties(names) => names.to_vec(),
            _ => Vec::new(),
        })
        .map(str::to_ascii_lowercase)
        .collect();
    let mut registered: BTreeMap<Site, usize> = BTreeMap::new();
    for site in BUILD_TIME_SITES.iter().map(|site| {
        let kind = match site.kind {
            SiteKind::Item => "Item",
            SiteKind::Property => "Property",
        };
        (
            kind,
            site.name.to_string(),
            site.file.to_string(),
            site.target.to_string(),
            site.write.to_string(),
            site.conditions.iter().map(|c| c.to_string()).collect(),
        )
    }) {
        *registered.entry(site).or_default() += 1;
    }
    let mut failures = Vec::new();
    for sdk in verified_sdk_dirs() {
        let mut files = Vec::new();
        msbuild_files(&sdk, &mut files);
        let mut found: BTreeMap<Site, usize> = BTreeMap::new();
        for file in files {
            let text = text(&file);
            // A file the scan cannot read could hold a site.
            let doc = match parse(&text) {
                Ok(doc) => doc,
                Err(e) => {
                    failures.push(format!("{}: unscanned: {e}", file.display()));
                    continue;
                }
            };
            let relative = file
                .strip_prefix(&sdk)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            let mut out = Vec::new();
            writes(doc.root(), None, &mut out);
            for (kind, name, target, write, condition) in out {
                let computed = name.contains(['%', '$', '@']);
                let fed = match kind {
                    "Item" => fed_items.contains(&name.to_ascii_lowercase()),
                    _ => fed_properties.contains(&name.to_ascii_lowercase()),
                };
                if fed || computed {
                    // A value the scan cannot read could be any write.
                    let Some(write) = write else {
                        failures.push(format!(
                            "{}: unscanned: the value of `{name}` in `{target}`",
                            file.display()
                        ));
                        continue;
                    };
                    *found
                        .entry((kind, name, relative.clone(), target, write, condition))
                        .or_default() += 1;
                }
            }
        }
        for (site, count) in &found {
            let rows = registered.get(site).copied().unwrap_or(0);
            if rows < *count {
                failures.push(format!(
                    "{}: unregistered site ({count} writes, {rows} rows) {site:?}",
                    sdk.display()
                ));
            }
        }
        for (site, rows) in &registered {
            let count = found.get(site).copied().unwrap_or(0);
            if count < *rows {
                failures.push(format!(
                    "{}: a registered site the SDK has no more ({count} writes, {rows} rows): {site:?}",
                    sdk.display()
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
