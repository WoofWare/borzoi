//! MSBuild's loader schema (#888, #917): a port of `ProjectParser`, the pass
//! that turns a file's XML into project elements before anything in it is
//! evaluated, and refuses the whole project for a file it cannot parse,
//! whatever any condition in the file holds.
//!
//! [`first_violation`] walks a file's root as `ProjectParser.Parse` does and
//! returns the first rule it breaks. Names are read as `XmlDocument` reads
//! them, the prefix included (a start tag's qualified name, and its
//! attributes', namespace declarations among them), which `roxmltree` does
//! not hand out, so they come from the start tag's source text.
//!
//! **Relaxable rules.** A newer MSBuild skips an unrecognised attribute or
//! child that a `Directory.Parse.config` above the project, or the files
//! `MSBUILD_PARSE_CONFIG` names, list (`ParserIgnoreConfiguration`). Neither
//! SDK 10 nor SDK 11 reads them (probed), but such a violation is marked
//! [`Violation::relaxable`], and [`first_violation`] with `relax` skips every
//! one, as the most permissive configuration would: the rejection judgement
//! claims a relaxable violation only where no configuration can apply.
//!
//! **Doubt.** A rule the port reads only approximately (CDATA it cannot find
//! in the source, an item definition's metadatum that may name an item list)
//! gives a violation that is not [`Violation::sure`].
//!
//! The differential `fsproj_property_table_diff`'s loader schema sweep puts
//! every element MSBuild parses through every attribute and child of a table
//! against the oracle.

use std::ops::Range;

use roxmltree::Node;

use crate::LoadTimeError;
use crate::document::attribute;
use crate::properties::escaping;

use super::is_msbuild_reserved_name;

/// A rule of the loader a file breaks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Violation {
    pub(super) error: LoadTimeError,
    pub(super) span: Range<usize>,
    /// A newer MSBuild's parse configuration may skip it.
    pub(super) relaxable: bool,
    /// The port is sure MSBuild refuses it.
    pub(super) sure: bool,
}

/// The first rule of MSBuild's loader that the file whose root element is
/// `root` breaks. With `relax`, every relaxable violation is skipped, an
/// unrecognised child with all it holds. A file that breaks none but keeps
/// whitespace ([`whitespace_kept`]) may yet be refused.
pub(super) fn first_violation(root: Node<'_, '_>, relax: bool) -> Option<Violation> {
    let mut loader = Loader {
        relax,
        seen_extensions: false,
    };
    loader.root(root).err().or_else(|| whitespace_kept(root))
}

/// Doubt over a file whose root asks for whitespace to be kept, by an
/// `xml:space` attribute that is not `default`. Under `preserve` the reader
/// reports whitespace as significant, which every rule above takes for
/// skippable: MSBuild then refuses whitespace between elements (MSB4067, an
/// unrecognised `<#significant-whitespace>`), and evaluates a file without
/// any keeping the whitespace in its bodies (`dotnet msbuild` 10.0). Neither
/// is modelled, so the violation is never sure.
fn whitespace_kept(root: Node<'_, '_>) -> Option<Violation> {
    let space = crate::document::xml_space(root).filter(|a| a.value() != "default")?;
    Some(Violation {
        error: LoadTimeError::WhitespaceKept,
        span: space.range(),
        relaxable: false,
        sure: false,
    })
}

/// The deepest `<Choose>` nesting MSBuild loads (`MaximumChooseNesting`).
const MAXIMUM_CHOOSE_NESTING: usize = 50;

/// The names MSBuild reserves for its own elements, which no property, item
/// type or metadatum may take (`XMakeElements.ReservedItemNames`, ordinal).
const RESERVED_ELEMENT_NAMES: [&str; 12] = [
    "VisualStudioProject",
    "Target",
    "PropertyGroup",
    "Output",
    "ItemGroup",
    "UsingTask",
    "ProjectExtensions",
    "OnError",
    "ImportGroup",
    "Choose",
    "When",
    "Otherwise",
];

/// The item-spec modifiers, which no metadatum may be named for, in any case
/// (`ItemSpecModifiers.IsItemSpecModifier`).
const ITEM_SPEC_MODIFIERS: [&str; 15] = [
    "FullPath",
    "RootDir",
    "Filename",
    "Extension",
    "RelativeDir",
    "Directory",
    "RecursiveDir",
    "Identity",
    "ModifiedTime",
    "CreatedTime",
    "AccessedTime",
    "DefiningProjectFullPath",
    "DefiningProjectDirectory",
    "DefiningProjectName",
    "DefiningProjectExtension",
];

/// The attributes an item takes besides metadata (`KnownAttributesOnItem`).
const ITEM_ATTRIBUTES: [&str; 11] = [
    "Condition",
    "Label",
    "Include",
    "Exclude",
    "Remove",
    "KeepMetadata",
    "RemoveMetadata",
    "KeepDuplicates",
    "Update",
    "MatchOnMetadata",
    "MatchOnMetadataOptions",
];

const CONDITION_AND_LABEL: &[&str] = &["Condition", "Label"];
const IMPORT_ATTRIBUTES: &[&str] = &[
    "Condition",
    "Label",
    "Project",
    "Sdk",
    "Version",
    "MinimumVersion",
];
const USING_TASK_ATTRIBUTES: &[&str] = &[
    "Condition",
    "Label",
    "TaskName",
    "AssemblyFile",
    "AssemblyName",
    "TaskFactory",
    "Architecture",
    "Runtime",
    "RequiredPlatform",
    "RequiredRuntime",
    "Override",
];
const TARGET_ATTRIBUTES: &[&str] = &[
    "Condition",
    "Label",
    "Name",
    "Inputs",
    "Outputs",
    "KeepDuplicateOutputs",
    "DependsOnTargets",
    "BeforeTargets",
    "AfterTargets",
    "Returns",
];
const ON_ERROR_ATTRIBUTES: &[&str] = &["Condition", "Label", "ExecuteTargets"];
const OUTPUT_ATTRIBUTES: &[&str] = &[
    "Condition",
    "Label",
    "TaskParameter",
    "ItemName",
    "PropertyName",
];
const PARAMETER_ATTRIBUTES: &[&str] = &["ParameterType", "Output", "Required"];
const TASK_BODY_ATTRIBUTES: &[&str] = &["Evaluate"];
/// A task's attributes MSBuild refuses in any case but their own
/// (`IsBadlyCasedSpecialTaskAttribute`).
const SPECIAL_TASK_ATTRIBUTES: &[&str] = &[
    "Condition",
    "ContinueOnError",
    "MSBuildRuntime",
    "MSBuildArchitecture",
    "xmlns",
];

type Parsed = Result<(), Violation>;

struct Loader {
    relax: bool,
    seen_extensions: bool,
}

/// An element's or attribute's name as `XmlDocument` reads it.
fn qname<'input>(node: Node<'_, 'input>) -> &'input str {
    let source = node.document().input_text();
    let tag = &source[node.range().start + 1..];
    let end = tag
        .find(|c: char| c.is_ascii_whitespace() || c == '/' || c == '>')
        .unwrap_or(tag.len());
    &tag[..end]
}

/// The qualified names of the attributes in `node`'s start tag, namespace
/// declarations included, read from the source (`roxmltree` checked it is
/// well formed).
fn attribute_names<'input>(node: Node<'_, 'input>) -> Vec<&'input str> {
    let source = node.document().input_text();
    let tag = &source[node.range().start + 1..];
    let mut at = qname(node).len();
    let bytes = tag.as_bytes();
    let mut names = Vec::new();
    loop {
        while at < bytes.len() && bytes[at].is_ascii_whitespace() {
            at += 1;
        }
        if at >= bytes.len() || bytes[at] == b'/' || bytes[at] == b'>' {
            return names;
        }
        let start = at;
        while at < bytes.len() && !bytes[at].is_ascii_whitespace() && bytes[at] != b'=' {
            at += 1;
        }
        names.push(&tag[start..at]);
        while at < bytes.len() && bytes[at] != b'"' && bytes[at] != b'\'' {
            at += 1;
        }
        let Some(&quote) = bytes.get(at) else {
            return names;
        };
        at += 1;
        while at < bytes.len() && bytes[at] != quote {
            at += 1;
        }
        at += 1;
    }
}

/// `XmlUtilities.IsValidElementName`: ASCII letters and `_`, then also digits
/// and `-`.
pub(crate) fn is_valid_name(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn is_reserved_element_name(name: &str) -> bool {
    RESERVED_ELEMENT_NAMES.contains(&name)
}

fn is_item_spec_modifier(name: &str) -> bool {
    ITEM_SPEC_MODIFIERS
        .iter()
        .any(|m| m.eq_ignore_ascii_case(name))
}

/// `element`'s attribute `name` as `GetAttribute` reads it: empty when absent.
fn value_of(element: Node<'_, '_>, name: &str) -> String {
    attribute(element, name)
        .map(|v| v.into_owned())
        .unwrap_or_default()
}

fn has(element: Node<'_, '_>, name: &str) -> bool {
    attribute_names(element).contains(&name)
}

fn violation(error: LoadTimeError, node: Node<'_, '_>) -> Violation {
    Violation {
        error,
        span: node.range(),
        relaxable: false,
        sure: true,
    }
}

fn malformed(element: Node<'_, '_>, rule: &'static str) -> Violation {
    violation(
        LoadTimeError::Malformed {
            element: qname(element).to_owned(),
            rule,
        },
        element,
    )
}

impl Loader {
    /// `Err` of a relaxable `v`, unless relaxing.
    fn relaxable(&self, mut v: Violation) -> Parsed {
        v.relaxable = true;
        if self.relax { Ok(()) } else { Err(v) }
    }

    /// `VerifyThrowProjectAttributes`: every attribute of `element` is one of
    /// `valid`.
    fn attributes(&self, element: Node<'_, '_>, valid: &[&str]) -> Parsed {
        for name in attribute_names(element) {
            if !valid.contains(&name) {
                self.unrecognized_attribute(element, name)?;
            }
        }
        Ok(())
    }

    fn unrecognized_attribute(&self, element: Node<'_, '_>, name: &str) -> Parsed {
        self.relaxable(violation(
            LoadTimeError::UnrecognizedAttribute {
                element: qname(element).to_owned(),
                attribute: name.to_owned(),
            },
            element,
        ))
    }

    /// `Err` for `child`, a child `parent` does not take, unless relaxing.
    fn unrecognized_child(&self, parent: Node<'_, '_>, child: Node<'_, '_>) -> Parsed {
        self.relaxable(violation(
            LoadTimeError::UnrecognizedChild {
                parent: qname(parent).to_owned(),
                child: qname(child).to_owned(),
            },
            child,
        ))
    }

    /// `GetVerifyThrowProjectChildElements`: `element`'s child elements, after
    /// checking that the rest of its content is comments and whitespace (by
    /// `String.IsNullOrWhiteSpace`, whose classification is Rust's).
    fn children<'a, 'input>(
        &self,
        element: Node<'a, 'input>,
    ) -> Result<Vec<Node<'a, 'input>>, Violation> {
        let mut elements = Vec::new();
        for child in element.children() {
            if child.is_element() {
                elements.push(child);
            } else if child.is_text() {
                let stray = |name: &str, sure: bool| Violation {
                    error: LoadTimeError::UnrecognizedChild {
                        parent: qname(element).to_owned(),
                        child: name.to_owned(),
                    },
                    span: child.range(),
                    relaxable: false,
                    sure,
                };
                match crate::document::text(child) {
                    Some(text) if text.chars().all(char::is_whitespace) => {}
                    Some(_) => return Err(stray("#text", true)),
                    None => {
                        return Err(stray("#cdata-section", holds_cdata(child)));
                    }
                }
            } else if child.is_pi() {
                let target = child.pi().map(|pi| pi.target).unwrap_or_default();
                return Err(Violation {
                    error: LoadTimeError::UnrecognizedChild {
                        parent: qname(element).to_owned(),
                        child: target.to_owned(),
                    },
                    span: child.range(),
                    relaxable: false,
                    sure: true,
                });
            }
        }
        Ok(elements)
    }

    /// `VerifyThrowProjectNoChildElements`.
    fn no_children(&self, element: Node<'_, '_>) -> Parsed {
        for child in self.children(element)? {
            self.unrecognized_child(element, child)?;
        }
        Ok(())
    }

    fn required(&self, element: Node<'_, '_>, name: &str, rule: &'static str) -> Parsed {
        if value_of(element, name).is_empty() {
            return Err(malformed(element, rule));
        }
        Ok(())
    }

    fn root(&mut self, root: Node<'_, '_>) -> Parsed {
        // The root takes any attribute; its name and namespace are the
        // reader's business (a project the walk reads at all is `Project`).
        for child in self.children(root)? {
            match qname(child) {
                "PropertyGroup" => self.property_group(child)?,
                "ItemGroup" => self.item_group(child, false)?,
                "ImportGroup" => self.import_group(child)?,
                "Import" => self.import(child)?,
                "UsingTask" => self.using_task(child)?,
                "Target" => self.target(child)?,
                "ItemDefinitionGroup" => self.item_definition_group(child)?,
                "Choose" => self.choose(child, 0)?,
                "ProjectExtensions" => {
                    for name in attribute_names(child) {
                        self.unrecognized_attribute(child, name)?;
                    }
                    if self.seen_extensions {
                        return Err(malformed(child, "a second `<ProjectExtensions>`"));
                    }
                    self.seen_extensions = true;
                }
                "Sdk" => self.required(child, "Name", "`Name` is missing or empty")?,
                "Error" | "Warning" | "Message" => {
                    return Err(malformed(child, "a task outside a target"));
                }
                _ => self.unrecognized_child(root, child)?,
            }
        }
        Ok(())
    }

    fn property_group(&self, group: Node<'_, '_>) -> Parsed {
        self.attributes(group, CONDITION_AND_LABEL)?;
        for property in self.children(group)? {
            self.attributes(property, CONDITION_AND_LABEL)?;
            let name = qname(property);
            if !is_valid_name(name) {
                return Err(violation(
                    LoadTimeError::InvalidName {
                        name: name.to_owned(),
                    },
                    property,
                ));
            }
            if is_reserved_element_name(name) || is_msbuild_reserved_name(name) {
                return Err(violation(
                    LoadTimeError::ReservedProperty {
                        name: name.to_owned(),
                    },
                    property,
                ));
            }
        }
        Ok(())
    }

    fn item_group(&self, group: Node<'_, '_>, below_target: bool) -> Parsed {
        self.attributes(group, CONDITION_AND_LABEL)?;
        for item in self.children(group)? {
            self.item(item, below_target)?;
        }
        Ok(())
    }

    fn item(&self, item: Node<'_, '_>, below_target: bool) -> Parsed {
        let item_type = qname(item);
        let without_spec = || {
            violation(
                LoadTimeError::ItemWithoutSpec {
                    item: item_type.to_owned(),
                },
                item,
            )
        };
        let operations = ["Include", "Remove", "Update"]
            .into_iter()
            .filter(|op| has(item, op))
            .count();
        if operations > 1 || (operations == 0 && !below_target) {
            return Err(without_spec());
        }
        let include = value_of(item, "Include");
        if !value_of(item, "Exclude").is_empty() && include.is_empty() {
            return Err(malformed(item, "`Exclude` without an `Include`"));
        }
        if ["Include", "Remove", "Update"]
            .into_iter()
            .any(|op| has(item, op) && value_of(item, op).is_empty())
        {
            return Err(without_spec());
        }
        if !is_valid_name(item_type) {
            return Err(violation(
                LoadTimeError::InvalidName {
                    name: item_type.to_owned(),
                },
                item,
            ));
        }
        if is_reserved_element_name(item_type) {
            return Err(violation(
                LoadTimeError::ReservedItemName {
                    name: item_type.to_owned(),
                },
                item,
            ));
        }
        for name in attribute_names(item) {
            if !is_known_or_metadata(name) {
                self.unrecognized_attribute(item, name)?;
            }
        }
        let removes = !value_of(item, "Remove").is_empty();
        for metadatum in self.children(item)? {
            if removes {
                // `ChildElementsBelowRemoveNotAllowed`, after the metadatum's
                // own attributes and name.
                self.attributes(metadatum, CONDITION_AND_LABEL)?;
                self.metadatum_name(metadatum)?;
                return Err(malformed(metadatum, "metadata under a `Remove`"));
            }
            self.metadatum(metadatum, false)?;
        }
        Ok(())
    }

    fn metadatum_name(&self, metadatum: Node<'_, '_>) -> Parsed {
        let name = qname(metadatum);
        if !is_valid_name(name) {
            return Err(violation(
                LoadTimeError::InvalidName {
                    name: name.to_owned(),
                },
                metadatum,
            ));
        }
        Ok(())
    }

    fn metadatum(&self, metadatum: Node<'_, '_>, in_definition: bool) -> Parsed {
        self.attributes(metadatum, CONDITION_AND_LABEL)?;
        self.metadatum_name(metadatum)?;
        let name = qname(metadatum);
        if is_item_spec_modifier(name) {
            return Err(violation(
                LoadTimeError::ReservedMetadata {
                    name: name.to_owned(),
                },
                metadatum,
            ));
        }
        if is_reserved_element_name(name) {
            return Err(violation(
                LoadTimeError::ReservedItemName {
                    name: name.to_owned(),
                },
                metadatum,
            ));
        }
        if in_definition {
            // `ExpressionContainsItemVector` on the value, which is the
            // element's inner XML: an item list reference is refused. Read for
            // certain only on a value of one text node holding one `@(`, a name
            // and `)`; perhaps wherever else the source holds `@(`.
            let source = metadatum.document().input_text();
            let mut nodes = metadatum.children();
            let lone_text = match (nodes.next(), nodes.next()) {
                (Some(only), None) if only.is_text() => crate::document::text(only),
                _ => None,
            };
            let sure = lone_text.as_deref().is_some_and(|value| {
                value.matches("@(").count() == 1
                    && value.find("@(").is_some_and(|at| {
                        let rest = &value[at + 2..];
                        rest.find(')')
                            .is_some_and(|close| is_valid_name(rest[..close].trim()))
                    })
            });
            if sure || source[metadatum.range()].contains("@(") {
                return Err(Violation {
                    sure,
                    ..malformed(metadatum, "an item list in an item definition's metadatum")
                });
            }
        }
        Ok(())
    }

    fn import_group(&self, group: Node<'_, '_>) -> Parsed {
        self.attributes(group, CONDITION_AND_LABEL)?;
        for child in self.children(group)? {
            if qname(child) == "Import" {
                self.import(child)?;
            } else {
                self.unrecognized_child(group, child)?;
            }
        }
        Ok(())
    }

    fn import(&self, import: Node<'_, '_>) -> Parsed {
        self.attributes(import, IMPORT_ATTRIBUTES)?;
        if value_of(import, "Project").is_empty() {
            return Err(violation(LoadTimeError::ImportWithoutProject, import));
        }
        self.no_children(import)
    }

    fn using_task(&self, task: Node<'_, '_>) -> Parsed {
        self.attributes(task, USING_TASK_ATTRIBUTES)?;
        self.required(task, "TaskName", "`TaskName` is missing or empty")?;
        let assembly_name = value_of(task, "AssemblyName");
        let assembly_file = value_of(task, "AssemblyFile");
        if assembly_name.is_empty() == assembly_file.is_empty() {
            return Err(malformed(
                task,
                "not exactly one of `AssemblyName` and `AssemblyFile`",
            ));
        }
        for name in ["AssemblyName", "AssemblyFile"] {
            if attribute(task, name).is_some_and(|v| v.is_empty()) {
                return Err(malformed(task, "an empty `AssemblyName` or `AssemblyFile`"));
            }
        }
        let (mut parameters, mut body) = (false, false);
        for child in self.children(task)? {
            match qname(child) {
                "ParameterGroup" => {
                    if parameters {
                        return Err(malformed(child, "a second `<ParameterGroup>`"));
                    }
                    parameters = true;
                    self.parameter_group(child)?;
                }
                "Task" => {
                    if body {
                        return Err(malformed(child, "a second `<Task>`"));
                    }
                    body = true;
                    self.attributes(child, TASK_BODY_ATTRIBUTES)?;
                }
                _ => self.unrecognized_child(task, child)?,
            }
        }
        // A parameter group or a task body needs a task factory (MSB4035;
        // probed, `dotnet msbuild` 10.0, under a false condition too).
        if (parameters || body) && value_of(task, "TaskFactory").is_empty() {
            return Err(malformed(
                task,
                "a `<ParameterGroup>` or `<Task>` without a `TaskFactory`",
            ));
        }
        Ok(())
    }

    fn parameter_group(&self, group: Node<'_, '_>) -> Parsed {
        for name in attribute_names(group) {
            self.unrecognized_attribute(group, name)?;
        }
        let mut seen: Vec<&str> = Vec::new();
        for parameter in self.children(group)? {
            let name = qname(parameter);
            if seen.contains(&name) {
                return Err(malformed(parameter, "a second parameter of one name"));
            }
            self.attributes(parameter, PARAMETER_ATTRIBUTES)?;
            if !is_valid_name(name) {
                return Err(violation(
                    LoadTimeError::InvalidName {
                        name: name.to_owned(),
                    },
                    parameter,
                ));
            }
            seen.push(name);
        }
        Ok(())
    }

    fn target(&self, target: Node<'_, '_>) -> Parsed {
        self.attributes(target, TARGET_ATTRIBUTES)?;
        self.required(target, "Name", "`Name` is missing or empty")?;
        if escaping::unescape(&value_of(target, "Name"))
            .contains(['$', '@', '(', ')', '%', '*', '?', '.'])
        {
            return Err(malformed(target, "a character a target name cannot hold"));
        }
        let mut on_error = false;
        for child in self.children(target)? {
            let after_on_error = || malformed(target, "content after an `<OnError>`");
            match qname(child) {
                "PropertyGroup" => {
                    if on_error {
                        return Err(after_on_error());
                    }
                    self.property_group(child)?;
                }
                "ItemGroup" => {
                    if on_error {
                        return Err(after_on_error());
                    }
                    self.item_group(child, true)?;
                }
                "OnError" => {
                    self.attributes(child, ON_ERROR_ATTRIBUTES)?;
                    self.required(
                        child,
                        "ExecuteTargets",
                        "`ExecuteTargets` is missing or empty",
                    )?;
                    self.no_children(child)?;
                    on_error = true;
                }
                "ItemDefinitionGroup" => {
                    return Err(malformed(child, "an item definition group in a target"));
                }
                _ => {
                    if on_error {
                        return Err(after_on_error());
                    }
                    // A property written outside a property group: one text
                    // node, and nothing else.
                    let mut nodes = child.children();
                    if let (Some(only), None) = (nodes.next(), nodes.next())
                        && only.is_text()
                        && crate::document::text(only).is_some_and(|t| {
                            !t.chars().all(|c| matches!(c, ' ' | '\t' | '\r' | '\n'))
                        })
                    {
                        return Err(malformed(child, "a property outside a property group"));
                    }
                    self.task(child)?;
                }
            }
        }
        Ok(())
    }

    fn task(&self, task: Node<'_, '_>) -> Parsed {
        for name in attribute_names(task) {
            if SPECIAL_TASK_ATTRIBUTES
                .iter()
                .any(|special| special.eq_ignore_ascii_case(name) && *special != name)
            {
                return Err(malformed(
                    task,
                    "a task parameter cased apart from MSBuild's",
                ));
            }
        }
        for child in self.children(task)? {
            if qname(child) == "Output" {
                self.output(child)?;
            } else {
                self.unrecognized_child(task, child)?;
            }
        }
        Ok(())
    }

    fn output(&self, output: Node<'_, '_>) -> Parsed {
        self.attributes(output, OUTPUT_ATTRIBUTES)?;
        self.required(
            output,
            "TaskParameter",
            "`TaskParameter` is missing or empty",
        )?;
        self.no_children(output)?;
        let blank =
            |name: &str| attribute(output, name).is_none_or(|v| v.chars().all(char::is_whitespace));
        if blank("ItemName") == blank("PropertyName") {
            return Err(malformed(
                output,
                "not exactly one of `ItemName` and `PropertyName`",
            ));
        }
        for name in ["ItemName", "PropertyName"] {
            if attribute(output, name).is_some_and(|v| v.is_empty()) {
                return Err(malformed(output, "an empty `ItemName` or `PropertyName`"));
            }
        }
        if let Some(property) = attribute(output, "PropertyName")
            && !property.chars().all(char::is_whitespace)
            && is_msbuild_reserved_name(&property)
        {
            return Err(violation(
                LoadTimeError::ReservedProperty {
                    name: property.into_owned(),
                },
                output,
            ));
        }
        Ok(())
    }

    fn item_definition_group(&self, group: Node<'_, '_>) -> Parsed {
        self.attributes(group, CONDITION_AND_LABEL)?;
        for definition in self.children(group)? {
            for name in attribute_names(definition) {
                let known = ITEM_ATTRIBUTES.contains(&name);
                if (known && !CONDITION_AND_LABEL.contains(&name))
                    || (!known && !is_known_or_metadata(name))
                {
                    self.unrecognized_attribute(definition, name)?;
                }
            }
            for metadatum in self.children(definition)? {
                self.metadatum(metadatum, true)?;
            }
        }
        Ok(())
    }

    fn choose(&self, choose: Node<'_, '_>, depth: usize) -> Parsed {
        for name in attribute_names(choose) {
            self.unrecognized_attribute(choose, name)?;
        }
        let depth = depth + 1;
        if depth > MAXIMUM_CHOOSE_NESTING {
            return Err(violation(LoadTimeError::MalformedChoose, choose));
        }
        let (mut when, mut otherwise) = (false, false);
        for child in self.children(choose)? {
            match qname(child) {
                "When" => {
                    if otherwise || value_of(child, "Condition").is_empty() {
                        return Err(violation(LoadTimeError::MalformedChoose, choose));
                    }
                    self.branch(child, depth)?;
                    when = true;
                }
                "Otherwise" => {
                    if otherwise {
                        return Err(violation(LoadTimeError::MalformedChoose, choose));
                    }
                    otherwise = true;
                    for name in attribute_names(child) {
                        self.unrecognized_attribute(child, name)?;
                    }
                    self.branch(child, depth)?;
                }
                _ => self.unrecognized_child(choose, child)?,
            }
        }
        if !when {
            return Err(violation(LoadTimeError::MalformedChoose, choose));
        }
        Ok(())
    }

    /// `ParseWhenOtherwiseChildren`.
    fn branch(&self, branch: Node<'_, '_>, depth: usize) -> Parsed {
        for child in self.children(branch)? {
            match qname(child) {
                "PropertyGroup" => self.property_group(child)?,
                "ItemGroup" => self.item_group(child, false)?,
                "Choose" => self.choose(child, depth)?,
                "ItemDefinitionGroup" => self.item_definition_group(child)?,
                _ => self.unrecognized_child(branch, child)?,
            }
        }
        Ok(())
    }
}

/// `CheckMetadataAsAttributeName`: whether an item's attribute `name` is one
/// it takes, or a metadatum it may be written as.
fn is_known_or_metadata(name: &str) -> bool {
    if !is_valid_name(name) {
        return false;
    }
    if ITEM_ATTRIBUTES.contains(&name) {
        return true;
    }
    !(ITEM_ATTRIBUTES.iter().any(|a| a.eq_ignore_ascii_case(name))
        || name.starts_with('_')
        || is_item_spec_modifier(name)
        || is_reserved_element_name(name))
}

/// Whether the source of the text node `text` (with a little either side,
/// where `roxmltree` merges a CDATA section into its neighbours) holds a CDATA
/// section.
fn holds_cdata(text: Node<'_, '_>) -> bool {
    let source = text.document().input_text();
    let mut start = text.range().start.saturating_sub(9);
    while !source.is_char_boundary(start) {
        start -= 1;
    }
    let mut end = (text.range().end + 9).min(source.len());
    while !source.is_char_boundary(end) {
        end += 1;
    }
    source[start..end].contains("<![CDATA[")
}

/// Whether MSBuild refuses the item at `item`, a `Remove` with
/// `MatchOnMetadata` that names more than item types ("Only item types may be
/// referenced when removing with MatchOnMetadata"; probed, `dotnet msbuild`
/// 10.0): `Some(true)` for certain, `Some(false)` perhaps. Not the loader's
/// rule but the item operation's, which a build builds for an item whose
/// group's and own conditions hold (design-time evaluation, under false ones
/// too), and not in a `<When>` it does not choose. Both lists are split at
/// `;` and trimmed, and an empty one makes no claim; text a property, item or
/// escape may change is only perhaps refused.
pub(super) fn remove_matching_more_than_items(item: Node<'_, '_>) -> Option<bool> {
    let fragments = |text: &str| -> Vec<String> {
        text.split(';')
            .map(str::trim)
            .filter(|f| !f.is_empty())
            .map(str::to_owned)
            .collect()
    };
    let remove = attribute(item, "Remove")?;
    let matching = attribute(item, "MatchOnMetadata")?;
    let dynamic = |text: &str| text.contains(['$', '@', '%']);
    if fragments(&matching).is_empty() && !dynamic(&matching) {
        return None;
    }
    let removed = fragments(&remove);
    let references_only = removed.iter().all(|fragment| {
        fragment
            .strip_prefix("@(")
            .and_then(|rest| rest.strip_suffix(')'))
            .is_some_and(is_valid_name)
    });
    if references_only && !remove.contains(['$', '%']) {
        return None;
    }
    Some(!dynamic(&remove) && !dynamic(&matching) && !removed.is_empty())
}
