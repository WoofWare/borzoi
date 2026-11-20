//! Generated element contents, each held to the text MSBuild reads of the
//! element (`Utilities.GetXmlNodeInnerContents`, behind
//! `ProjectPropertyElement.Value`, `ProjectMetadataElement.Value` and
//! `ProjectUsingTaskBodyElement.TaskBody`) through
//! `tools/msbuild-condition-oracle`'s `elementContents` op.
//!
//! The rejection judgement expands a property's body, a metadatum's and an
//! inline task's as MSBuild does, so it must first read each as MSBuild
//! does: the element's text, its inner text where a CDATA section leads, or
//! its inner XML as `XmlDocument` serializes it, which writes back namespace
//! declarations, quotes and escapes attribute values its own way, and drops
//! whitespace nodes. The walk reproduces that reading where it can and
//! declines elsewhere ([`borzoi_msbuild::test_support::element_contents`]).
//!
//! The generator writes contents over the shapes that reading turns on:
//! default and prefixed namespaces, inherited from the project or
//! redeclared, `xml:space` scopes, CDATA sections, comments, processing
//! instructions and whitespace nodes at every position, entity and character
//! references, attributes in either quote on nested elements, nesting to past
//! the walk's depth bound, and Windows line ends; and puts them in each
//! element MSBuild reads so ([`Site`]). Its texts and namespace names are
//! drawn from the hostile name alphabet and spelled through the hostile XML
//! alphabet (`borzoi_oracle_harness::hostile`). Each is graded
//! certain-implies-exact: where the walk reads an element's text, it is
//! MSBuild's, byte for byte; a decline makes no claim.

mod common;

use std::collections::BTreeSet;
use std::path::Path;

use borzoi_oracle_harness::hostile::{self, Dimension, coverage, name, xml};
use common::{Oracle, SplitMix64, soak_parameters};
use tempfile::TempDir;

/// MSBuild's namespace, which a project's root may declare.
const MSBUILD_NS: &str = "http://schemas.microsoft.com/developer/msbuild/2003";

/// What the census excludes, and why.
const EXCLUDED: &[(Dimension, &str)] = &[(
    Dimension::NonUtf8,
    "an XML document is text: a name that is not UTF-8 cannot be written into one",
)];

/// The texts the generator writes of its own, and the stems hostile names
/// are rendered around.
const PLAIN_TEXTS: &[&str] = &[
    "x",
    "$(P)",
    "a b",
    "1 < 2 && 3 > 2",
    "\"q\" 'a'",
    "]]>",
    "--",
    "@(I)",
    "%(M)",
    "$(P.Substring(9))",
    "é",
    "",
    "\n    Log.LogMessage(\"$(P)\");\n  ",
    "a\tb\nc",
];

/// Text spelt with references, which a reader decodes and a serializer
/// writes back its own way.
const REFERENCES: &[&str] = &[
    "&amp;",
    "&lt;",
    "&gt;",
    "&quot;",
    "&apos;",
    "a&amp;b",
    "&#36;(P)",
    "&#x24;(P)",
    "&#32;",
    "&#x20;",
    "&#10;",
    "&#9;",
    "&#xD;",
    "&#13;",
    "&#xA0;",
];

/// Whitespace nodes: XML whitespace alone, which MSBuild's reader drops
/// unless an `xml:space` scope keeps it.
const WHITESPACE: &[&str] = &[" ", "\n  ", "\t", "\n", "\r\n", "  \n\t "];

/// Processing instructions.
const INSTRUCTIONS: &[&str] = &[
    "<?pi?>",
    "<?pi data $(P)?>",
    "<?x-y a=\"b\"?>",
    "<?pi   d?>",
    "<?pi d  ?>",
    "<?pi\n\td?>",
    "<?pi ?>",
    "<?pi a\nb ?>",
];

/// Element names, without a prefix.
const ELEMENT_NAMES: &[&str] = &["Code", "Reference", "Using", "a", "Code.Sub", "x-y"];

/// Attribute names, without a prefix.
const ATTRIBUTE_NAMES: &[&str] = &["Include", "Type", "a", "b-c", "Language"];

/// One node of a generated body.
#[derive(Debug, Clone)]
enum Node {
    /// Source written as it is: text, a CDATA section, a comment, a
    /// processing instruction, whitespace.
    Raw(String),
    Element {
        name: String,
        /// Each attribute's name, its value as source, and its quote.
        attributes: Vec<(String, String, char)>,
        children: Vec<Node>,
        self_closing: bool,
    },
}

fn render(node: &Node, out: &mut String) {
    match node {
        Node::Raw(source) => out.push_str(source),
        Node::Element {
            name,
            attributes,
            children,
            self_closing,
        } => {
            out.push('<');
            out.push_str(name);
            for (attribute, value, quote) in attributes {
                out.push(' ');
                out.push_str(attribute);
                out.push('=');
                out.push(*quote);
                out.push_str(value);
                out.push(*quote);
            }
            if *self_closing && children.is_empty() {
                out.push_str("/>");
            } else {
                out.push('>');
                for child in children {
                    render(child, out);
                }
                out.push_str("</");
                out.push_str(name);
                out.push('>');
            }
        }
    }
}

/// The case being built: the hostile dimensions drawn into it.
struct Case {
    hostile: BTreeSet<Dimension>,
    texts: Vec<hostile::Entry<String>>,
}

impl Case {
    /// A text: the generator's own, or a hostile name.
    fn text(&mut self, rng: &mut SplitMix64) -> String {
        let plain = *rng.pick(PLAIN_TEXTS);
        match hostile::sample(&self.texts, rng.next()) {
            Some(entry) => {
                self.hostile.insert(entry.dimension);
                entry.value.replace("Stem", plain)
            }
            None => plain.to_owned(),
        }
    }

    /// `text` written in `place`: plainly, or in a hostile XML spelling, and
    /// with a character XML cannot hold written as itself (the document is
    /// then malformed, which both readers must refuse).
    fn spell(&mut self, rng: &mut SplitMix64, text: &str, place: xml::Place) -> String {
        if let Some(entry) = xml::alphabet().sample(rng.next())
            && let Some(spelt) = xml::spell(text, entry.value, place)
        {
            self.hostile.insert(entry.dimension);
            return spelt.xml;
        }
        match xml::escape(text, place) {
            Ok(escaped) => escaped,
            Err(_) => text
                .chars()
                .map(|c| {
                    if xml::representable(c) {
                        xml::escape(&c.to_string(), place).expect("representable")
                    } else {
                        c.to_string()
                    }
                })
                .collect(),
        }
    }

    /// A namespace name, as an attribute value's source.
    fn namespace(&mut self, rng: &mut SplitMix64) -> String {
        match rng.below(6) {
            0 => MSBUILD_NS.to_owned(),
            1 => String::new(),
            2 | 3 => "urn:a".to_owned(),
            _ => {
                let text = format!("urn:{}", self.text(rng));
                self.spell(rng, &text, xml::Place::Attribute)
            }
        }
    }

    fn attribute(&mut self, rng: &mut SplitMix64) -> (String, String, char) {
        let name = match rng.below(12) {
            0 => "p:a".to_owned(),
            1 => "xml:lang".to_owned(),
            _ => (*rng.pick(ATTRIBUTE_NAMES)).to_owned(),
        };
        let text = self.text(rng);
        let value = self.spell(rng, &text, xml::Place::Attribute);
        if rng.below(3) == 0 {
            (name, value.replace('\'', "&apos;"), '\'')
        } else {
            (name, value, '"')
        }
    }

    /// The declarations and scopes an element may carry: a default or
    /// prefixed namespace, an `xml:space`.
    fn declarations(&mut self, rng: &mut SplitMix64, rate: usize) -> Vec<(String, String, char)> {
        let mut out = Vec::new();
        if rng.below(rate) == 0 {
            let uri = self.namespace(rng);
            out.push(("xmlns".to_owned(), uri, '"'));
        }
        if rng.below(rate) == 0 {
            let uri = self.namespace(rng);
            out.push(("xmlns:p".to_owned(), uri, '"'));
        }
        if rng.below(rate + 4) == 0 {
            let space = *rng.pick(&["preserve", "default"]);
            out.push(("xml:space".to_owned(), space.to_owned(), '"'));
        }
        out
    }

    fn element(&mut self, rng: &mut SplitMix64, depth: usize) -> Node {
        let local = *rng.pick(ELEMENT_NAMES);
        let name = if rng.below(8) == 0 {
            format!("p:{local}")
        } else {
            local.to_owned()
        };
        let mut attributes: Vec<(String, String, char)> = Vec::new();
        for _ in 0..rng.below(3) {
            let attribute = self.attribute(rng);
            // A name twice is malformed.
            if attributes.iter().all(|(name, ..)| *name != attribute.0) {
                attributes.push(attribute);
            }
        }
        let declarations = self.declarations(rng, 8);
        // A declaration among the attributes, or after them.
        let at = rng.below(attributes.len() + 1);
        for (i, declaration) in declarations.into_iter().enumerate() {
            attributes.insert(at + i, declaration);
        }
        let children = if depth >= 3 {
            Vec::new()
        } else {
            self.children(rng, depth + 1)
        };
        Node::Element {
            name,
            attributes,
            self_closing: children.is_empty() && rng.below(2) == 0,
            children,
        }
    }

    fn node(&mut self, rng: &mut SplitMix64, depth: usize) -> Node {
        match rng.below(if depth >= 3 { 7 } else { 10 }) {
            0 => Node::Raw((*rng.pick(WHITESPACE)).to_owned()),
            1 | 2 => {
                let text = self.text(rng);
                Node::Raw(self.spell(rng, &text, xml::Place::Element))
            }
            3 => {
                let text = self.text(rng);
                self.hostile.insert(Dimension::Cdata);
                Node::Raw(
                    xml::spell(&text, xml::How::Cdata, xml::Place::Element)
                        .map_or_else(|| "<![CDATA[]]>".to_owned(), |spelt| spelt.xml),
                )
            }
            4 => Node::Raw(format!("<!--{}-->", self.text(rng))),
            5 => Node::Raw((*rng.pick(REFERENCES)).to_owned()),
            6 => Node::Raw((*rng.pick(INSTRUCTIONS)).to_owned()),
            _ => self.element(rng, depth),
        }
    }

    fn children(&mut self, rng: &mut SplitMix64, depth: usize) -> Vec<Node> {
        (0..rng.below(4)).map(|_| self.node(rng, depth)).collect()
    }
}

/// The element the generated contents stand in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Site {
    /// A `<UsingTask>`'s `<Task>`.
    TaskBody,
    /// A property.
    Property,
    /// An item's metadatum.
    ItemMetadata,
    /// An item definition's metadatum.
    DefinitionMetadata,
}

const SITES: [Site; 4] = [
    Site::TaskBody,
    Site::Property,
    Site::ItemMetadata,
    Site::DefinitionMetadata,
];

/// One generated project: its source, the site of its contents, and the
/// hostile dimensions in it.
fn generate(rng: &mut SplitMix64, texts: &[hostile::Entry<String>]) -> (String, Site, Case) {
    let mut case = Case {
        hostile: BTreeSet::new(),
        texts: texts.to_vec(),
    };
    let mut body = if rng.below(20) == 0 {
        // A chain of elements about the walk's depth bound.
        let depth = *rng.pick(&[2usize, 62, 63, 64, 65, 66, 70]);
        let mut node = Node::Raw("$(P)".to_owned());
        for _ in 0..depth {
            node = Node::Element {
                name: "a".to_owned(),
                attributes: Vec::new(),
                children: vec![node],
                self_closing: false,
            };
        }
        vec![node]
    } else {
        case.children(rng, 0)
    };
    // Most bodies hold an element, which is what MSBuild serializes.
    if rng.below(3) != 0 && !body.iter().any(|n| matches!(n, Node::Element { .. })) {
        let at = rng.below(body.len() + 1);
        let element = case.element(rng, 0);
        body.insert(at, element);
    }
    let project_ns = match rng.below(3) {
        0 => String::new(),
        _ => format!(" xmlns=\"{MSBUILD_NS}\""),
    };
    // The prefix most bodies' prefixed names need, declared on the project
    // (`<Task>` takes no attribute but `Evaluate`, a declaration included).
    let mut project_extra = String::new();
    if rng.below(2) == 0 {
        let uri = match case.namespace(rng) {
            uri if uri.is_empty() => "urn:p".to_owned(),
            uri => uri,
        };
        project_extra.push_str(&format!(" xmlns:p=\"{uri}\""));
    }
    let mut inner = String::new();
    for node in &body {
        render(node, &mut inner);
    }
    // Half the cases are inline tasks, whose bodies are where XML is written.
    let site = match rng.below(6) {
        0..3 => Site::TaskBody,
        3 => Site::Property,
        4 => Site::ItemMetadata,
        _ => Site::DefinitionMetadata,
    };
    let element = match site {
        Site::TaskBody => {
            let evaluate = if rng.below(10) == 0 {
                " Evaluate=\"true\""
            } else {
                ""
            };
            format!(
                "<UsingTask TaskName=\"T\" TaskFactory=\"RoslynCodeTaskFactory\" \
                 AssemblyFile=\"y.dll\">\n    <Task{evaluate}>{inner}</Task>\n  </UsingTask>"
            )
        }
        Site::Property => format!("<PropertyGroup>\n    <P>{inner}</P>\n  </PropertyGroup>"),
        Site::ItemMetadata => {
            format!("<ItemGroup>\n    <I Include=\"a\"><M>{inner}</M></I>\n  </ItemGroup>")
        }
        Site::DefinitionMetadata => {
            format!("<ItemDefinitionGroup>\n    <I><M>{inner}</M></I>\n  </ItemDefinitionGroup>")
        }
    };
    let source = format!("<Project{project_ns}{project_extra}>\n  {element}\n</Project>\n");
    // A document written with Windows line ends.
    let source = if rng.below(6) == 0 {
        source.replace("\r\n", "\n").replace('\n', "\r\n")
    } else {
        source
    };
    (source, site, case)
}

#[derive(Debug, Default)]
struct Tally {
    cases: usize,
    /// The walk read the body, and it is MSBuild's.
    committed: usize,
    /// The walk declined to read it.
    declined: usize,
    /// MSBuild refused to load the document, so it reads no body.
    msbuild_refused: usize,
    /// Committed bodies that MSBuild serialized from elements.
    committed_with_elements: usize,
    /// Committed bodies whose serialization declares a namespace.
    committed_with_namespace: usize,
    /// Committed bodies serialized from elements, by site ([`SITES`]).
    committed_with_elements_by_site: [usize; 4],
    /// Each body the walk reads otherwise than MSBuild: the project, ours,
    /// MSBuild's.
    wrong: Vec<(String, String, Option<String>)>,
}

/// Grade `source` (a project at `path` whose contents stand at `site`): the
/// walk's reading of the element is MSBuild's, or a decline. The outcome,
/// for the census.
fn grade(
    oracle: &mut Oracle,
    source: &str,
    site: Site,
    path: &Path,
    tally: &mut Tally,
) -> &'static str {
    tally.cases += 1;
    let ours = borzoi_msbuild::test_support::element_contents(source);
    let Some(theirs) = oracle.element_contents(source, path) else {
        tally.msbuild_refused += 1;
        return "msbuild-refuses";
    };
    let Some(ours) = ours else {
        tally.declined += 1;
        return "decline";
    };
    let theirs = theirs.first().cloned();
    if theirs.as_ref() != Some(&ours) {
        tally.wrong.push((source.to_owned(), ours, theirs));
        return "wrong";
    }
    tally.committed += 1;
    if ours.contains('<') {
        tally.committed_with_elements += 1;
        let at = SITES.iter().position(|s| *s == site).expect("a site");
        tally.committed_with_elements_by_site[at] += 1;
    }
    if ours.contains("xmlns=") {
        tally.committed_with_namespace += 1;
    }
    "commit"
}

/// Fail, showing the first few, if the walk read any body otherwise than
/// MSBuild.
fn assert_read_as_msbuild_reads(tally: &Tally) {
    let shown: Vec<String> = tally
        .wrong
        .iter()
        .take(8)
        .map(|(source, ours, theirs)| {
            format!("{source}\n  ours:    {ours:?}\n  MSBuild: {theirs:?}")
        })
        .collect();
    assert!(
        tally.wrong.is_empty(),
        "the walk reads {} of {} elements' contents otherwise than MSBuild does:\n\n{}",
        tally.wrong.len(),
        tally.cases,
        shown.join("\n\n")
    );
}

fn sweep(rng: &mut SplitMix64, cases: usize) -> Tally {
    let census = coverage::open(
        "crates/msbuild/tests/element_contents_diff.rs",
        "element_contents",
        EXCLUDED,
    );
    let texts = name::as_text("Stem", "");
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.proj");
    let mut tally = Tally::default();
    while tally.cases < cases {
        let (source, site, case) = generate(rng, &texts);
        let outcome = grade(&mut oracle, &source, site, &path, &mut tally);
        census.reached(&case.hostile, outcome);
    }
    census.finish(
        "BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-msbuild --test \
         element_contents_diff sweep_fixed_seed",
    );
    tally
}

/// The generated contents at a fixed seed. The floors say the sweep reaches
/// what it is for: contents the walk reads, serialized from elements at
/// every site, with a namespace written back.
#[test]
fn sweep_fixed_seed() {
    let mut rng = SplitMix64(0x1009_b0d1);
    let tally = sweep(&mut rng, 2_000);
    for (site, committed) in SITES.iter().zip(tally.committed_with_elements_by_site) {
        assert!(committed >= tally.cases / 50, "{site:?}: {tally:?}");
    }
    assert_read_as_msbuild_reads(&tally);
    eprintln!("element contents sweep: {tally:?}");
    assert!(tally.committed >= tally.cases / 4, "{tally:?}");
    assert!(
        tally.committed_with_elements >= tally.cases / 10,
        "{tally:?}"
    );
    assert!(
        tally.committed_with_namespace >= tally.cases / 50,
        "{tally:?}"
    );
    assert!(tally.msbuild_refused <= tally.cases / 2, "{tally:?}");
}

/// [`sweep_fixed_seed`] at a seed and size of the environment's choosing.
#[test]
#[ignore]
fn sweep_soak() {
    let (seed, cases) = soak_parameters("element contents", 10_000);
    let mut rng = SplitMix64(seed);
    let tally = sweep(&mut rng, cases);
    assert_read_as_msbuild_reads(&tally);
    eprintln!("element contents soak: {tally:?}");
}

/// Each corner's project: the attributes of its `<Project>`, and its body.
fn corner_source(project: &str, body: &str) -> String {
    format!(
        "<Project{project}><UsingTask TaskName=\"T\" TaskFactory=\"RoslynCodeTaskFactory\" \
         AssemblyFile=\"y.dll\"><Task>{body}</Task></UsingTask></Project>"
    )
}

/// The project's attributes declaring MSBuild's namespace.
const IN_MSBUILD_NS: &str = " xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\"";

/// Bodies the walk must read, each MSBuild's: the shapes of real inline
/// tasks, which a sweep could commit to none of without failing a floor.
#[test]
fn corner_bodies_are_read_as_msbuild_reads_them() {
    let corners: &[(&str, &str)] = &[
        // An element in the project's namespace, which it inherits.
        (IN_MSBUILD_NS, "<Reference Include=\"$(Lib)\" />"),
        // Its child, which inherits it from the element too.
        (IN_MSBUILD_NS, "<Code><Using Namespace=\"N\"/></Code>"),
        // No namespace at all.
        ("", "<Reference Include=\"$(Lib)\" />"),
        // Whitespace nodes between, around and inside elements.
        (IN_MSBUILD_NS, "\n  <a>x</a>\n  <b> </b>\n"),
        ("", "\n\t<a/>  <a/>\n"),
        // The same with Windows line ends.
        (
            IN_MSBUILD_NS,
            "\r\n  <Reference Include=\"$(Lib)\" />\r\n  <Code Type=\"Fragment\"><![CDATA[x]]></Code>\r\n",
        ),
        // Code as text, over several lines, which the writer writes as read.
        (
            IN_MSBUILD_NS,
            "<Code Type=\"Fragment\" Language=\"cs\">\n    Log.LogMessage(\"$(P)\");\n  </Code>",
        ),
        // A leading CDATA section, read as the inner text.
        ("", "<![CDATA[$(P)]]><a>y</a>"),
        // Text, references and quotes, escaped as the serializer escapes them.
        ("", "<a b='x\"y' c=\"1 &lt; 2\">p &amp; q &apos;r&apos;</a>"),
        // A line end in an attribute, which the writer writes as a reference.
        ("", "<a b=\"x&#10;y&#13;z&#9;w\"/>"),
        // A comment and processing instructions beside an element, an
        // instruction with no data written with a space all the same.
        ("", "<!-- c --><a/><?pi d?><?pi?><?pi   e?>"),
        // A CDATA section within an element of text.
        (
            IN_MSBUILD_NS,
            "<Code Type=\"Fragment\"><![CDATA[ $(P) ]]></Code>",
        ),
    ];
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.proj");
    for (project, body) in corners {
        let source = corner_source(project, body);
        let theirs = oracle
            .element_contents(&source, &path)
            .unwrap_or_else(|| panic!("MSBuild refuses {source}"));
        let ours = borzoi_msbuild::test_support::element_contents(&source);
        assert!(
            ours.is_some(),
            "the walk declines {source}; MSBuild reads {theirs:?}"
        );
        assert_eq!(ours.as_ref(), theirs.first(), "{source}");
    }
}

/// Bodies the walk has read otherwise than MSBuild, each found by the sweep:
/// it must now read each as MSBuild does, or decline.
#[test]
fn bodies_once_misread_are_read_as_msbuild_reads_them_or_declined() {
    let corners: &[(&str, &str)] = &[
        // A CDATA section and a whitespace node `roxmltree` joins into one
        // text, where MSBuild's reader drops the whitespace.
        ("", "<![CDATA[%(M)]]><Code.Sub><![CDATA[x]]>\n</Code.Sub>"),
        ("", "<![CDATA[a]]>\n <a/>"),
        // A namespace declared again as what is in scope, which `XmlDocument`
        // writes back as an attribute where it stands.
        (
            IN_MSBUILD_NS,
            "<Code.Sub xmlns=\"http://schemas.microsoft.com/developer/msbuild/2003\" Language=\"$(P)\">x</Code.Sub>",
        ),
        (" xmlns:p=\"urn:a\"", "a<a xmlns:p=\"urn:a\"><!--c--></a>"),
        // A processing instruction with no data.
        ("", "<?pi?><a/>"),
    ];
    let mut oracle = Oracle::spawn();
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.proj");
    for (project, body) in corners {
        let source = corner_source(project, body);
        let theirs = oracle
            .element_contents(&source, &path)
            .unwrap_or_else(|| panic!("MSBuild refuses {source}"));
        if let Some(ours) = borzoi_msbuild::test_support::element_contents(&source) {
            assert_eq!(Some(&ours), theirs.first(), "{source}");
        }
    }
}
