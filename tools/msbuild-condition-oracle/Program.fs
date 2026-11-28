/// Differential-test oracle over the *real* MSBuild condition evaluator
/// (test-only; never shipped in the LSP). It answers the one question
/// `crates/msbuild/src/condition.rs` reimplements: "given these properties,
/// does MSBuild consider this `Condition` string true, false, or illegal?"
///
/// Protocol: JSONL request/response over stdin/stdout, one response line per
/// request line, in order (the same long-lived-batch-child pattern as
/// tools/fcs-dump and tools/nuget-oracle). The ops:
///
///   {"op":"eval","condition":s,"properties":{name:value, ..}}
///     -> {"ok":true,"value":true|false}   // MSBuild evaluated the condition
///      | {"ok":false}                     // MSBuild rejects it as illegal
///                                          //   (InvalidProjectFileException,
///                                          //    e.g. `==`, `1 <`, bad funcs)
///
///   {"op":"expand","value":s,"properties":{name:value, ..}}
///     -> {"ok":true,"value":s}            // MSBuild expanded the property value
///      | {"ok":false}                     // MSBuild errors evaluating it
///                                          //   (e.g. a property function that
///                                          //    throws: bad Version.Parse,
///                                          //    out-of-range indexer)
///     The `value` is placed verbatim as the text of a `<_ExpandResult>`
///     property and read back after evaluation, so `$(…)` property functions
///     inside it run exactly as a real build would run them. The caller MUST
///     NOT reference `_ExpandResult` inside `value` (it would self-collide);
///     the differential harness generates names from a controlled set disjoint
///     from it, exactly as for `eval`.
///
///   {"op":"items","xml":s,"path":s,"itemType":s,"globals":{name:value, ..}?}
///     -> {"ok":true,"items":[fullPath, ..]}     // MSBuild evaluated the items
///      | {"ok":false}                           // MSBuild rejects the project
///     The `project` op's item-side twin: the document is written to `path` and
///     loaded as that file (so the reserved path derivatives are computed from
///     the same path the Rust side uses), and the evaluated items of `itemType`
///     come back as their `FullPath` metadata, in evaluation order. This is what
///     `dotnet msbuild -getItem:` reports, but through the resident oracle — a
///     per-case `dotnet msbuild` pays .NET startup every time, which a
///     generative sweep cannot afford.
///
///   {"op":"elementContents","xml":s,"path":s}
///     -> {"ok":true,"contents":[s, ..]}         // each property's, metadatum's
///                                               //   and inline task body's
///                                               //   text, unexpanded
///      | {"ok":false}                           // MSBuild refuses to load it
///     What MSBuild reads as the text of each element it reads by its
///     contents (`ProjectPropertyElement.Value`, `ProjectMetadataElement.Value`,
///     `ProjectUsingTaskBodyElement.TaskBody`: an element's inner text or
///     inner XML, `Utilities.GetXmlNodeInnerContents`), in document order,
///     for the rejection judgement's reading of them to be held to.
///
///   {"op":"itemsMeta","xml":s,"path":s,"itemType":s,"metadata":[name, ..],
///    "designTime":true?}
///     -> {"ok":true,"items":[{"identity":s,"escaped":s,"metadata":{name:value, ..}}, ..]}
///      | {"ok":false}                           // MSBuild rejects the project
///     The `items` op enriched for the *dependency* set, where `FullPath` is
///     meaningless: each evaluated item of `itemType` comes back as its
///     `EvaluatedInclude` (the identity MSBuild matches `Update`/`Remove`
///     against) plus the requested metadata's evaluated values (unset reads
///     back as ""). This is what lets a generative sweep diff a
///     `<PackageReference>` `Include`+`Update` collapse — identity matching and
///     per-key metadata merge — against the real evaluator, resident.
///
///   {"op":"project","xml":s,"names":[..],"globals":{name:value, ..}?,
///    "designTime":true?}
///     -> {"ok":true,"values":{name:value, ..}}  // MSBuild evaluated the project
///      | {"ok":false}                           // MSBuild rejects the project
///     The caller's project XML is evaluated *verbatim*, so both sides read the
///     same document. Unlike `expand` — which hands MSBuild a property *body*
///     between sentinels, and is therefore blind to the XML layer that runs
///     before expansion (insignificant whitespace, entity decoding, CDATA,
///     comment-split text) — this op is what lets a differential see that
///     layer at all. It evaluates as a build does; `"designTime":true` asks
///     for the evaluation a design-time host loads instead (`Evaluation`).
///
///   {"op":"restoreCone","project":s,"globals":{name:value, ..}}
///     -> {"ok":true,"succeeded":b,"errors":[..],"msbuildDirectory":s,
///         "sdkVersion":s,"targets":[..],"tasks":[..],"files":{..},
///         "assemblies":{..},"loadedDuringBuilds":[..],"dgspec":s|null,
///         "writer":{"restoreRecursive":s|null,"invocations":n,
///                   "entries":[{"identity":s,"metadata":{..}}, ..]}|null}
///     The restore-cone census of docs/nuget-dgspec-boundary-plan.md (stage
///     8): builds `GenerateRestoreGraphFile` on the project file in-process,
///     under exactly `globals`, and reports every target and task that
///     executed, the SHA-256 of each file they come from, each task assembly's
///     identity, and the spec written to `RestoreGraphOutputPath`. See
///     `restoreCone` below. `writer` is the inputs of the one
///     `WriteRestoreGraphTask` invocation that wrote `RestoreGraphOutputPath`,
///     as it was handed them: its items with their custom metadata as it reads
///     them (unescaped), and its `RestoreRecursive` (null when unset). It is
///     null unless exactly one invocation wrote that path. This is the item
///     seam of A₁. Unlike the evaluation ops this one *executes*
///     targets, so it reaches the SDK's task code.
///
///   {"op":"evaluated","project":s,"globals":{..},"properties":[..],"items":[..]}
///     -> {"ok":true,"properties":{name:value|null, ..},
///         "items":{type:[{"identity":s,"metadata":{..}}, ..], ..},
///         "targets":{name:{"file":s,"line":n,"column":n}|null, ..}}
///     Evaluates the project file at `project` under `globals` without building
///     it, and reads back each named property (null when unset) and each named
///     item type's items with their metadata: the evaluation the restore
///     targets run on. The restore-cone census reads it against ours.
///     An optional `"targets":[..]` names targets to look up in the
///     evaluation's target table, by MSBuild's own name rules: where the
///     definition it keeps is, or null.
///     `{"ok":false}` when MSBuild rejects the project.
///
///   {"op":"runTargets","path":s,"targets":[..],"properties":[..],"items":[..]}
///     -> {"ok":true,"succeeded":b,"errors":[..],"targets":[name, ..],
///         "properties":{name:value|null, ..},
///         "items":{type:[{"identity":s,"escaped":s,"metadata":{..}}, ..], ..}}
///      | {"ok":false}                           // MSBuild rejects the project
///     Evaluates the project file at `path`, builds `targets` on it in-process,
///     and reads back every target that started, in order, and the properties
///     and items the build leaves. A₁.3c's executor is held to it.
///
///   {"op":"targetItems","path":s,"target":s,"itemType":s,"globals":{..}?}
///     -> {"ok":true,"succeeded":b,"errors":[..],"items":[fullPath, ..]}
///      | {"ok":false}                           // MSBuild rejects the project
///     Evaluates the project file at `path` as it stands on disk, executes
///     `target` on that evaluation in-process, and reads back the `FullPath` of
///     every `itemType` item the build leaves, in order: what a target makes of
///     the evaluated items (F#'s `FSharpSourceCodeCompileOrder` reorders the
///     Compile list) without a `dotnet msbuild` per case.
///
///   {"op":"rejectionCode","xml":s,"path":s}
///     -> {"ok":true}                     // MSBuild evaluated the project
///      | {"ok":false,"code":s,"message":s,"line":n,"column":n}
///                                        // MSBuild rejects it, so, there
///     The design-time evaluation of the document as the file at `path`, as
///     `project` with `"designTime":true` evaluates it, reporting the
///     `InvalidProjectFileException`'s error code (`MSB4184`, …; `null` for
///     an XML error, whose message stands for it) and where in the file it
///     points, for a differential that grades which refusal rejected the
///     project (`respondRejectionCode`).
///
///   {"op":"globalName","name":s}
///     -> {"accepted":true}
///      | {"accepted":false,"exceptionType":s,"message":s}
///     Whether MSBuild takes `name` as a global property name
///     (`respondGlobalName`).
///
///   {"op":"reservedNames"}
///     -> {"names":[..],"table":[..]|null,"kinds":n}
///     The names the loaded MSBuild reserves, read by reflection
///     (`respondReservedNames`).
///
///   {"op":"bench","project":s,"globals":{..}?,"mode":m,"reps":n,"scratch":dir?}
///     -> {"ok":b,"errors":[..],"runs":[{"instructions":n|null,"allocatedBytes":n}, ..],
///         "processInstructions":n|null,"msbuildBinPath":s,"compile":[fullPath, ..]}
///     Not a differential: what MSBuild costs, for `crates/lsp/examples/eval_counts.rs`
///     to set beside our evaluation's cost. Runs `mode` `reps` times in this
///     process and reports each run in order: the instructions the whole
///     process retired over it (`proc_pid_rusage`, null off macOS) and the
///     managed bytes it allocated. The modes:
///       - "fresh": evaluate the project file in a new `ProjectCollection`.
///       - "shared": evaluate it in one `ProjectCollection` kept for the
///         process's life, across runs and requests, so MSBuild reuses
///         whatever that collection caches, as a resident host does.
///       - "designTime": what Ionide.ProjInfo (FsAutoComplete's loader) does
///         to load the project: two evaluations and a design-time build
///         (`projInfoDesignTimeBuild`), its intermediate output sent to
///         `scratch`, which this mode needs.
///     `ok` is false, with the build's errors, at the first run that fails.
///     `processInstructions` is everything the process has retired by the end,
///     .NET start-up and JIT included. `msbuildBinPath` and `compile` are the
///     last measured run's evaluation (the design-time build's before its
///     targets run; null and empty when no run succeeded), so the caller can
///     check MSBuild evaluated the project it evaluated, on the same toolset.
///
///   {"op":"idle","ms":n} -> {"instructions":n|null}
///     Sleeps `ms` milliseconds and reports the instructions the process
///     retired meanwhile: the work of its background threads. .NET's tiered
///     JIT recompiles hot code on one for seconds after a burst of new work,
///     and how soon that lands depends on what else the machine is doing, so
///     `bench` runs measured before the process goes quiet count that work and
///     run code the JIT has not yet optimised. A caller wanting MSBuild's
///     steady state waits on this between batches.
///
/// Not an op: `FscArgsLogger`, which `borzoi-oracle-harness`'s `fsc_args`
/// driver loads into a real `dotnet msbuild -restore -t:Build` to record what
/// each `Fsc` invocation hands fsc.
///
/// The process takes one optional argument pair, `--msbuild-sdk <dir>`, which
/// pins it to the MSBuild of the SDK installed at `<dir>` instead of the one
/// `dotnet` resolves from the working directory (`registerMSBuild`).
/// A second optional pair, `--sdks-path <dir>`, last on the line, points MSBuild's
/// default SDK resolver at `<dir>` (`splitSdksPath`).
///
/// `project`, `items` and `itemsMeta` evaluate as a build does, through a
/// `ProjectInstance`; `Evaluation` has how that differs from the editable
/// `Project` a design-time host loads.
///
/// `globals` — on `project` and `items` — is MSBuild's **global property** set:
/// the `-p:` command line, and what an IDE-style consumer injects. It is not a
/// property group write. A global outranks every document write of the same
/// name (unless the document's `TreatAsLocalProperty` opts out), gates
/// conditions, selects `<Choose>` arms, and can steer an `<Import>`. Sweeping it
/// is the only way a differential can see whether a value we commit is a fixed
/// fact or an artefact of the globals the caller happened to guess: every other
/// op evaluates both sides under the *same* globals, so a global-dependence bug
/// agrees with MSBuild exactly and passes unnoticed.
///
/// `properties` is optional; each entry becomes a `<name>value</name>` in the
/// stub project's property group. Property names MUST be valid MSBuild/XML
/// identifiers and SHOULD stay disjoint from process environment variables and
/// MSBuild reserved names: MSBuild evaluation folds the environment in as
/// properties, and the Rust side only knows the map it sent, so a collision
/// would make the two disagree for reasons unrelated to the condition grammar.
/// The differential harness scrubs the environment and generates names from a
/// controlled set to guarantee this.
///
/// How a boolean is obtained: the stub declares a single guarded *item* (see
/// `stubXml`); the item is present iff MSBuild considers the condition true, so
/// we read back its count. An item — not a property — deliberately, so the
/// result lives in a namespace (`@(...)`) disjoint from everything a condition
/// references (`$(...)`); no property name a caller supplies or a condition
/// mentions can perturb it. Evaluation happens in-process against the installed
/// SDK's MSBuild (see the .fsproj note on MSBuildLocator), so it is the same
/// evaluator `dotnet msbuild` would run over the same stub — but ~7000×/s
/// instead of one process spawn per case.
///
/// Any *unexpected* per-request exception (a harness/generator bug — malformed
/// XML from an invalid property name, say — never a legitimate differential
/// result) is reported as {"error":..} on that line; the process itself never
/// dies mid-batch. An illegal *condition* is not an error: it is the
/// first-class {"ok":false} answer.
module MsBuildConditionOracle.Program

open System
open System.IO
open System.Security
open System.Text
open System.Text.Json
open System.Xml
open Microsoft.Build.Evaluation
open Microsoft.Build.Exceptions
open Microsoft.Build.Execution
open Microsoft.Build.Locator

/// The item whose presence encodes the condition's truth. Deliberately an
/// *item*, not a property: the condition is expressed purely in the property
/// namespace (`$(Name)`), so a result held in the item namespace (`@(Name)`)
/// cannot collide with anything a condition references or a caller supplies —
/// even a caller property or `$(...)` reference literally named
/// `_ConditionResult` leaves this item untouched.
[<Literal>]
let private ResultItem = "_ConditionResult"

/// The property whose evaluated text is the `expand` op's answer. As with
/// `ResultItem`, callers must keep it out of the value under test (a
/// `$(_ExpandResult)` self-reference would perturb the answer). Unlike the
/// condition case there is no disjoint namespace to hide in — an *expanded
/// value* is a property, so this must be a property — so the discipline is on
/// the caller (the differential harness generates disjoint names).
[<Literal>]
let private ResultProperty = "_ExpandResult"

/// `s` escaped as element text, with a carriage return written as a character
/// reference: MSBuild reading a project file keeps a CR (probed: a CRLF in a
/// property body counts two characters), and a reference reads as itself under
/// any XML reader, normalising or not.
let private escapeText (s: string) : string =
    (SecurityElement.Escape s).Replace("\r", "&#13;")

/// `s` escaped as an attribute value: as [`escapeText`], and a tab or line
/// feed as a character reference too, which an attribute-normalising reader
/// would otherwise read as a space.
let private escapeAttribute (s: string) : string =
    (escapeText s).Replace("\t", "&#9;").Replace("\n", "&#10;")

/// A reader over project text that reads it as MSBuild reads a project file
/// (`XmlReaderExtension.GetXmlReader`): an `XmlTextReader`, whose
/// `Normalization` is off, so a tab, line feed or carriage return in an
/// attribute value, and a CRLF anywhere, reach the evaluator as written. The
/// readers `XmlReader.Create` makes normalise both, so a document loaded
/// through one evaluates apart from the same document on disk.
let private projectReader (xml: string) : XmlReader =
    new XmlTextReader(new StringReader(xml), DtdProcessing = DtdProcessing.Ignore)

/// Build the stub project XML: the supplied properties in a `<PropertyGroup>`,
/// then a single `<_ConditionResult>` item guarded by `condition` — present iff
/// MSBuild considers the condition true. Everything is XML-escaped; property
/// *values* and the condition are attacker-controlled fuzz, so they go through
/// `SecurityElement.Escape`. Property *names* are trusted to be valid
/// identifiers (see the module docs) and are emitted verbatim.
///
/// What the caller sent is what MSBuild evaluates: see [`escapeText`] and
/// [`escapeAttribute`].
let private stubXml (condition: string) (properties: (string * string) seq) : string =
    let sb = StringBuilder()
    sb.Append "<Project><PropertyGroup>" |> ignore

    for (name, value) in properties do
        sb.Append('<').Append(name).Append('>') |> ignore
        sb.Append(escapeText value) |> ignore
        sb.Append("</").Append(name).Append('>') |> ignore

    sb.Append "</PropertyGroup><ItemGroup><" |> ignore
    sb.Append(ResultItem).Append(" Include=\"x\" Condition=\"") |> ignore
    sb.Append(escapeAttribute condition) |> ignore
    sb.Append "\" /></ItemGroup></Project>" |> ignore
    sb.ToString()

/// Evaluate `condition` against `properties` via a throwaway
/// `ProjectCollection` (so a long batch does not accumulate loaded projects in
/// the global collection). Returns `Some true`/`Some false` for a value MSBuild
/// computed, or `None` when MSBuild rejects the condition as illegal.
let private evalCondition (condition: string) (properties: (string * string) seq) : bool option =
    let xml = stubXml condition properties
    use collection = new ProjectCollection()
    use reader = projectReader xml
    // Create the root *in the throwaway collection* (the parameterless
    // overload caches it in the global collection instead, so a long batch
    // would accumulate thousands of roots there). Disposing `collection`
    // releases both the root and the evaluated project.
    let root = Microsoft.Build.Construction.ProjectRootElement.Create(reader, collection)

    try
        // `Project` construction evaluates eagerly — an illegal condition
        // throws here rather than at item read.
        let project = Project(root, null, null, collection)
        // `GetItems` returns post-condition items: the result item is present
        // iff MSBuild considered the guard true.
        Some(project.GetItems(ResultItem).Count > 0)
    with :? InvalidProjectFileException ->
        None

let private respondEval (root: JsonElement) : string =
    let condition = root.GetProperty("condition").GetString()

    let properties =
        match root.TryGetProperty "properties" with
        | true, props when props.ValueKind = JsonValueKind.Object ->
            props.EnumerateObject()
            |> Seq.map (fun p -> (p.Name, p.Value.GetString()))
            |> Seq.toArray
        | _ -> [||]

    match evalCondition condition properties with
    | Some value -> JsonSerializer.Serialize {| ok = true; value = value |}
    | None -> JsonSerializer.Serialize {| ok = false |}

/// Build the stub project XML for the `expand` op: the supplied properties,
/// then a `<_ExpandResult>` whose text is the value under test. Placed *after*
/// the supplied properties so a `$(Foo)` reference resolves to the value the
/// caller sent. Everything is XML-escaped; property values and the value under
/// test are attacker-controlled fuzz.
let private expandStubXml (value: string) (properties: (string * string) seq) : string =
    let sb = StringBuilder()
    sb.Append "<Project><PropertyGroup>" |> ignore

    for (name, propValue) in properties do
        sb.Append('<').Append(name).Append('>') |> ignore
        sb.Append(escapeText propValue) |> ignore
        sb.Append("</").Append(name).Append('>') |> ignore

    sb.Append('<').Append(ResultProperty).Append('>') |> ignore
    sb.Append(escapeText value) |> ignore
    sb.Append("</").Append(ResultProperty).Append('>') |> ignore
    sb.Append "</PropertyGroup></Project>" |> ignore
    sb.ToString()

/// Expand `value` as a property body against `properties`. `Some s` is the
/// evaluated text MSBuild produced (`""` when it reduces to empty — distinct
/// from an error); `None` when MSBuild throws evaluating it (a property
/// function that fails: an unparseable `Version`, an out-of-range indexer,
/// an unknown member). MSBuild evaluates properties eagerly at `Project`
/// construction, so those throw here, exactly like an illegal condition.
let private evalExpand (value: string) (properties: (string * string) seq) : string option =
    let xml = expandStubXml value properties
    use collection = new ProjectCollection()
    use reader = projectReader xml
    let root = Microsoft.Build.Construction.ProjectRootElement.Create(reader, collection)

    try
        let project = Project(root, null, null, collection)
        Some(project.GetPropertyValue ResultProperty)
    with :? InvalidProjectFileException ->
        None

let private respondExpand (root: JsonElement) : string =
    let value = root.GetProperty("value").GetString()

    let properties =
        match root.TryGetProperty "properties" with
        | true, props when props.ValueKind = JsonValueKind.Object ->
            props.EnumerateObject()
            |> Seq.map (fun p -> (p.Name, p.Value.GetString()))
            |> Seq.toArray
        | _ -> [||]

    match evalExpand value properties with
    | Some value -> JsonSerializer.Serialize {| ok = true; value = value |}
    | None -> JsonSerializer.Serialize {| ok = false |}

/// The evaluation `project`, `items` and `itemsMeta` answer from.
///
/// `Build` is a `ProjectInstance`, the evaluation a build runs on: `dotnet
/// build`, `dotnet restore` and `dotnet msbuild -t:…` evaluate through
/// `BuildManager`, which builds one. Every differential grades against it
/// unless it asks for the other.
///
/// `DesignTime` is the editable `Project`, the evaluation a design-time host
/// (Visual Studio's project system) loads, and the one `dotnet msbuild
/// -getProperty:` builds when it runs no target. It differs from a build in
/// two ways:
///
/// - it evaluates an `<ItemGroup>`'s items and their metadata whatever the
///   item's or the group's condition holds, to keep `ItemsIgnoringCondition`,
///   so an illegal condition on an item under a false `<ItemGroup>` rejects
///   the project, which a build evaluates without reading it (probed: `dotnet
///   msbuild -getProperty:` rejects such a project, `dotnet msbuild -t:` on
///   it builds);
/// - in this process it refuses a global named `MSBuildSDKsPath` ("is a
///   global property, and cannot be modified": `ProjectProperty` refuses a
///   non-global property of a global's name), which a build, and `dotnet
///   msbuild -p:`, accept.
///
/// Where both evaluate a document, they agree on every property and item the
/// differentials read (every `project`, `items` and `itemsMeta` request of
/// the crate's suite was run through both).
type private Evaluation =
    | Build
    | DesignTime

/// `globals` as MSBuild's global property set: `null` reads as none.
let private globalTable
    (globals: Collections.Generic.IDictionary<string, string>)
    : Collections.Generic.IDictionary<string, string> =
    match globals with
    | null -> Collections.Generic.Dictionary<string, string>() :> Collections.Generic.IDictionary<_, _>
    | globals -> globals

/// Write `xml` to `path`, creating its directory, so the evaluation loads it
/// as that file.
let private writeProject (path: string) (xml: string) =
    Directory.CreateDirectory(Path.GetDirectoryName path: string) |> ignore
    File.WriteAllText(path, xml)

/// Evaluate a *whole project* — the caller's XML verbatim, byte for byte, so
/// both sides see the same document — and read back the named properties.
/// `Some map` is what MSBuild computed; `None` when it rejects the project.
///
/// This is the `expand` op's structural counterpart: `expand` deliberately
/// anchors its value between sentinels and hands MSBuild a *body*, which makes
/// it blind to everything the XML layer does before expansion (insignificant
/// whitespace, entity decoding, CDATA, comment-split text). Handing over the
/// document itself is the only way to compare that layer.
///
/// A name MSBuild never defines reads back as `""` — indistinguishable from a
/// defined-empty property through this API. The Rust harness only asserts on
/// names it *committed* a value for, so that ambiguity costs nothing: a name we
/// dropped makes no claim either way.
/// With a `path`, the XML is written there and loaded *as that file*, so
/// MSBuild's reserved path derivatives (`MSBuildProjectDirectory`,
/// `MSBuildProjectName`, …) are computed from the same path the Rust side
/// passes to its own parser. That is the only way to diff anything those
/// properties feed — including the one case where a `%XX` is *not* an escape,
/// because it came from the project's own directory name.
///
/// `globals` is MSBuild's global property set (`null` for none), handed to the
/// evaluation rather than written into the document: a global is read-only to
/// the body it evaluates, which is precisely the behaviour a property-group
/// write could not reproduce.
let private evalProject
    (evaluation: Evaluation)
    (path: string option)
    (xml: string)
    (names: string seq)
    (globals: Collections.Generic.IDictionary<string, string>)
    : Map<string, string> option =
    use collection = new ProjectCollection()
    let globals = globalTable globals

    let read =
        try
            match evaluation, path with
            | Build, Some path ->
                writeProject path xml
                let instance = ProjectInstance(path, globals, null, collection)
                Some(fun (name: string) -> instance.GetPropertyValue name)
            | DesignTime, Some path ->
                writeProject path xml
                let project = Project(path, globals, null, collection)
                Some(fun (name: string) -> project.GetPropertyValue name)
            | evaluation, None ->
                // Create the root *in the throwaway collection*, so disposing
                // it releases both the root and the evaluation.
                use reader = projectReader xml
                let root = Microsoft.Build.Construction.ProjectRootElement.Create(reader, collection)

                match evaluation with
                | Build ->
                    let instance = ProjectInstance(root, globals, null, collection)
                    Some(fun (name: string) -> instance.GetPropertyValue name)
                | DesignTime ->
                    let project = Project(root, globals, null, collection)
                    Some(fun (name: string) -> project.GetPropertyValue name)
        with :? InvalidProjectFileException ->
            None

    read
    |> Option.map (fun read -> names |> Seq.map (fun name -> (name, read name)) |> Map.ofSeq)

/// The `project` op's item-side twin: evaluate the document *as a file at
/// `path`* and read back the `FullPath` of every `itemType` item, in evaluation
/// order. `None` when MSBuild rejects the project.
let private evalItems
    (path: string)
    (xml: string)
    (itemType: string)
    (globals: Collections.Generic.IDictionary<string, string>)
    : string list option =
    use collection = new ProjectCollection()

    try
        writeProject path xml
        let instance = ProjectInstance(path, globalTable globals, null, collection)

        instance.GetItems itemType
        |> Seq.map (fun item -> item.GetMetadataValue "FullPath")
        |> List.ofSeq
        |> Some
    with :? InvalidProjectFileException ->
        None

/// The request's optional `globals` object as MSBuild's global property set.
/// Absent (or not an object) reads back as `null` — MSBuild's own spelling for
/// "no globals" — so an op that never sends the field evaluates exactly as it
/// did before the field existed.
let private readGlobals (root: JsonElement) : Collections.Generic.IDictionary<string, string> =
    match root.TryGetProperty "globals" with
    | true, g when g.ValueKind = JsonValueKind.Object ->
        let table = Collections.Generic.Dictionary<string, string>()

        for entry in g.EnumerateObject() do
            table[entry.Name] <- entry.Value.GetString()

        table :> Collections.Generic.IDictionary<string, string>
    | _ -> null

/// The `elementContents` op: the text MSBuild reads of each property,
/// metadatum (an element's, not an attribute's) and inline task body,
/// unexpanded (`Utilities.GetXmlNodeInnerContents`), in document order. The
/// document is written to `path` and opened as that file, so it is read
/// exactly as a project file is (whitespace nodes dropped). `None` when
/// MSBuild refuses to load it.
let private elementContents (path: string) (xml: string) : string array option =
    use collection = new ProjectCollection()

    try
        writeProject path xml
        let element = Microsoft.Build.Construction.ProjectRootElement.Open(path, collection)

        element.AllChildren
        |> Seq.choose (fun child ->
            match child with
            | :? Microsoft.Build.Construction.ProjectPropertyElement as property -> Some property.Value
            | :? Microsoft.Build.Construction.ProjectMetadataElement as metadata when
                not metadata.ExpressedAsAttribute
                ->
                Some metadata.Value
            | :? Microsoft.Build.Construction.ProjectUsingTaskBodyElement as body -> Some body.TaskBody
            | _ -> None)
        |> Seq.toArray
        |> Some
    with :? InvalidProjectFileException ->
        None

let private respondElementContents (root: JsonElement) : string =
    let xml = root.GetProperty("xml").GetString()
    let path = root.GetProperty("path").GetString()

    match elementContents path xml with
    | Some contents -> JsonSerializer.Serialize {| ok = true; contents = contents |}
    | None -> JsonSerializer.Serialize {| ok = false |}

let private respondItems (root: JsonElement) : string =
    let xml = root.GetProperty("xml").GetString()
    let path = root.GetProperty("path").GetString()
    let itemType = root.GetProperty("itemType").GetString()

    match evalItems path xml itemType (readGlobals root) with
    | Some items -> JsonSerializer.Serialize {| ok = true; items = items |}
    | None -> JsonSerializer.Serialize {| ok = false |}

/// The `items` op enriched for dependency items: each item's `EvaluatedInclude`
/// (the identity `Update`/`Remove` match against), its escaped spelling (`a%2Ex`
/// where `EvaluatedInclude` reads `a.x`: the spelling every expansion of the
/// item list and every metadata derivation starts from), and the requested
/// metadata's evaluated values, in evaluation order. `None` when MSBuild
/// rejects the project.
/// With `DesignTime` (`Evaluation`), the items are the editable `Project`'s,
/// and the metadata values are escaped, as the SDK's targets compare them.
let private evalItemsMeta
    (evaluation: Evaluation)
    (path: string)
    (xml: string)
    (itemType: string)
    (metadata: string list)
    : (string * string * Map<string, string>) list option =
    use collection = new ProjectCollection()

    try
        writeProject path xml
        let globals = Collections.Generic.Dictionary<string, string>()

        match evaluation with
        | Build ->
            let instance = ProjectInstance(path, globals, null, collection)

            instance.GetItems itemType
            |> Seq.map (fun item ->
                let values =
                    metadata
                    |> List.map (fun name -> (name, item.GetMetadataValue name))
                    |> Map.ofList

                (item.EvaluatedInclude, (item :> Microsoft.Build.Framework.ITaskItem2).EvaluatedIncludeEscaped, values))
            |> List.ofSeq
            |> Some
        | DesignTime ->
            let project = Project(path, globals, null, collection)

            // Escaped, as the SDK's targets compare metadata
            // (`WithMetadataValue` reads `GetMetadataValueEscaped`): an
            // unescaped `Compile%46irst` would read as `CompileFirst`.
            project.GetItems itemType
            |> Seq.map (fun item ->
                let values =
                    metadata
                    |> List.map (fun name -> (name, Project.GetMetadataValueEscaped(item, name)))
                    |> Map.ofList

                (item.EvaluatedInclude, Project.GetEvaluatedItemIncludeEscaped item, values))
            |> List.ofSeq
            |> Some
    with :? InvalidProjectFileException ->
        None

let private respondItemsMeta (root: JsonElement) : string =
    let xml = root.GetProperty("xml").GetString()
    let path = root.GetProperty("path").GetString()
    let itemType = root.GetProperty("itemType").GetString()

    let metadata =
        root.GetProperty("metadata").EnumerateArray()
        |> Seq.map (fun n -> n.GetString())
        |> List.ofSeq

    let evaluation =
        match root.TryGetProperty "designTime" with
        | true, d when d.ValueKind = JsonValueKind.True -> DesignTime
        | _ -> Build

    match evalItemsMeta evaluation path xml itemType metadata with
    | Some items ->
        JsonSerializer.Serialize
            {| ok = true
               items =
                items
                |> List.map (fun (identity, escaped, values) ->
                    {| identity = identity
                       escaped = escaped
                       metadata = values |> Map.toSeq |> dict |}) |}
    | None -> JsonSerializer.Serialize {| ok = false |}

let private respondProject (root: JsonElement) : string =
    let xml = root.GetProperty("xml").GetString()

    let path =
        match root.TryGetProperty "path" with
        | true, p when p.ValueKind = JsonValueKind.String -> Some(p.GetString())
        | _ -> None

    let names =
        root.GetProperty("names").EnumerateArray()
        |> Seq.map (fun n -> n.GetString())
        |> Seq.toArray

    let evaluation =
        match root.TryGetProperty "designTime" with
        | true, d when d.ValueKind = JsonValueKind.True -> DesignTime
        | _ -> Build

    match evalProject evaluation path xml names (readGlobals root) with
    | Some values ->
        JsonSerializer.Serialize
            {| ok = true
               values = values |> Map.toSeq |> dict |}
    | None -> JsonSerializer.Serialize {| ok = false |}

/// The `rejectionCode` op: the design-time evaluation of `xml` as the file at
/// `path`, and the error code of the `InvalidProjectFileException` that
/// rejects it, if one does.
let private respondRejectionCode (root: JsonElement) : string =
    let xml = root.GetProperty("xml").GetString()
    let path = root.GetProperty("path").GetString()
    use collection = new ProjectCollection()
    writeProject path xml

    try
        Project(path, globalTable null, null, collection) |> ignore
        JsonSerializer.Serialize {| ok = true |}
    with :? InvalidProjectFileException as e ->
        JsonSerializer.Serialize
            {| ok = false
               code = e.ErrorCode
               message = e.BaseMessage
               line = e.LineNumber
               column = e.ColumnNumber |}

/// The `globalName` op: whether MSBuild takes `name` as a global property name,
/// or the exception it refuses it with. MSBuild refuses a reserved name
/// (`ReservedPropertyNames.IsReservedProperty`) and a name that is not a valid
/// element name, each before evaluating anything, so the document is empty.
///
/// The evaluation is a `ProjectInstance`, as a build's is (`dotnet msbuild`
/// evaluates through `BuildManager`), and as the `project` op's is
/// (`Evaluation`): the editable `Project` also refuses a global named
/// `MSBuildSDKsPath` in this process, which `-p:` sets freely.
let private respondGlobalName (root: JsonElement) : string =
    let name = root.GetProperty("name").GetString()
    use collection = new ProjectCollection()
    let globals = Collections.Generic.Dictionary<string, string>()
    globals[name] <- "x"

    try
        use reader = projectReader "<Project />"
        let element = Microsoft.Build.Construction.ProjectRootElement.Create(reader, collection)
        ProjectInstance(element, globals, null, collection) |> ignore
        JsonSerializer.Serialize {| accepted = true |}
    with ex ->
        JsonSerializer.Serialize
            {| accepted = false
               exceptionType = ex.GetType().FullName
               message = ex.Message |}

/// The `reservedNames` op: the names the loaded MSBuild reserves, read from
/// `Microsoft.Build.Internal.ReservedPropertyNames` by reflection. `names` is
/// every string constant of that class for which its own
/// `IsReservedProperty` holds; `table` is its `ReservedProperties` set where
/// the class keeps one (`null` otherwise); `kinds` counts the members of
/// `ReservedPropertyKind` other than `None` where that enum exists (`-1`
/// otherwise), one per reserved name, so a reserved name no constant spells
/// shows up as a count that disagrees with `names`.
let private respondReservedNames () : string =
    let flags =
        Reflection.BindingFlags.Static
        ||| Reflection.BindingFlags.Public
        ||| Reflection.BindingFlags.NonPublic

    let assembly = typeof<Project>.Assembly
    let names = assembly.GetType("Microsoft.Build.Internal.ReservedPropertyNames", true)
    let isReserved = names.GetMethod("IsReservedProperty", flags, [| typeof<string> |])

    let reserved =
        names.GetFields flags
        |> Array.filter (fun f -> f.IsLiteral && f.FieldType = typeof<string>)
        |> Array.map (fun f -> f.GetRawConstantValue() :?> string)
        |> Array.filter (fun n -> isReserved.Invoke(null, [| box n |]) :?> bool)
        |> Array.distinct
        |> Array.sort

    let table =
        match names.GetField("ReservedProperties", flags) with
        | null -> null
        | field -> (field.GetValue null :?> Collections.Generic.IEnumerable<string>) |> Seq.sort |> Array.ofSeq

    let kinds =
        match assembly.GetTypes() |> Array.tryFind (fun t -> t.IsEnum && t.Name = "ReservedPropertyKind") with
        | Some kind -> Enum.GetNames kind |> Array.filter (fun n -> n <> "None") |> Array.length
        | None -> -1

    JsonSerializer.Serialize
        {| names = reserved
           table = table
           kinds = kinds |}

/// The restore target whose execution the `restoreCone` op records: half A of
/// docs/nuget-dgspec-boundary-plan.md, what `dotnet msbuild
/// -t:GenerateRestoreGraphFile` runs.
[<Literal>]
let private RestoreGraphTarget = "GenerateRestoreGraphFile"

/// One target MSBuild executed (a `TargetStarted` event: its condition held and
/// it was not already built in that project instance).
type internal TargetRun =
    { Name: string
      File: string
      Project: string }

/// One task MSBuild executed (a `TaskStarted` event: its condition held). The
/// engine's intrinsic `PropertyGroup`/`ItemGroup` inside a target raise no such
/// event; they are MSBuild semantics, not task code.
type internal TaskRun =
    { Name: string
      Target: string
      File: string
      Assembly: string }

/// The executed targets and tasks as the `restoreCone` op reports them.
let internal targetsJson (targets: TargetRun list) =
    targets
    |> List.map (fun t ->
        {| name = t.Name
           file = t.File
           project = t.Project |})

let internal tasksJson (tasks: TaskRun list) =
    tasks
    |> List.map (fun t ->
        {| name = t.Name
           target = t.Target
           file = t.File
           assembly = t.Assembly |})

/// Records every target and task that starts, and every error. The containing
/// target of a task is found through its build event context, which names the
/// target instance it runs in.
///
/// Public so that `dotnet msbuild` can load it too
/// (`-logger:MsBuildConditionOracle.Program+ConeLogger,<this assembly>;<file>`):
/// given a file as its parameter, it writes the targets and tasks it saw there
/// as JSON when the build ends, in the `restoreCone` op's shape. That is how the
/// census compares the cone it measures in-process with the cone the CLI runs.
type ConeLogger() =
    let targets = ResizeArray<TargetRun>()
    let tasks = ResizeArray<TaskRun>()
    let errors = ResizeArray<string>()
    let targetNames = Collections.Generic.Dictionary<struct (int * int * int), string>()
    let taskNames = Collections.Generic.Dictionary<struct (int * int * int * int), string>()
    let writers =
        Collections.Generic.Dictionary<struct (int * int * int * int), Collections.Generic.Dictionary<string, obj list>>()

    let writerOrder = ResizeArray<struct (int * int * int * int)>()
    let mutable verbosity = Microsoft.Build.Framework.LoggerVerbosity.Normal
    let mutable parameters: string = null

    let contextKey (context: Microsoft.Build.Framework.BuildEventContext) =
        struct (context.NodeId, context.ProjectContextId, context.TargetId)

    member internal _.Targets = List.ofSeq targets
    member internal _.Tasks = List.ofSeq tasks
    member internal _.Errors = List.ofSeq errors
    /// Each `WriteRestoreGraphTask` invocation's inputs, by parameter, in the
    /// order the invocations started, as MSBuild logs a task's inputs (only when
    /// the build sets `LogTaskInputs`). An unset parameter is absent.
    member internal _.WriterInvocations = writerOrder |> Seq.map (fun key -> writers[key]) |> List.ofSeq

    interface Microsoft.Build.Framework.ILogger with
        member _.Verbosity
            with get () = verbosity
            and set v = verbosity <- v

        member _.Parameters
            with get () = parameters
            and set v = parameters <- v

        member _.Initialize(source: Microsoft.Build.Framework.IEventSource) =
            source.TargetStarted.Add(fun e ->
                targetNames[contextKey e.BuildEventContext] <- e.TargetName

                targets.Add
                    { Name = e.TargetName
                      File = e.TargetFile
                      Project = e.ProjectFile })

            source.TaskStarted.Add(fun e ->
                let c = e.BuildEventContext
                taskNames[struct (c.NodeId, c.ProjectContextId, c.TargetId, c.TaskId)] <- e.TaskName

                let target =
                    match targetNames.TryGetValue(contextKey e.BuildEventContext) with
                    | true, name -> name
                    | _ -> failwith $"task %s{e.TaskName} started outside any recorded target"

                tasks.Add
                    { Name = e.TaskName
                      Target = target
                      File = e.TaskFile
                      Assembly = e.TaskAssemblyLocation })

            source.MessageRaised.Add(fun e ->
                match e with
                | :? Microsoft.Build.Framework.TaskParameterEventArgs as p when
                    p.Kind = Microsoft.Build.Framework.TaskParameterMessageKind.TaskInput
                    ->
                    let c = p.BuildEventContext
                    let key = struct (c.NodeId, c.ProjectContextId, c.TargetId, c.TaskId)

                    match taskNames.TryGetValue key with
                    // By name, bare or qualified with its namespace, in any case, as
                    // MSBuild looks tasks up.
                    | true, name when
                        name.Equals("WriteRestoreGraphTask", StringComparison.OrdinalIgnoreCase)
                        || name.EndsWith(".WriteRestoreGraphTask", StringComparison.OrdinalIgnoreCase)
                        ->
                        if not (writers.ContainsKey key) then
                            writers[key] <- Collections.Generic.Dictionary<string, obj list>()
                            writerOrder.Add key

                        writers[key][p.ItemType] <- p.Items |> Seq.cast<obj> |> List.ofSeq
                    | _ -> ()
                | _ -> ())

            source.ErrorRaised.Add(fun e -> errors.Add $"%s{e.File}(%d{e.LineNumber}): %s{e.Code} %s{e.Message}")

        member _.Shutdown() =
            if not (String.IsNullOrEmpty parameters) then
                let cone =
                    {| targets = targetsJson (List.ofSeq targets)
                       tasks = tasksJson (List.ofSeq tasks)
                       errors = List.ofSeq errors |}

                File.WriteAllText(parameters, JsonSerializer.Serialize cone)

/// Whether a task MSBuild ran is the `Fsc` task: by name, bare or qualified
/// with its namespace, in any case, as MSBuild looks tasks up.
let private isFsc (name: string) =
    name.Equals("Fsc", StringComparison.OrdinalIgnoreCase)
    || name.EndsWith(".Fsc", StringComparison.OrdinalIgnoreCase)

/// The `Fsc` task's parameters that choose the program it runs.
let private compilerParameters = [ "ToolPath"; "ToolExe"; "DotnetFscCompilerPath" ]

/// One `Fsc` invocation as [`FscArgsLogger`] sees it.
type private FscRun =
    { Project: string
      Globals: Collections.Generic.IDictionary<string, string>
      Assembly: string
      Inputs: Collections.Generic.Dictionary<string, string>
      Messages: ResizeArray<string>
      /// What fsc itself said, in the task's context: its banner on standard
      /// output (`Microsoft (R) F# Compiler …`, which `ToolTask` logs), and
      /// its diagnostics (errors and warnings coded `FS…`). Evidence that fsc
      /// ran, tied to this invocation.
      CompilerOutput: ResizeArray<string> }

/// The response file `run` handed fsc, read off the command line the task
/// logged before running it (`ToolTask` logs
/// `<tool path> <command-line commands> <response-file commands>`; `Fsc`'s
/// tool path is `ToolPath` joined with `ToolExe`, and its command-line
/// commands are its `DotnetFscCompilerPath`, verbatim), or why it cannot be.
///
/// Only for the SDK's own launch, where all three are logged (a parameter
/// whose logging a project suppresses is indistinguishable from an empty one)
/// and `DotnetFscCompilerPath` is one quoted path, the compiler's: anything
/// more would reach fsc as arguments of its own, ahead of the response file.
/// The driver checks that the paths are the build's `dotnet` host and its
/// SDK's `fsc.dll`.
let private responseFileOf (run: FscRun) : Result<string, string> =
    let logged = compilerParameters |> List.forall run.Inputs.ContainsKey

    let input name =
        match run.Inputs.TryGetValue name with
        | true, value -> value
        | _ -> ""

    let tool = Path.Combine(input "ToolPath", input "ToolExe")
    let compiler = input "DotnetFscCompilerPath"

    let pathAlone =
        compiler.Length >= 2
        && compiler.StartsWith "\""
        && compiler.EndsWith "\""
        && not (compiler.Substring(1, compiler.Length - 2).Contains '"')

    let prefix = tool + " " + compiler + " "

    if not logged then
        Error $"the compiler's launch was not logged in full: %A{List.ofSeq run.Inputs.Keys}"
    elif not pathAlone then
        Error $"DotnetFscCompilerPath is not one quoted path: %s{compiler}"
    else
        match run.Messages |> Seq.filter (fun m -> m.StartsWith(prefix, StringComparison.Ordinal)) |> List.ofSeq with
        | [ message ] -> Ok(message.Substring prefix.Length)
        | [] -> Error $"Fsc logged no command line starting %s{prefix}"
        | many -> Error $"Fsc logged %d{many.Length} command lines"

/// Records every `Fsc` invocation of a real build, for the `fsc_args` driver
/// in `borzoi-oracle-harness`, which loads it into `dotnet msbuild -restore
/// -t:Build` (`-logger:MsBuildConditionOracle.Program+FscArgsLogger,<this
/// assembly>;<file>`). When the build ends it writes to `<file>`, as JSON,
/// whether the build succeeded, its errors, and for each invocation the
/// project and global properties it ran under, the task assembly, the
/// parameters choosing the program it runs (MSBuild logs a task's inputs only
/// when asked: the driver asks with a diagnostic file log, which sets nothing
/// the build can read), the diagnostics fsc itself reported, and the response
/// file it handed fsc (or why that could not be read).
///
/// That `Fsc` started is MSBuild's account; that fsc ran is fsc's own: its
/// banner or diagnostics in the task's context. The report also carries the
/// program running the build (`Environment.ProcessPath`, the `dotnet` host)
/// and the directory of the MSBuild running it (its SDK's), which the driver
/// holds the launch to.
///
/// A real build, not an imitation of one: the restore, the targets, the
/// project references and the compiler are the CLI's own, so what it reports
/// is what fsc is handed, and an invocation that never happens is one a real
/// build does not make.
type FscArgsLogger() =
    let errors = ResizeArray<string>()
    let projects = Collections.Generic.Dictionary<int, string * Collections.Generic.IDictionary<string, string>>()
    let runs = Collections.Generic.Dictionary<struct (int * int * int * int), FscRun>()
    let order = ResizeArray<struct (int * int * int * int)>()
    let mutable succeeded = false
    let mutable verbosity = Microsoft.Build.Framework.LoggerVerbosity.Normal
    let mutable parameters: string = null

    let key (c: Microsoft.Build.Framework.BuildEventContext) =
        struct (c.NodeId, c.ProjectContextId, c.TargetId, c.TaskId)

    interface Microsoft.Build.Framework.ILogger with
        member _.Verbosity
            with get () = verbosity
            and set v = verbosity <- v

        member _.Parameters
            with get () = parameters
            and set v = parameters <- v

        member _.Initialize(source: Microsoft.Build.Framework.IEventSource) =
            source.ProjectStarted.Add(fun e ->
                let globals =
                    match e.GlobalProperties with
                    | null -> Collections.Generic.Dictionary<string, string>() :> Collections.Generic.IDictionary<_, _>
                    | globals -> globals

                projects[e.BuildEventContext.ProjectContextId] <- (e.ProjectFile, globals))

            source.TaskStarted.Add(fun e ->
                if isFsc e.TaskName then
                    let k = key e.BuildEventContext

                    let project, globals =
                        match projects.TryGetValue e.BuildEventContext.ProjectContextId with
                        | true, found -> found
                        | _ -> (e.ProjectFile, Collections.Generic.Dictionary<string, string>() :> _)

                    runs[k] <-
                        { Project = project
                          Globals = globals
                          Assembly = e.TaskAssemblyLocation
                          Inputs = Collections.Generic.Dictionary<string, string>()
                          Messages = ResizeArray<string>()
                          CompilerOutput = ResizeArray<string>() }

                    order.Add k)

            source.MessageRaised.Add(fun e ->
                let run =
                    match e.BuildEventContext with
                    | null -> None
                    | context ->
                        match runs.TryGetValue(key context) with
                        | true, run -> Some run
                        | _ -> None

                match run, e with
                | Some run, (:? Microsoft.Build.Framework.TaskParameterEventArgs as p) ->
                    if
                        p.Kind = Microsoft.Build.Framework.TaskParameterMessageKind.TaskInput
                        && List.contains p.ItemType compilerParameters
                    then
                        run.Inputs[p.ItemType] <-
                            match p.Items |> Seq.cast<obj> |> List.ofSeq with
                            | [ :? string as value ] -> value
                            | [ :? Microsoft.Build.Framework.ITaskItem as item ] -> item.ItemSpec
                            | items -> String.Join(";", items)
                | Some run, e ->
                    run.Messages.Add e.Message

                    if not (isNull e.Message) && e.Message.StartsWith("Microsoft (R) F# Compiler", StringComparison.Ordinal) then
                        run.CompilerOutput.Add e.Message
                | None, _ -> ())

            let compilerSpoke (context: Microsoft.Build.Framework.BuildEventContext) (code: string) message =
                match context with
                | null -> ()
                | context ->
                    match runs.TryGetValue(key context) with
                    | true, run when not (isNull code) && code.StartsWith("FS", StringComparison.Ordinal) ->
                        run.CompilerOutput.Add $"%s{code} %s{message}"
                    | _ -> ()

            source.ErrorRaised.Add(fun e ->
                errors.Add $"%s{e.File}(%d{e.LineNumber}): %s{e.Code} %s{e.Message}"
                compilerSpoke e.BuildEventContext e.Code e.Message)

            source.WarningRaised.Add(fun e -> compilerSpoke e.BuildEventContext e.Code e.Message)

            source.BuildFinished.Add(fun e -> succeeded <- e.Succeeded)

        member _.Shutdown() =
            if not (String.IsNullOrEmpty parameters) then
                let invocations =
                    order
                    |> Seq.map (fun k ->
                        let run = runs[k]
                        let file, problem =
                            match responseFileOf run with
                            | Ok file -> file, null
                            | Error why -> null, why

                        {| project = run.Project
                           globals = run.Globals
                           taskAssembly = run.Assembly
                           compiler = run.Inputs
                           responseFile = file
                           compilerOutput = List.ofSeq run.CompilerOutput
                           problem = problem |})
                    |> List.ofSeq

                File.WriteAllText(
                    parameters,
                    JsonSerializer.Serialize
                        {| succeeded = succeeded
                           errors = List.ofSeq errors
                           processPath = Environment.ProcessPath
                           msbuildDirectory =
                            Path.GetDirectoryName typeof<Microsoft.Build.Framework.ILogger>.Assembly.Location
                           invocations = invocations |}
                )

/// Every assembly loaded while a `restoreCone` build ran, across the process's
/// life, by path. Task assemblies load their dependencies lazily, as the code
/// that needs them first runs, so this is the code the builds reached, beyond
/// the task assemblies themselves. An assembly the oracle had already loaded
/// before its first build (MSBuild's own evaluator, the runtime) is not here.
let private loadedDuringBuilds = Collections.Generic.HashSet<string>()

let mutable private building = false

let private recordLoad (args: AssemblyLoadEventArgs) =
    if building && not args.LoadedAssembly.IsDynamic && args.LoadedAssembly.Location <> "" then
        loadedDuringBuilds.Add args.LoadedAssembly.Location |> ignore

let private sha256Hex (path: string) : string =
    Convert.ToHexString(Security.Cryptography.SHA256.HashData(File.ReadAllBytes path)).ToLowerInvariant()

/// A task assembly's identity, independent of the host: its simple name, its
/// version, and its informational version, which names the commit the SDK was
/// built from. Neither the file's bytes nor its module MVID would do: each
/// platform's SDK compiles the IL separately and precompiles it natively, so
/// both differ between the macOS and Linux builds of one SDK.
let private assemblyIdentity (path: string) =
    let name = Reflection.AssemblyName.GetAssemblyName path

    {| name = name.Name
       version = string name.Version
       informationalVersion = Diagnostics.FileVersionInfo.GetVersionInfo(path).ProductVersion |}

/// Run `GenerateRestoreGraphFile` on `project` under `globals`, in-process, with
/// a [`ConeLogger`] attached: the targets and tasks it executed, the content
/// hash of every file defining one of those targets (and holding one of those
/// tasks), the identity of every task assembly, whether the build succeeded,
/// and the spec it wrote to `RestoreGraphOutputPath`.
///
/// One node, in this process, no node reuse: the census is of what runs, and
/// an out-of-process node would run it where no logger of ours could see the
/// task assemblies load.
let private restoreCone (project: string) (globals: Collections.Generic.IDictionary<string, string>) =
    use collection = new ProjectCollection()
    let logger = ConeLogger()

    let parameters =
        BuildParameters(
            collection,
            Loggers = [ logger :> Microsoft.Build.Framework.ILogger ],
            MaxNodeCount = 1,
            EnableNodeReuse = false,
            // So that `WriteRestoreGraphTask`'s input is logged, and recorded.
            LogTaskInputs = true
        )

    let request =
        BuildRequestData(
            project,
            globals,
            null,
            [| RestoreGraphTarget |],
            null,
            BuildRequestDataFlags.ProvideProjectStateAfterBuild
        )

    building <- true

    let result =
        try
            BuildManager.DefaultBuildManager.Build(parameters, request)
        finally
            building <- false

    let targets = logger.Targets
    let tasks = logger.Tasks

    let files =
        Seq.append (targets |> Seq.map _.File) (tasks |> Seq.map _.File)
        |> Seq.distinct
        |> Seq.map (fun file -> (file, sha256Hex file))
        |> dict

    let assemblies =
        tasks
        |> Seq.map _.Assembly
        |> Seq.distinct
        |> Seq.map (fun path -> (path, assemblyIdentity path))
        |> dict

    let state = result.ProjectStateAfterBuild

    let property name =
        if isNull state then null else state.GetPropertyValue name

    let dgspec =
        match globals.TryGetValue "RestoreGraphOutputPath" with
        | true, path when File.Exists path -> File.ReadAllText path
        | _ -> null

    // The inputs of the writer invocation that wrote the requested spec: a
    // hook may run the task again for another file, and change the properties
    // its inputs come from after it ran. Every input is as the invocation was
    // handed it. `null` unless exactly one invocation wrote the requested path.
    let writer =
        let scalar (inputs: Collections.Generic.Dictionary<string, obj list>) name =
            match inputs.TryGetValue name with
            | true, [ :? string as value ] -> Some value
            // A bool parameter is logged as the boxed value it was converted to.
            | true, [ :? bool as value ] -> Some(if value then "true" else "false")
            | true, [ :? Microsoft.Build.Framework.ITaskItem as item ] -> Some item.ItemSpec
            | _ -> None

        let requested =
            match globals.TryGetValue "RestoreGraphOutputPath" with
            | true, path -> Some(Path.GetFullPath path)
            | _ -> None

        let writing =
            logger.WriterInvocations
            |> List.filter (fun inputs ->
                requested.IsSome
                && (scalar inputs "RestoreGraphOutputPath" |> Option.map Path.GetFullPath) = requested)

        match writing with
        | [ inputs ] ->
            let items =
                match inputs.TryGetValue "RestoreGraphItems" with
                | true, items -> items |> List.map (fun item -> item :?> Microsoft.Build.Framework.ITaskItem)
                | _ -> []

            box
                {| restoreRecursive = scalar inputs "RestoreRecursive" |> Option.toObj
                   invocations = logger.WriterInvocations.Length
                   entries =
                    items
                    |> List.map (fun item ->
                        {| identity = item.ItemSpec
                           metadata =
                            item.CloneCustomMetadata().Keys
                            |> Seq.cast<string>
                            |> Seq.sort
                            |> Seq.map (fun name -> (name, item.GetMetadata name))
                            |> dict |}) |}
        | _ -> null

    {| ok = true
       succeeded = (result.OverallResult = BuildResultCode.Success)
       errors = logger.Errors
       msbuildDirectory = Path.GetDirectoryName(typeof<Project>.Assembly.Location)
       sdkVersion = property "NETCoreSdkVersion"
       targets = targetsJson targets
       tasks = tasksJson tasks
       files = files
       assemblies = assemblies
       loadedDuringBuilds =
        loadedDuringBuilds
        |> Seq.sort
        |> Seq.map (fun path ->
            {| path = path
               name = Reflection.AssemblyName.GetAssemblyName(path).Name
               informationalVersion = Diagnostics.FileVersionInfo.GetVersionInfo(path).ProductVersion |})
        |> List.ofSeq
       dgspec = dgspec
       writer = writer |}

let private respondRestoreCone (root: JsonElement) : string =
    let project = root.GetProperty("project").GetString()

    match readGlobals root with
    | null -> JsonSerializer.Serialize {| error = "restoreCone needs a globals object" |}
    | globals -> JsonSerializer.Serialize(restoreCone project globals)

/// The `evaluated` op: evaluate the project file at `project` under `globals`,
/// without building it, and read back each named property (`null` when unset)
/// and each named item type's items, with their custom and item-definition
/// metadata, in order. This is the evaluation the restore targets run on, which
/// the restore-cone census reads against ours (stage A₁.3a).
let private evaluated
    (project: string)
    (globals: Collections.Generic.IDictionary<string, string>)
    (properties: string list)
    (itemTypes: string list)
    (targets: string list)
    =
    use collection = new ProjectCollection()
    let instance = ProjectInstance(project, globals, null, collection)

    {| ok = true
       targets =
        targets
        |> List.map (fun name ->
            match instance.Targets.TryGetValue name with
            | true, target ->
                (name,
                 box
                     {| file = target.FullPath
                        line = target.Location.Line
                        column = target.Location.Column |})
            | _ -> (name, null))
        |> dict
       properties =
        properties
        |> List.map (fun name ->
            match instance.GetProperty name with
            | null -> (name, null)
            | p -> (name, p.EvaluatedValue))
        |> dict
       items =
        itemTypes
        |> List.map (fun itemType ->
            let items =
                instance.GetItems itemType
                |> Seq.map (fun item ->
                    {| identity = item.EvaluatedInclude
                       metadata =
                        item.Metadata
                        |> Seq.sortBy (fun m -> m.Name)
                        |> Seq.map (fun m -> (m.Name, m.EvaluatedValue))
                        |> dict |})
                |> List.ofSeq

            (itemType, items))
        |> dict |}

let private respondEvaluated (root: JsonElement) : string =
    let project = root.GetProperty("project").GetString()

    let names (field: string) =
        root.GetProperty(field).EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq

    // `targets` is optional: the names to look up in MSBuild's own target table.
    let targets =
        match root.TryGetProperty "targets" with
        | true, _ -> names "targets"
        | _ -> []

    match readGlobals root with
    | null -> JsonSerializer.Serialize {| error = "evaluated needs a globals object" |}
    | globals ->
        try
            JsonSerializer.Serialize(evaluated project globals (names "properties") (names "items") targets)
        with :? InvalidProjectFileException ->
            JsonSerializer.Serialize {| ok = false |}

/// The `targetItems` op: evaluate the project file at `path` as it stands on
/// disk, execute `target` on that evaluation in-process, and read back the
/// `FullPath` of every `itemType` item the build leaves, in order. `None` when
/// MSBuild rejects the project at evaluation.
///
/// This is how a differential sees what a target makes of the evaluated items
/// (F#'s `FSharpSourceCodeCompileOrder` reorders the Compile list) without a
/// `dotnet msbuild` per case. The target runs in this process on one node, as
/// `restoreCone`'s does.
let private targetItems
    (path: string)
    (target: string)
    (itemType: string)
    (globals: Collections.Generic.IDictionary<string, string>)
    =
    use collection = new ProjectCollection()

    let globals =
        match globals with
        | null -> Collections.Generic.Dictionary<string, string>() :> Collections.Generic.IDictionary<_, _>
        | globals -> globals

    try
        let instance = ProjectInstance(path, globals, null, collection)
        let logger = ConeLogger()

        let succeeded =
            instance.Build([| target |], [ logger :> Microsoft.Build.Framework.ILogger ])

        Some(
            succeeded,
            logger.Errors,
            instance.GetItems itemType
            |> Seq.map (fun item -> item.GetMetadataValue "FullPath")
            |> List.ofSeq
        )
    with :? InvalidProjectFileException ->
        None

let private respondTargetItems (root: JsonElement) : string =
    let path = root.GetProperty("path").GetString()
    let target = root.GetProperty("target").GetString()
    let itemType = root.GetProperty("itemType").GetString()

    match targetItems path target itemType (readGlobals root) with
    | Some(succeeded, errors, items) ->
        JsonSerializer.Serialize
            {| ok = true
               succeeded = succeeded
               errors = errors
               items = items |}
    | None -> JsonSerializer.Serialize {| ok = false |}

/// The `runTargets` op: evaluate the project file at `path`, build `targets`
/// on that evaluation in-process, and read back every target that started, in
/// order, each named property (null when unset), and each named item type's
/// items with their escaped spellings and metadata. `None` when MSBuild
/// rejects the project at evaluation. What A₁.3c's executor is held to on
/// generated targets.
let private runTargets
    (path: string)
    (targets: string list)
    (properties: string list)
    (itemTypes: string list)
    =
    use collection = new ProjectCollection()

    try
        let instance =
            ProjectInstance(path, Collections.Generic.Dictionary<string, string>(), null, collection)

        let logger = ConeLogger()

        let succeeded =
            instance.Build(List.toArray targets, [ logger :> Microsoft.Build.Framework.ILogger ])

        Some
            {| ok = true
               succeeded = succeeded
               errors = logger.Errors
               targets = logger.Targets |> List.map (fun t -> t.Name)
               properties =
                properties
                |> List.map (fun name ->
                    match instance.GetProperty name with
                    | null -> (name, null)
                    | p -> (name, p.EvaluatedValue))
                |> dict
               items =
                itemTypes
                |> List.map (fun itemType ->
                    let items =
                        instance.GetItems itemType
                        |> Seq.map (fun item ->
                            {| identity = item.EvaluatedInclude
                               escaped = (item :> Microsoft.Build.Framework.ITaskItem2).EvaluatedIncludeEscaped
                               metadata =
                                item.Metadata
                                |> Seq.sortBy (fun m -> m.Name)
                                |> Seq.map (fun m -> (m.Name, m.EvaluatedValue))
                                |> dict |})
                        |> List.ofSeq

                    (itemType, items))
                |> dict |}
    with :? InvalidProjectFileException ->
        None

let private respondRunTargets (root: JsonElement) : string =
    let names (field: string) =
        root.GetProperty(field).EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq

    match runTargets (root.GetProperty("path").GetString()) (names "targets") (names "properties") (names "items") with
    | Some answer -> JsonSerializer.Serialize answer
    | None -> JsonSerializer.Serialize {| ok = false |}

/// `proc_pid_rusage`, macOS's per-process resource counters, the same call
/// `crates/lsp/examples/eval_counts.rs` reads for our side, so the two
/// processes' instruction counts are one kernel counter read the same way.
[<Runtime.InteropServices.DllImport("/usr/lib/libSystem.B.dylib")>]
extern int private proc_pid_rusage(int pid, int flavor, uint64[] buffer)

/// Instructions this process has retired so far (`ri_instructions` of
/// `rusage_info_v4`, kernel mode included), or `None` off macOS. Counts every
/// thread, so the JIT's, the GC's and tiered recompilation's work is in it:
/// what a resident MSBuild host pays, wherever in the process it pays it.
let private instructionsRetired () : uint64 option =
    if OperatingSystem.IsMacOS() then
        // `rusage_info_v4` is a 16-byte UUID followed by `u64`s; 64 words is
        // larger than its 37.
        let buffer = Array.zeroCreate<uint64> 64

        if proc_pid_rusage (Environment.ProcessId, 4, buffer) = 0 then
            Some buffer[2 + 29]
        else
            None
    else
        None

/// A logger that keeps only error messages: the cheapest way to say why a
/// build failed, so the benchmark measures the build rather than its logging.
type private ErrorLogger() =
    let errors = ResizeArray<string>()
    member _.Errors = List.ofSeq errors

    interface Microsoft.Build.Framework.ILogger with
        member val Verbosity = Microsoft.Build.Framework.LoggerVerbosity.Quiet with get, set
        member val Parameters: string = null with get, set
        member _.Initialize(source: Microsoft.Build.Framework.IEventSource) = source.ErrorRaised.Add(fun e -> errors.Add e.Message)
        member _.Shutdown() = ()

/// The global properties Ionide.ProjInfo (FsAutoComplete's project loader)
/// sets for a design-time build (`ProjectLoader.getGlobalProps`), on top of the
/// request's globals, with `tfm` as `TargetFramework` when given.
let private projInfoGlobals
    (globals: Collections.Generic.IDictionary<string, string>)
    (scratch: string)
    (tfm: string option)
    =
    let table = Collections.Generic.Dictionary<string, string>(globals)

    for name, value in
        [ "ProvideCommandLineArgs", "true"
          "DesignTimeBuild", "true"
          "SkipCompilerExecution", "true"
          "GeneratePackageOnBuild", "false"
          "Configuration", "Debug"
          "DefineExplicitDefaults", "true"
          "BuildProjectReferences", "false"
          "UseCommonOutputDirectory", "false"
          "NonExistentFile", Path.Combine("__NonExistentSubDir__", "__NonExistentFile__")
          "DotnetProjInfo", "true"
          // Not ProjInfo's: the targets below write into the intermediate
          // directory (the compile-inputs cache, the generated AssemblyInfo)
          // and create the output directory, which for a benchmark must not be
          // the project's own `obj/` and `bin/`. `BaseIntermediateOutputPath`,
          // and so where the assets file is read from, is left alone.
          "IntermediateOutputPath", Path.Combine(scratch, "obj") + string Path.DirectorySeparatorChar
          "OutDir", Path.Combine(scratch, "bin") + string Path.DirectorySeparatorChar ] do
        table[name] <- value

    tfm |> Option.iter (fun tfm -> table["TargetFramework"] <- tfm)
    table :> Collections.Generic.IDictionary<string, string>

/// Ionide.ProjInfo's design-time targets for an SDK-style project
/// (`ProjectLoader.designTimeBuildTargets false`).
let private projInfoTargets =
    [| "ResolveAssemblyReferencesDesignTime"
       "ResolveProjectReferencesDesignTime"
       "ResolvePackageDependenciesDesignTime"
       "FindReferenceAssembliesForReferences"
       "_GenerateCompileDependencyCache"
       "_ComputeNonExistentFileProperty"
       "BeforeBuild"
       "BeforeCompile"
       "CoreCompile" |]

/// What a caller compares with its own evaluation of the project, to tell the
/// two evaluated the same project on the same toolset: the MSBuild that ran
/// and the `Compile` items, in order.
let private evaluationSummary (instance: ProjectInstance) : string * string list =
    instance.GetPropertyValue "MSBuildBinPath",
    instance.GetItems "Compile" |> Seq.map (fun item -> item.GetMetadataValue "FullPath") |> List.ofSeq

/// The collection the `bench` op's "shared" mode evaluates in, kept for the
/// process's life, so its caches outlast any one request as a resident
/// host's do. Typed `obj` because a module-level value is initialised at
/// start-up, and naming a `Microsoft.Build` type there loads the pinned
/// reference assembly before `registerMSBuild` redirects the loader.
let mutable private benchShared: obj = null

let private benchSharedCollection () : ProjectCollection =
    match benchShared with
    | :? ProjectCollection as collection -> collection
    | _ ->
        let collection = new ProjectCollection()
        benchShared <- collection
        collection

/// One design-time build as Ionide.ProjInfo's `ProjectLoader.loadProject`
/// performs it for an SDK-style project: in a fresh collection, evaluate once
/// to read the target framework (`TargetFramework`, else the first of
/// `TargetFrameworks`), evaluate again with it as a global (unless that
/// leaves the globals unchanged), and build
/// `projInfoTargets` on that evaluation. Returns the evaluation the build ran
/// on, as `evaluationSummary` reads it before the targets change it, or the
/// build's errors when it fails. ProjInfo's loggers (a string writer and its
/// log provider) are left out, so this is cheaper than what ProjInfo runs,
/// never dearer.
let private projInfoDesignTimeBuild
    (project: string)
    (globals: Collections.Generic.IDictionary<string, string>)
    (scratch: string)
    : Result<string * string list, string list> =
    use collection = new ProjectCollection()
    let settings = ProjectLoadSettings.IgnoreMissingImports ||| ProjectLoadSettings.IgnoreInvalidImports

    let load properties =
        Project(project, properties, null, collection, settings)

    let readingGlobals = projInfoGlobals globals scratch None
    let readingProject = load readingGlobals
    let reading = readingProject.CreateProjectInstance()

    let tfm =
        match reading.GetPropertyValue "TargetFramework" with
        | tfm when not (String.IsNullOrWhiteSpace tfm) -> Some tfm
        | _ ->
            match reading.GetPropertyValue "TargetFrameworks" with
            | null -> None
            | tfms -> tfms.Split ';' |> Array.tryHead

    // ProjInfo looks the second load up in the collection first
    // (`findOrCreateMatchingProject`), and MSBuild refuses a second project of
    // the same path and globals, so a framework the request's globals already
    // chose reuses the first load.
    let buildGlobals = projInfoGlobals globals scratch tfm

    let sameGlobals =
        readingGlobals.Count = buildGlobals.Count
        && readingGlobals
           |> Seq.forall (fun entry ->
               match buildGlobals.TryGetValue entry.Key with
               | true, value -> value = entry.Value
               | _ -> false)

    let buildProject = if sameGlobals then readingProject else load buildGlobals
    let instance = buildProject.CreateProjectInstance()
    let evaluated = evaluationSummary instance
    let logger = ErrorLogger()

    if instance.Build(projInfoTargets, [ logger :> Microsoft.Build.Framework.ILogger ]) then
        Ok evaluated
    else
        Error logger.Errors

/// The `bench` op: run one way of getting a project's evaluation `reps` times
/// in this process and report what each run cost, in order, so the caller can
/// tell the first (JIT-cold) run from the warm ones. See the op's entry in the
/// header for the modes.
let private bench
    (project: string)
    (globals: Collections.Generic.IDictionary<string, string>)
    (mode: string)
    (reps: int)
    (scratch: string)
    =
    let evaluate (collection: ProjectCollection) =
        ProjectInstance(project, globals, null, collection)

    // Each run returns how to summarise the evaluation it measured, which the
    // loop calls outside the measured window. The design-time build must
    // summarise inside it, before its targets add to the items.
    let body: unit -> Result<unit -> string * string list, string list> =
        match mode with
        | "fresh" ->
            fun () ->
                use collection = new ProjectCollection()
                let instance = evaluate collection
                Ok(fun () -> evaluationSummary instance)
        | "shared" ->
            fun () ->
                let instance = evaluate (benchSharedCollection ())
                Ok(fun () -> evaluationSummary instance)
        | "designTime" ->
            fun () -> projInfoDesignTimeBuild project globals scratch |> Result.map (fun summary () -> summary)
        | other -> failwith $"unknown bench mode: %s{other}"

    let runs = ResizeArray()
    let mutable failure = None
    let mutable summary = None

    for _ in 1..reps do
        if failure.IsNone then
            let bytes0 = GC.GetTotalAllocatedBytes true
            let instructions0 = instructionsRetired ()
            let result = body ()
            let instructions1 = instructionsRetired ()
            let bytes1 = GC.GetTotalAllocatedBytes true

            match result with
            | Error errors -> failure <- Some errors
            | Ok summarise ->
                summary <- Some(summarise ())

                runs.Add
                    {| instructions =
                        match instructions0, instructions1 with
                        | Some i0, Some i1 -> Nullable(i1 - i0)
                        | _ -> Nullable()
                       allocatedBytes = bytes1 - bytes0 |}

    let msbuildBinPath, compile =
        match summary with
        | Some(binPath, compile) -> binPath, compile
        | None -> null, []

    {| ok = failure.IsNone
       errors = defaultArg failure []
       runs = List.ofSeq runs
       processInstructions = Option.toNullable (instructionsRetired ())
       msbuildBinPath = msbuildBinPath
       compile = compile |}

/// The `idle` op: sleep for `ms` milliseconds and report the instructions the
/// process retired meanwhile, which is the work its background threads did.
let private respondIdle (root: JsonElement) : string =
    let before = instructionsRetired ()
    Threading.Thread.Sleep(root.GetProperty("ms").GetInt32())
    let after = instructionsRetired ()

    JsonSerializer.Serialize
        {| instructions =
            match before, after with
            | Some i0, Some i1 -> Nullable(i1 - i0)
            | _ -> Nullable() |}

let private respondBench (root: JsonElement) : string =
    let globals =
        match readGlobals root with
        | null -> Collections.Generic.Dictionary<string, string>() :> Collections.Generic.IDictionary<string, string>
        | globals -> globals

    let scratch =
        match root.TryGetProperty "scratch" with
        | true, s -> s.GetString()
        | _ -> null

    let mode = root.GetProperty("mode").GetString()

    if mode = "designTime" && isNull scratch then
        JsonSerializer.Serialize {| error = "bench's designTime mode needs a scratch directory" |}
    else
        JsonSerializer.Serialize(
            bench (root.GetProperty("project").GetString()) globals mode (root.GetProperty("reps").GetInt32()) scratch
        )

/// Register the MSBuild the oracle runs. With no arguments, the SDK `dotnet`
/// resolves from the working directory (`RegisterDefaults`). With
/// `--msbuild-sdk <dir>`, the SDK installed at `<dir>` (`<root>/sdk/<version>`),
/// spelt exactly as given: MSBuild records paths into its own directory in what
/// it computes (the runtime identifier graph's path lands in the restore spec),
/// so the caller chooses the spelling the build it stands in for would see.
/// The environment is what `MSBuildLocator.RegisterInstance` sets for a .NET
/// SDK instance; the process fails if `<dir>` holds no MSBuild, since a census
/// of one SDK that quietly ran another would be a census of the wrong thing.
let private registerMSBuild (argv: string[]) =
    match argv with
    | [||] -> MSBuildLocator.RegisterDefaults() |> ignore
    | [| "--msbuild-sdk"; dir |] ->
        let dir = Path.TrimEndingDirectorySeparator(Path.GetFullPath dir)
        let msbuild = Path.Combine(dir, "MSBuild.dll")

        if not (File.Exists msbuild) then
            failwith $"no MSBuild at %s{msbuild}"

        Environment.SetEnvironmentVariable("MSBUILD_EXE_PATH", msbuild)
        Environment.SetEnvironmentVariable("MSBuildExtensionsPath", dir)
        Environment.SetEnvironmentVariable("MSBuildSDKsPath", Path.Combine(dir, "Sdks"))
        MSBuildLocator.RegisterMSBuildPath dir
    | _ -> failwith $"usage: msbuild-condition-oracle [--msbuild-sdk <dir>] [--sdks-path <dir>]; got %A{argv}"

/// Split off a trailing `--sdks-path <dir>`: the directory MSBuild's default SDK
/// resolver looks in for a `<Project Sdk="Name">` (`<dir>/Name/Sdk`), set as
/// `MSBuildSDKsPath` *after* registration, since registering an MSBuild sets that
/// variable to the registered SDK's own `Sdks` directory. The resolver reads the
/// variable at each resolution. This is how a differential that lays out a
/// synthetic SDK gets MSBuild to import it through the `Sdk` attribute, exactly as
/// a real project imports its SDK, rather than through a hand-written `<Import>`.
let private splitSdksPath (argv: string[]) : string[] * string option =
    let n = argv.Length

    if n >= 2 && argv[n - 2] = "--sdks-path" then
        argv[.. n - 3], Some argv[n - 1]
    else
        argv, None

[<EntryPoint>]
let main argv =
    // Redirect the assembly loader to the installed SDK's MSBuild before any
    // Microsoft.Build type is touched at runtime. The evaluation logic lives
    // behind `evalCondition`, which is not JIT-compiled until first called
    // (well after this line), so the pinned reference assemblies never load.
    let argv, sdksPath = splitSdksPath argv
    registerMSBuild argv

    sdksPath
    |> Option.iter (fun dir -> Environment.SetEnvironmentVariable("MSBuildSDKsPath", Path.GetFullPath dir))

    AppDomain.CurrentDomain.add_AssemblyLoad(AssemblyLoadEventHandler(fun _ args -> recordLoad args))

    let mutable line = Console.In.ReadLine()

    while not (isNull line) do
        if line.Trim() <> "" then
            let response =
                try
                    use doc = JsonDocument.Parse line
                    let root = doc.RootElement

                    match root.GetProperty("op").GetString() with
                    | "eval" -> respondEval root
                    | "expand" -> respondExpand root
                    | "project" -> respondProject root
                    | "items" -> respondItems root
                    | "itemsMeta" -> respondItemsMeta root
                    | "elementContents" -> respondElementContents root
                    | "restoreCone" -> respondRestoreCone root
                    | "evaluated" -> respondEvaluated root
                    | "targetItems" -> respondTargetItems root
                    | "runTargets" -> respondRunTargets root
                    | "rejectionCode" -> respondRejectionCode root
                    | "globalName" -> respondGlobalName root
                    | "reservedNames" -> respondReservedNames ()
                    | "bench" -> respondBench root
                    | "idle" -> respondIdle root
                    | other -> JsonSerializer.Serialize {| error = $"unknown op: %s{other}" |}
                with ex ->
                    JsonSerializer.Serialize {| error = ex.Message |}

            Console.Out.WriteLine response
            Console.Out.Flush()

        line <- Console.In.ReadLine()

    0
