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
///   {"op":"itemsMeta","xml":s,"path":s,"itemType":s,"metadata":[name, ..]}
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
///   {"op":"fscArgs","path":s,"xml":s?,"globals":{..}?}
///     -> {"ok":true,"args":[s, ..],"responseFile":s,"taskAssembly":s,
///         "compiler":{"ToolPath":s,"ToolExe":s,"DotnetFscCompilerPath":s}}
///      | {"ok":false,"errors":[s, ..]}          // no answer, and why
///     What the F# compiler is handed for the project at `path` (with `xml`
///     written there first, when given): it restores in-process as `-restore`
///     does, then runs a real `Build`'s targets through `Compile` with
///     `ProvideCommandLineArgs` and `SkipCompilerExecution` (fsc's arguments
///     are computed, fsc is not run). `args` is the real `Fsc` task's
///     `FscCommandLineArgs`, each as the task wrote it (the item's escaped
///     spelling: its unescaped one would decode a `%41` fsc was handed).
///     `responseFile` is the file the task hands fsc, read off the command
///     line it logs: those arguments one per line, with `--refout:` and
///     `--refonly` among them, and each `\` as written (the items turn it into
///     `/` off Windows). fsc reads that file a line at a time, so it, not
///     `args`, is what decides fsc's output. `taskAssembly` and `compiler` say
///     which `Fsc` ran and which program its arguments go to. `errors` leads
///     with "MSBuild rejects the project", "the restore failed" or "the build
///     failed" when MSBuild built nothing; any other decline means fsc may run
///     on arguments the op cannot report: a `Build` or `CoreBuild` target
///     other than the toolset's, a false `Build` condition, `Fsc` run other
///     than once, a build that fails after `Fsc` ran, a build that rewrites
///     its own target lists, a `ProjectReference` naming its own `Targets`
///     (which `BuildProjectReferences=false` does not build), a logged
///     command line that is not the reported arguments.
///     `fsc_args_oracle_calibration` holds the op to real compiling builds.
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
let private evalItemsMeta
    (path: string)
    (xml: string)
    (itemType: string)
    (metadata: string list)
    : (string * string * Map<string, string>) list option =
    use collection = new ProjectCollection()

    try
        writeProject path xml

        let instance =
            ProjectInstance(path, Collections.Generic.Dictionary<string, string>(), null, collection)

        instance.GetItems itemType
        |> Seq.map (fun item ->
            let values =
                metadata
                |> List.map (fun name -> (name, item.GetMetadataValue name))
                |> Map.ofList

            (item.EvaluatedInclude, (item :> Microsoft.Build.Framework.ITaskItem2).EvaluatedIncludeEscaped, values))
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

    match evalItemsMeta path xml itemType metadata with
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

/// The globals that make a build stop at computing fsc's command line.
/// `SkipCompilerExecution` makes the `Fsc` task bind its parameters and report
/// `FscCommandLineArgs` without compiling, so every argument is the task's own
/// doing, not this tool's. `BuildProjectReferences=false` resolves references
/// by asking for their target paths instead of building them: a referenced
/// project's build cannot change this one's arguments, and globals propagate
/// into it, where skipping the compiler would leave nothing to copy.
/// Deliberately *not* `DesignTimeBuild`: that is a switch build logic can read,
/// and every global that differs from a real build is a place the two could
/// disagree.
let private commandLineGlobals =
    [ "ProvideCommandLineArgs", "true"
      "SkipCompilerExecution", "true"
      "BuildProjectReferences", "false" ]

/// The targets a real `Build` runs up to and including `Compile`: the entries
/// of `$(BuildDependsOn)` before `CoreBuild`, then those of
/// `$(CoreBuildDependsOn)` through `Compile`. Read from the project itself, so
/// an extended or rewritten list is honoured, and every `BeforeTargets` /
/// `AfterTargets` hook on those targets runs as it would in a real build.
/// Nothing after `Compile` can change what fsc was passed. `None` when either
/// list lacks its anchor — a project whose build graph this tool does not
/// recognise.
let private buildTargetsThroughCompile (instance: ProjectInstance) : string list option =
    let split (name: string) =
        instance.GetPropertyValue(name).Split(';')
        |> Array.map (fun t -> t.Trim())
        |> Array.filter (fun t -> t <> "")
        |> List.ofArray

    let build = split "BuildDependsOn"
    let coreBuild = split "CoreBuildDependsOn"

    match List.tryFindIndex ((=) "CoreBuild") build, List.tryFindIndex ((=) "Compile") coreBuild with
    | Some beforeCore, Some compile -> Some(List.take beforeCore build @ List.take (compile + 1) coreBuild)
    | _ -> None

/// Why the targets of [`buildTargetsThroughCompile`] may not be what a real
/// `Build` runs, or `None` when they are: the `Build` and `CoreBuild` targets
/// must be the toolset's own (defined in a file under `MSBuildToolsPath`),
/// since a replaced one may run anything, and `Build`'s condition must hold,
/// since a false one skips its dependencies.
let private buildGraphDoubt (instance: ProjectInstance) : string option =
    let tools =
        Path.TrimEndingDirectorySeparator(instance.GetPropertyValue "MSBuildToolsPath")
        + string Path.DirectorySeparatorChar

    let own (name: string) =
        match instance.Targets.TryGetValue name with
        | true, target when target.FullPath.StartsWith(tools, StringComparison.Ordinal) -> Some target
        | _ -> None

    match own "Build", own "CoreBuild" with
    | None, _ -> Some "the Build target is not the toolset's own"
    | _, None -> Some "the CoreBuild target is not the toolset's own"
    | Some build, Some _ when not (instance.EvaluateCondition build.Condition) ->
        Some "the Build target's condition is false"
    | Some _, Some _ -> None

/// Whether a task MSBuild ran is the `Fsc` task: by name, bare or qualified
/// with its namespace, in any case, as MSBuild looks tasks up.
let private isFsc (name: string) =
    name.Equals("Fsc", StringComparison.OrdinalIgnoreCase)
    || name.EndsWith(".Fsc", StringComparison.OrdinalIgnoreCase)

/// The `Fsc` task's parameters that choose the program it runs, as the
/// `fscArgs` op reports them.
let private compilerParameters = [ "ToolPath"; "ToolExe"; "DotnetFscCompilerPath" ]

/// One `Fsc` invocation: the file of the task assembly that ran, the
/// parameters of [`compilerParameters`] as it was handed them, and the
/// messages it logged.
type private FscRun =
    { Assembly: string
      Inputs: Collections.Generic.Dictionary<string, string>
      Messages: ResizeArray<string> }

/// Records each `Fsc` invocation of a build, and every error. A task's
/// parameters are logged only when the build sets `LogTaskInputs`.
type private FscLogger() =
    let errors = ResizeArray<string>()
    let runs = Collections.Generic.Dictionary<struct (int * int * int * int), FscRun>()
    let order = ResizeArray<struct (int * int * int * int)>()

    let key (c: Microsoft.Build.Framework.BuildEventContext) =
        struct (c.NodeId, c.ProjectContextId, c.TargetId, c.TaskId)

    member _.Errors = List.ofSeq errors
    /// Each `Fsc` invocation, in the order they started.
    member _.Runs = order |> Seq.map (fun k -> runs[k]) |> List.ofSeq

    interface Microsoft.Build.Framework.ILogger with
        member val Verbosity = Microsoft.Build.Framework.LoggerVerbosity.Normal with get, set
        member val Parameters: string = null with get, set

        member _.Initialize(source: Microsoft.Build.Framework.IEventSource) =
            source.TaskStarted.Add(fun e ->
                if isFsc e.TaskName then
                    let k = key e.BuildEventContext

                    runs[k] <-
                        { Assembly = e.TaskAssemblyLocation
                          Inputs = Collections.Generic.Dictionary<string, string>()
                          Messages = ResizeArray<string>() }

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
                | Some run, e -> run.Messages.Add e.Message
                | None, _ -> ())

            source.ErrorRaised.Add(fun e -> errors.Add $"%s{e.File}(%d{e.LineNumber}): %s{e.Code} %s{e.Message}")

        member _.Shutdown() = ()

/// What the `fscArgs` op reports of one compile.
type private FscInvocation =
    { Args: string list
      ResponseFile: string
      TaskAssembly: string
      Compiler: Collections.Generic.IDictionary<string, string> }

/// The response file `run` handed fsc, read off the command line the task
/// logged before running it (`ToolTask` logs
/// `<tool path> <command-line commands> <response-file commands>`): the
/// tool path is `ToolPath` joined with `ToolExe`, and `Fsc`'s command-line
/// commands are its `DotnetFscCompilerPath`, verbatim. `Error` when no
/// message has that shape, or the file's lines are not the reported
/// arguments' (`args`, the items `Fsc` built from them, which turn each `\`
/// into `/` off Windows): those differ only by `--refout:` and `--refonly`,
/// which the task writes to the file but not to its reported arguments.
let private responseFileOf (run: FscRun) (args: string list) : Result<string, string> =
    let input name =
        match run.Inputs.TryGetValue name with
        | true, value -> value
        | _ -> ""

    let tool = Path.Combine(input "ToolPath", input "ToolExe")

    let prefix =
        match input "DotnetFscCompilerPath" with
        | "" -> tool + "  "
        | compiler -> tool + " " + compiler + " "

    match run.Messages |> Seq.filter (fun m -> m.StartsWith(prefix, StringComparison.Ordinal)) |> List.ofSeq with
    | [ message ] ->
        let file = message.Substring prefix.Length

        let lines (text: string) =
            text.Split('\n')
            |> Array.filter (fun line -> not (line.StartsWith "--refout:" || line = "--refonly"))
            |> List.ofArray

        let fixedFile =
            if Path.DirectorySeparatorChar = '\\' then
                file
            else
                file.Replace('\\', '/')

        if lines fixedFile = lines (String.Join("\n", args)) then
            Ok file
        else
            Error $"the logged command line is not the reported arguments: %s{message}"
    | [] -> Error $"Fsc logged no command line starting %s{prefix}"
    | many -> Error $"Fsc logged %d{many.Length} command lines"

/// The arguments the `Fsc` task passes fsc for the project at `path` (writing
/// `xml` there first, when given), in order, or the reasons none can be
/// reported. See the `fscArgs` op in the header.
let private evalFscArgs
    (path: string)
    (xml: string option)
    (globals: Collections.Generic.IDictionary<string, string>)
    : Result<FscInvocation, string list> =
    use collection = new ProjectCollection()

    try
        xml |> Option.iter (writeProject path)
        let globals = globalTable globals
        let logger = FscLogger()

        // Restore first, as a real build (`dotnet build`, `msbuild -restore`)
        // does: a package's `build/*.props` and `.targets` are imported only
        // through the restore outputs. Like `-restore`, it runs in its own
        // evaluation under a restore session id with package imports excluded,
        // and the build then re-evaluates from scratch so it sees what the
        // restore wrote.
        let restored =
            use restoreCollection = new ProjectCollection()
            let restoreGlobals = Collections.Generic.Dictionary<string, string>(globals)
            restoreGlobals["MSBuildRestoreSessionId"] <- Guid.NewGuid().ToString()
            restoreGlobals["ExcludeRestorePackageImports"] <- "true"

            ProjectInstance(path, restoreGlobals, null, restoreCollection)
                .Build([| "Restore" |], [ logger :> Microsoft.Build.Framework.ILogger ])

        let buildGlobals = Collections.Generic.Dictionary<string, string>(globals)

        for (name, value) in commandLineGlobals do
            buildGlobals[name] <- value

        let instance = ProjectInstance(path, buildGlobals, null, collection)
        // `CoreCompile` is incremental: over a project that was already built,
        // its outputs are up to date, the target is skipped, and `Fsc` never
        // reports its arguments. An input that does not exist makes it out of
        // date. Added to this project's instance only, so nothing propagates
        // into referenced projects the way a global would.
        instance.AddItem(
            "CustomAdditionalCompileInputs",
            Path.Combine(Path.GetTempPath(), "borzoi-fsc-args-" + Guid.NewGuid().ToString "N")
        )
        |> ignore

        if not restored then
            Error("the restore failed" :: logger.Errors)
        else
            match buildTargetsThroughCompile instance, buildGraphDoubt instance with
            | None, _ ->
                Error
                    [ "$(BuildDependsOn) has no CoreBuild or $(CoreBuildDependsOn) has no Compile: "
                      + "an unrecognised build graph" ]
            | _, Some doubt -> Error [ doubt ]
            // `BuildProjectReferences=false` resolves each reference by asking
            // for its target path, not by building the targets the item names,
            // whose outputs a real build would reference instead.
            | Some _, None when
                instance.GetItems "ProjectReference"
                |> Seq.exists (fun item -> item.GetMetadataValue "Targets" <> "")
                ->
                Error [ "a ProjectReference names its own Targets, which the op does not build" ]
            | Some targets, None ->
                let parameters =
                    BuildParameters(
                        collection,
                        Loggers = [ logger :> Microsoft.Build.Framework.ILogger ],
                        MaxNodeCount = 1,
                        EnableNodeReuse = false,
                        LogTaskInputs = true
                    )

                let request =
                    BuildRequestData(
                        instance,
                        Array.ofList targets,
                        null,
                        BuildRequestDataFlags.ProvideProjectStateAfterBuild
                    )

                let result = BuildManager.DefaultBuildManager.Build(parameters, request)
                let after = result.ProjectStateAfterBuild

                // A build that fails before `Fsc` runs compiles nothing; one
                // that fails after may fail only because the compiler was not
                // run (a hook reading its output), so says nothing either way.
                if result.OverallResult <> BuildResultCode.Success && List.isEmpty logger.Runs then
                    Error("the build failed" :: logger.Errors)
                elif result.OverallResult <> BuildResultCode.Success then
                    Error("the build failed after Fsc ran" :: logger.Errors)
                // A target that rewrites either list while the build runs
                // changes what a real `Build` executes after that point; the
                // list above was read before any target ran.
                elif buildTargetsThroughCompile after <> Some targets then
                    Error [ "the build rewrote $(BuildDependsOn) or $(CoreBuildDependsOn) while running" ]
                else
                    match logger.Runs with
                    | [ run ] ->
                        // Each argument as the task wrote it: `Fsc` reports
                        // them as items built from the raw text, which an
                        // item's unescaped spelling (`EvaluatedInclude`) would
                        // decode (`%41` reads back as `A`).
                        let args =
                            after.GetItems "FscCommandLineArgs"
                            |> Seq.map (fun item -> (item :> Microsoft.Build.Framework.ITaskItem2).EvaluatedIncludeEscaped)
                            |> List.ofSeq

                        if List.isEmpty args then
                            Error [ "Fsc ran outside this project, or reported no arguments" ]
                        else
                            match responseFileOf run args with
                            | Ok file ->
                                Ok
                                    { Args = args
                                      ResponseFile = file
                                      TaskAssembly = run.Assembly
                                      Compiler = run.Inputs }
                            | Error why -> Error [ why ]
                    | [] -> Error [ "Fsc never ran" ]
                    | many -> Error [ $"Fsc ran %d{many.Length} times" ]
    with :? InvalidProjectFileException as ex ->
        Error [ "MSBuild rejects the project"; ex.Message ]

let private respondFscArgs (root: JsonElement) : string =
    let path = root.GetProperty("path").GetString()

    let xml =
        match root.TryGetProperty "xml" with
        | true, x when x.ValueKind = JsonValueKind.String -> Some(x.GetString())
        | _ -> None

    match evalFscArgs path xml (readGlobals root) with
    | Ok invocation ->
        JsonSerializer.Serialize
            {| ok = true
               args = invocation.Args
               responseFile = invocation.ResponseFile
               taskAssembly = invocation.TaskAssembly
               compiler = invocation.Compiler |}
    | Error errors -> JsonSerializer.Serialize {| ok = false; errors = errors |}

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
                    | "restoreCone" -> respondRestoreCone root
                    | "evaluated" -> respondEvaluated root
                    | "targetItems" -> respondTargetItems root
                    | "runTargets" -> respondRunTargets root
                    | "fscArgs" -> respondFscArgs root
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
