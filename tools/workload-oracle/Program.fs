/// Differential-test oracle over the real MSBuild workload SDK resolver
/// (test-only; never shipped in the LSP). `crates/msbuild`'s
/// `sdk_resolver/workloads.rs` reimplements what this resolver answers for the
/// two workload locator SDKs, and `crates/msbuild/tests/workload_locator_diff.rs`
/// holds it to this tool.
///
/// Usage: `workload-oracle --sdk <sdk-dir>`, where `<sdk-dir>` is one .NET
/// SDK's directory (`<dotnet-root>/sdk/<version>/`).
///
/// Which resolver answers: the one in `<sdk-dir>`
/// (`Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver.dll` and the
/// `Microsoft.NET.Sdk.WorkloadManifestReader.dll` beside it), loaded from there
/// at runtime and reached through reflection, since neither is published as a
/// package. The `Resolving` handler serves every assembly the default context
/// cannot place from `<sdk-dir>`, and the `identity` op reports where each was
/// loaded from. An SDK's resolver targets that SDK's runtime, so the caller
/// runs this tool on it (an SDK 11 resolver needs runtime 11: roll forward).
///
/// Protocol: JSONL request/response over stdin/stdout, one response line per
/// request line, in order. Ops:
///
///   {"op":"identity"}
///     -> {"manifestReader":path,"resolver":path,"runtime":version,
///         "processArchitecture":RuntimeInformation.ProcessArchitecture}
///   {"op":"band","version":s}   (new SdkFeatureBand(s))
///     -> {"ok":true,"band":ToString(),"withoutPrerelease":..,"isPrerelease":..}
///      | {"ok":false,"thrown":..}
///   {"op":"compareBands","a":s,"b":s}   (SdkFeatureBand(a).CompareTo(SdkFeatureBand(b)))
///     -> {"ok":true,"cmp":-1|0|1} | {"ok":false,"thrown":..}
///   {"op":"resolve","sdk":name,"dotnetRoot":p,"sdkVersion":v,"userProfileDir":p|null,
///    "globalJsonPath":p|null}
///     (a fresh CachingWorkloadResolver's Resolve, the call MSBuild's workload
///      SDK resolver makes, handed the global.json MSBuild found, if any;
///      the install state is read under the process's own architecture)
///     -> {"ok":true,"kind":"multiple","paths":[..]}
///      | {"ok":true,"kind":"single","path":p}
///      | {"ok":true,"kind":"empty","properties":{name:value},
///         "items":[{"type":t,"spec":s,"metadata":{name:value}}]}
///      | {"ok":true,"kind":"null"}
///      | {"ok":false,"thrown":..}
///     (a name that is no locator asks `TryGetPackInfo`: an installed pack is
///      `single`, one that is not is `empty` with a `MissingWorkloadPack`
///      item, and no pack of the name is `null`)
///
/// A response `{"error":..}` means the request or the tool is broken, never a
/// resolver verdict.
module WorkloadOracle.Program

open System
open System.IO
open System.Reflection
open System.Runtime.CompilerServices
open System.Runtime.Loader
open System.Text.Json

let private manifestReaderName = "Microsoft.NET.Sdk.WorkloadManifestReader"
let private resolverName = "Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver"

/// The exception a reflective call threw, unwrapped, as `Type: message`.
let rec private describe (ex: exn) : string =
    match ex with
    | :? TargetInvocationException as tie when not (isNull tie.InnerException) -> describe tie.InnerException
    | _ -> $"%s{ex.GetType().FullName}: %s{ex.Message}"

let private featureBandType () =
    Assembly
        .Load(manifestReaderName)
        .GetType("Microsoft.NET.Sdk.WorkloadManifestReader.SdkFeatureBand", true)

let private featureBand (version: string) : obj =
    Activator.CreateInstance(featureBandType (), [| box version |])

let private call (target: obj) (name: string) (args: obj array) : obj =
    let types = args |> Array.map (fun a -> a.GetType())
    target.GetType().GetMethod(name, types).Invoke(target, args)

let private respondBand (root: JsonElement) : string =
    let version = root.GetProperty("version").GetString()

    try
        let band = featureBand version

        JsonSerializer.Serialize
            {| ok = true
               band = string (call band "ToString" [||])
               withoutPrerelease = string (call band "ToStringWithoutPrerelease" [||])
               isPrerelease = band.GetType().GetProperty("IsPrerelease").GetValue(band) :?> bool |}
    with ex ->
        JsonSerializer.Serialize {| ok = false; thrown = describe ex |}

let private respondCompareBands (root: JsonElement) : string =
    try
        let a = featureBand (root.GetProperty("a").GetString())
        let b = featureBand (root.GetProperty("b").GetString())
        let cmp = call a "CompareTo" [| b |] :?> int
        JsonSerializer.Serialize {| ok = true; cmp = sign cmp |}
    with ex ->
        JsonSerializer.Serialize {| ok = false; thrown = describe ex |}

let private optionalString (root: JsonElement) (name: string) : string =
    match root.TryGetProperty name with
    | true, value when value.ValueKind = JsonValueKind.String -> value.GetString()
    | _ -> null

let private respondResolve (root: JsonElement) : string =
    let resolverType =
        Assembly
            .Load(resolverName)
            .GetType("Microsoft.NET.Sdk.WorkloadMSBuildSdkResolver.CachingWorkloadResolver", true)

    try
        let resolver = Activator.CreateInstance resolverType

        let resolve =
            resolverType.GetMethod(
                "Resolve",
                [| typeof<string>; typeof<string>; typeof<string>; typeof<string>; typeof<string> |]
            )

        let result =
            resolve.Invoke(
                resolver,
                [| box (root.GetProperty("sdk").GetString())
                   box (root.GetProperty("dotnetRoot").GetString())
                   box (root.GetProperty("sdkVersion").GetString())
                   box (optionalString root "userProfileDir")
                   box (optionalString root "globalJsonPath") |]
            )

        match result.GetType().Name with
        | "MultiplePathResolutionResult" ->
            let paths =
                result.GetType().GetProperty("Paths").GetValue(result) :?> Collections.Generic.IEnumerable<string>

            JsonSerializer.Serialize
                {| ok = true
                   kind = "multiple"
                   paths = Seq.toArray paths |}
        | "SinglePathResolutionResult" ->
            JsonSerializer.Serialize
                {| ok = true
                   kind = "single"
                   path = result.GetType().GetProperty("Path").GetValue(result) :?> string |}
        | "EmptyResolutionResult" ->
            let property (target: obj) (name: string) =
                target.GetType().GetProperty(name).GetValue(target)

            let properties =
                property result "propertiesToAdd" :?> Collections.Generic.IDictionary<string, string>

            // `IDictionary<string, SdkResultItem>`, whose value type lives in
            // `Microsoft.Build.Framework`, which this tool does not reference.
            let items =
                [| for entry in property result "itemsToAdd" :?> Collections.IEnumerable do
                       let item = property entry "Value"

                       let metadata =
                           match property item "Metadata" with
                           | null -> dict []
                           | m -> m :?> Collections.Generic.IDictionary<string, string>

                       {| ``type`` = property entry "Key" :?> string
                          spec = property item "ItemSpec" :?> string
                          metadata = metadata |} |]

            JsonSerializer.Serialize
                {| ok = true
                   kind = "empty"
                   properties = properties
                   items = items |}
        | "NullResolutionResult" -> JsonSerializer.Serialize {| ok = true; kind = "null" |}
        | other -> JsonSerializer.Serialize {| error = $"unknown resolution result %s{other}" |}
    with ex ->
        JsonSerializer.Serialize {| ok = false; thrown = describe ex |}

let private respondIdentity () : string =
    let location name = Assembly.Load(name: string).Location

    JsonSerializer.Serialize
        {| manifestReader = location manifestReaderName
           resolver = location resolverName
           runtime = Environment.Version.ToString()
           processArchitecture = string Runtime.InteropServices.RuntimeInformation.ProcessArchitecture |}

/// `None` when both resolver assemblies and the feature-band type load, or why
/// not.
[<MethodImpl(MethodImplOptions.NoInlining)>]
let private probeLoad () : string option =
    try
        featureBandType () |> ignore
        Assembly.Load(resolverName).GetTypes() |> ignore
        None
    with ex ->
        Some(describe ex)

/// The request loop. Kept out of `main` so that compiling `main` never needs a
/// resolver type, which would load one before the `Resolving` handler exists.
[<MethodImpl(MethodImplOptions.NoInlining)>]
let private serve () =
    let mutable line = Console.In.ReadLine()

    while not (isNull line) do
        if line.Trim() <> "" then
            let response =
                try
                    use doc = JsonDocument.Parse line
                    let root = doc.RootElement

                    match root.GetProperty("op").GetString() with
                    | "identity" -> respondIdentity ()
                    | "band" -> respondBand root
                    | "compareBands" -> respondCompareBands root
                    | "resolve" -> respondResolve root
                    | other -> JsonSerializer.Serialize {| error = $"unknown op: %s{other}" |}
                with ex ->
                    JsonSerializer.Serialize {| error = describe ex |}

            Console.Out.WriteLine response
            Console.Out.Flush()

        line <- Console.In.ReadLine()

[<EntryPoint>]
let main argv =
    match List.ofArray argv with
    | [ "--sdk"; dir ] ->
        let sdkDir = Path.TrimEndingDirectorySeparator(Path.GetFullPath dir)

        if not (File.Exists(Path.Combine(sdkDir, resolverName + ".dll"))) then
            eprintfn "workload-oracle: %s has no %s.dll; expected an SDK directory" sdkDir resolverName
            2
        else
            AssemblyLoadContext.Default.add_Resolving (
                Func<AssemblyLoadContext, AssemblyName, Assembly>(fun context name ->
                    let candidate = Path.Combine(sdkDir, name.Name + ".dll")

                    if File.Exists candidate then
                        context.LoadFromAssemblyPath candidate
                    else
                        null)
            )

            // Load both assemblies now, so that a runtime too old for this
            // SDK's resolver fails the start rather than answering every
            // request with a load failure dressed as a resolver verdict.
            match probeLoad () with
            | Some failure ->
                eprintfn "workload-oracle: cannot load the resolver from %s: %s" sdkDir failure
                3
            | None ->
                serve ()
                0
    | _ ->
        eprintfn "usage: workload-oracle --sdk <sdk-dir>"
        2
