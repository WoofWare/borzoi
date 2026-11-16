// Emit MemberRefAttr.dll: a type `Probe.Marked` whose custom attribute's
// constructor is a MemberRef whose parent is a *local* TypeDef
// (`Microsoft.FSharp.Core.AutoOpenAttribute`, declared in this assembly).
open System
open System.Reflection
open System.Reflection.Metadata
open System.Reflection.Metadata.Ecma335
open System.Reflection.PortableExecutable

let out = fsi.CommandLineArgs.[1]
let mb = MetadataBuilder()
let str (s: string) = mb.GetOrAddString s
mb.AddModule(0, str "MemberRefAttr.dll", mb.GetOrAddGuid(Guid("6f1c2e1a-0b5e-4c8e-9a51-2d7c1f0e4b33")), GuidHandle(), GuidHandle()) |> ignore
mb.AddAssembly(str "MemberRefAttr", Version(1, 0, 0, 0), StringHandle(), BlobHandle(), enum 0, AssemblyHashAlgorithm.Sha1) |> ignore
let corlib =
    mb.AddAssemblyReference(
        str "System.Runtime", Version(10, 0, 0, 0), StringHandle(),
        mb.GetOrAddBlob([| 0xb0uy; 0x3fuy; 0x5fuy; 0x7fuy; 0x11uy; 0xd5uy; 0x0auy; 0x3auy |]), enum 0, BlobHandle())
let objectRef = mb.AddTypeReference(corlib, str "System", str "Object")
let attributeRef = mb.AddTypeReference(corlib, str "System", str "Attribute")

let ctorSig =
    let b = BlobBuilder()
    BlobEncoder(b).MethodSignature(isInstanceMethod = true).Parameters(0, (fun r -> r.Void()), (fun _ -> ())) |> ignore
    mb.GetOrAddBlob b

// <Module>
mb.AddTypeDefinition(enum 0, StringHandle(), str "<Module>", EntityHandle(), MetadataTokens.FieldDefinitionHandle 1, MetadataTokens.MethodDefinitionHandle 1) |> ignore
// The local attribute type, with an abstract-free bodiless ctor (RVA 0, runtime-implemented).
let attrDef =
    mb.AddTypeDefinition(
        TypeAttributes.Public ||| TypeAttributes.Class, str "Microsoft.FSharp.Core", str "AutoOpenAttribute",
        attributeRef, MetadataTokens.FieldDefinitionHandle 1, MetadataTokens.MethodDefinitionHandle 1)
mb.AddMethodDefinition(
    MethodAttributes.Public ||| MethodAttributes.SpecialName ||| MethodAttributes.RTSpecialName ||| MethodAttributes.HideBySig,
    MethodImplAttributes.Runtime ||| MethodImplAttributes.Managed, str ".ctor", ctorSig, -1, MetadataTokens.ParameterHandle 1) |> ignore
let marked =
    mb.AddTypeDefinition(
        TypeAttributes.Public ||| TypeAttributes.Class ||| TypeAttributes.Abstract ||| TypeAttributes.Sealed,
        str "Probe", str "Marked", objectRef, MetadataTokens.FieldDefinitionHandle 1, MetadataTokens.MethodDefinitionHandle 2)
// The constructor spelled as a MemberRef on the local TypeDef.
let ctorRef = mb.AddMemberReference(attrDef, str ".ctor", ctorSig)
let attrBlob = mb.GetOrAddBlob([| 0x01uy; 0x00uy; 0x00uy; 0x00uy |])
mb.AddCustomAttribute(marked, ctorRef, attrBlob) |> ignore

let pe = ManagedPEBuilder(PEHeaderBuilder(imageCharacteristics = Characteristics.Dll), MetadataRootBuilder(mb), BlobBuilder())
let blob = BlobBuilder()
pe.Serialize blob |> ignore
IO.File.WriteAllBytes(out, blob.ToArray())
printfn "wrote %s" out
