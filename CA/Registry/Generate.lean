import CA.Registry.Basic
import CA.Canonical
import CA.ExprHash
import CA.Util

/-!
# Registry Generation Command

Provides `#ca_registry "output_dir/"` — a command that generates
`declarations.json` and `meta.json` from `@[publish]` and `@[open_point]`
annotated declarations in the current environment.

Intended to be placed at the end of a project's registry file so that
`lake build` automatically produces the registry as a side-effect.
-/

open Lean Elab Command
open CA.Registry CA.ExprHash CA.Canonical CA.Util

namespace CA.Registry

/-- Pure-Lean hash of a ByteArray. Returns a 32-hex-char content identifier.
    Used because FFI-based SHA256 is not available during `#eval!` elaboration. -/
private def pureHash (data : ByteArray) : String :=
  let h1 := data.data.foldl (fun acc b =>
    acc * 6364136223846793005 + b.toUInt64 + 1) 14695981039346656037
  let h2 := data.data.foldl (fun acc b =>
    acc * 1099511628211 + b.toUInt64) 2166136261
  let hexDigit (n : UInt64) (i : Nat) : Char :=
    let nibble := ((n >>> (i * 4).toUInt64) &&& 0xF).toNat
    if nibble < 10 then Char.ofNat (48 + nibble) else Char.ofNat (87 + nibble)
  let s1 := (List.range 16).foldl (fun s i => s.push (hexDigit h1 (15 - i))) ""
  let s2 := (List.range 16).foldl (fun s i => s.push (hexDigit h2 (15 - i))) ""
  s1 ++ s2

/-- Classify a declaration as proved, open, or conditional. -/
private def classifyStatus (env : Environment) (name : Name)
    (openNames : NameSet) (isOpen : Bool) : String :=
  if isOpen then "open"
  else match env.find? name with
    | none => "unknown"
    | some ci =>
      if (collectConstants ci.type).any openNames.contains then "conditional"
      else "proved"

/-- Build a JSON entry for one declaration. -/
private def mkEntry (env : Environment) (name : Name) (status : String) :
    Lean.Json :=
  match env.find? name with
  | none => .null
  | some ci =>
    let ty := ci.type
    let hashTarget := match ci with
      | .defnInfo d => if ty == .sort .zero then d.value else ty
      | _ => ty
    let canonExpr := canonicalizeL0 hashTarget
    let serialized := serializeExpr canonExpr
    let typeHash := pureHash serialized
    let kind := match ci with
      | .thmInfo    _ => "theorem"
      | .defnInfo   _ => "definition"
      | .axiomInfo  _ => "axiom"
      | _ => "other"
    let moduleName := getModuleName env name
    let typeDeps := (collectConstants ty).toArray.map (·.toString)
    .mkObj [
      ("name", .str name.toString),
      ("module", .str moduleName.toString),
      ("kind", .str kind),
      ("status", .str status),
      ("type_hash", .str typeHash),
      ("pp_type", .str (toString ty)),
      ("type_deps", .arr (typeDeps.map .str))
    ]

/-- Generate registry files from the current environment.
    Writes `declarations.json` and `meta.json` to the given output directory. -/
def generateRegistryFiles (outputDir : String) : CommandElabM Unit := do
  let env ← getEnv

  let openPoints := getOpenPoints env
  let published := getPublished env
  logInfo m!"CA registry: {openPoints.length} open points, {published.length} published"

  let openNameSet := openPoints.foldl (fun acc (n, _) => acc.insert n) ({} : NameSet)

  let mut entries : Array Lean.Json := #[]

  for (name, _) in openPoints do
    let entry := mkEntry env name "open"
    entries := entries.push entry

  let mut condCount := 0
  for (name, _) in published do
    let status := classifyStatus env name openNameSet false
    if status == "conditional" then condCount := condCount + 1
    let entry := mkEntry env name status
    entries := entries.push entry

  IO.FS.createDirAll outputDir

  let declsPath := s!"{outputDir}/declarations.json"
  IO.FS.writeFile declsPath (Lean.Json.arr entries).pretty
  logInfo m!"Wrote {declsPath} ({entries.size} entries)"

  let openCount := openPoints.length
  let pubCount := published.length
  let metaJson := Lean.Json.mkObj [
    ("project", .str "registry"),
    ("ca_hash_level", .str "L0"),
    ("ca_hash_mode", .str "name-based"),
    ("open_points", .num ⟨openCount, 0⟩),
    ("published", .num ⟨pubCount, 0⟩),
    ("conditional", .num ⟨condCount, 0⟩),
    ("proved", .num ⟨pubCount - condCount, 0⟩)
  ]
  let metaPath := s!"{outputDir}/meta.json"
  IO.FS.writeFile metaPath metaJson.pretty
  logInfo m!"Wrote {metaPath}: {openCount} open, {pubCount - condCount} proved, {condCount} conditional"

/-- `#ca_registry "output_dir/"` — generates `declarations.json` and `meta.json`
    from `@[publish]` and `@[open_point]` annotations in the current environment.
    Place at the end of your registry file so `lake build` produces the registry. -/
elab "#ca_registry " dir:str : command => do
  generateRegistryFiles dir.getString

end CA.Registry
