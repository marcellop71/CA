import CA.Registry.Basic
import CA.Canonical
import CA.SHA256
import CA.ExprHash
import CA.Util

/-!
# Registry Generation Command

Provides `#ca_registry "output_dir/"` — a command that generates
`declarations.json` and `meta.json` from `@[publish]` and `@[open_point]`
annotated declarations in the current environment.

Intended to be placed at the end of a project's registry file so that
`lake build` automatically produces the registry as a side-effect.

The heavy lifting lives in `generateRegistryCore`, which is plain `IO`
over an `Environment` so that the `ca registry` CLI subcommand
(`Main.lean`) can reuse it — both paths must produce byte-identical
registries, or "addresses are computed, not assigned" would be false.
Hashing uses `sha256Pure` (`CA.SHA256`): the FFI SHA-256 is unavailable
to interpreted code (the `#ca_registry` command runs during
elaboration), and the pure implementation produces the same digests.
-/

open Lean Elab Command
open CA.Registry CA.ExprHash CA.Canonical CA.SHA256 CA.Util

namespace CA.Registry

/-- Classify a declaration as proved, open, or conditional. -/
def classifyStatus (env : Environment) (name : Name)
    (openNames : NameSet) (isOpen : Bool) : String :=
  if isOpen then "open"
  else match env.find? name with
    | none => "unknown"
    | some ci =>
      if (collectConstants ci.type).any openNames.contains then "conditional"
      else "proved"

/-- The expression a registry entry is addressed by: for an `@[open_point]`
    (a `def _ : Prop`), the *statement* is the definition's value; for
    everything else it is the type. -/
private def hashTarget (ci : ConstantInfo) : Expr :=
  match ci with
  | .defnInfo d => if ci.type == .sort .zero then d.value else ci.type
  | _ => ci.type

/-- Build a JSON entry for one declaration. -/
private def mkEntry (env : Environment) (name : Name) (status : String)
    (description : String := "") : IO Lean.Json := do
  match env.find? name with
  | none => return .null
  | some ci =>
    let target := hashTarget ci
    let canonExpr := canonicalizeL0 target
    let serialized := serializeExpr canonExpr
    let typeHash := toHex256 (sha256Pure serialized)
    let kind := match ci with
      | .thmInfo    _ => "theorem"
      | .defnInfo   _ => "definition"
      | .axiomInfo  _ => "axiom"
      | _ => "other"
    let moduleName := getModuleName env name
    let ppType ← runMetaM env do return (← Meta.ppExpr target).pretty
    let typeDeps := (collectConstants target).toArray.map (·.toString)
    let fields := [
      ("name", Lean.Json.str name.toString),
      ("module", .str moduleName.toString),
      ("kind", .str kind),
      ("status", .str status),
      ("type_hash", .str typeHash),
      ("pp_type", .str ppType),
      ("type_deps", .arr (typeDeps.map .str))
    ]
    let fields := if description.isEmpty then fields
      else fields ++ [("description", .str description)]
    return .mkObj fields

/-- Per-run summary of a registry generation. -/
structure RegistrySummary where
  openPoints  : Nat
  published   : Nat
  conditional : Nat
  entries     : Nat
  declsPath   : String
  metaPath    : String

/-- Generate `declarations.json` and `meta.json` from the `@[publish]` /
    `@[open_point]` annotations in `env`. Plain `IO`, shared by the
    `#ca_registry` command and the `ca registry` CLI subcommand.
    `toolchain` (when known) is recorded in `meta.json`. -/
def generateRegistryCore (env : Environment) (outputDir : String)
    (project : String := "registry") (toolchain : Option String := none)
    : IO RegistrySummary := do
  let openPoints := getOpenPoints env
  let published := getPublished env

  let openNameSet := openPoints.foldl (fun acc (n, _) => acc.insert n) ({} : NameSet)

  let mut entries : Array Lean.Json := #[]
  for (name, e) in openPoints do
    entries := entries.push (← mkEntry env name "open" e.description)
  let mut condCount : Nat := 0
  for (name, e) in published do
    let status := classifyStatus env name openNameSet false
    if status == "conditional" then condCount := condCount + 1
    entries := entries.push (← mkEntry env name status e.description)

  IO.FS.createDirAll outputDir

  let declsPath := s!"{outputDir}/declarations.json"
  IO.FS.writeFile declsPath (Lean.Json.arr entries).pretty

  let openCount := openPoints.length
  let pubCount := published.length
  let mut metaFields : List (String × Lean.Json) := [
    ("project", .str project),
    ("ca_hash_level", .str "L0"),
    ("ca_hash_mode", .str "name-based"),
    ("open_points", .num ⟨openCount, 0⟩),
    ("published", .num ⟨pubCount, 0⟩),
    ("conditional", .num ⟨condCount, 0⟩),
    ("proved", .num ⟨pubCount - condCount, 0⟩)
  ]
  if let some tc := toolchain then
    metaFields := metaFields ++ [("lean_toolchain", .str tc)]
  let metaPath := s!"{outputDir}/meta.json"
  IO.FS.writeFile metaPath (Lean.Json.mkObj metaFields).pretty

  return { openPoints := openCount, published := pubCount,
           conditional := condCount, entries := entries.size,
           declsPath, metaPath }

/-- Generate registry files from the current environment.
    Writes `declarations.json` and `meta.json` to the given output directory. -/
def generateRegistryFiles (outputDir : String) : CommandElabM Unit := do
  let env ← getEnv
  let toolchain ← try
      pure (some (← IO.FS.readFile "lean-toolchain").trimAscii.toString)
    catch _ => pure none
  let project := if env.mainModule == .anonymous then "registry"
    else env.mainModule.toString
  let s ← generateRegistryCore env outputDir (project := project) (toolchain := toolchain)
  logInfo m!"CA registry: {s.openPoints} open points, {s.published} published"
  logInfo m!"Wrote {s.declsPath} ({s.entries} entries)"
  logInfo m!"Wrote {s.metaPath}: {s.openPoints} open, {s.published - s.conditional} proved, {s.conditional} conditional"

/-- `#ca_registry "output_dir/"` — generates `declarations.json` and `meta.json`
    from `@[publish]` and `@[open_point]` annotations in the current environment.
    Place at the end of your registry file so `lake build` produces the registry. -/
elab "#ca_registry " dir:str : command => do
  generateRegistryFiles dir.getString

end CA.Registry
