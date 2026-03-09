import Lean
import CA.Canonical
import CA.SHA256
import CA.Util

open Lean Meta
open CA.Canonical
open CA.SHA256
open CA.Util

namespace CA.ExprHash

/-! ## ByteArray Serialization Helpers -/

private def pushTag (buf : ByteArray) (tag : UInt8) : ByteArray :=
  buf.push tag

private def pushUInt64 (buf : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut b := buf
  let mut v := n
  for _ in List.range 8 do
    b := b.push (v &&& 0xFF).toUInt8
    v := v >>> 8
  return b

private def pushNat (buf : ByteArray) (n : Nat) : ByteArray :=
  pushUInt64 buf n.toUInt64

private def pushString (buf : ByteArray) (s : String) : ByteArray :=
  let bytes := s.toUTF8
  let buf := pushNat buf bytes.size
  buf ++ bytes

private def pushName (buf : ByteArray) (n : Name) : ByteArray :=
  pushString buf n.toString

private def pushBinderInfo (buf : ByteArray) : BinderInfo → ByteArray
  | .default => buf.push 0
  | .implicit => buf.push 1
  | .strictImplicit => buf.push 2
  | .instImplicit => buf.push 3

private partial def pushLevel (buf : ByteArray) (l : Level) : ByteArray :=
  match l with
  | .zero => pushTag buf 0x10
  | .succ l => pushLevel (pushTag buf 0x11) l
  | .max l1 l2 => pushLevel (pushLevel (pushTag buf 0x12) l1) l2
  | .imax l1 l2 => pushLevel (pushLevel (pushTag buf 0x13) l1) l2
  | .param name => pushName (pushTag buf 0x14) name
  | .mvar id => pushName (pushTag buf 0x15) id.name

/-! ## Structural Serialization

Serialize an Expr into a ByteArray with tag bytes for each constructor.
Used for name-based hashing mode. -/

/-- Serialize an Expr into a ByteArray. Each constructor gets a unique tag byte
    followed by its serialized children. -/
partial def serializeExpr (e : Expr) (buf : ByteArray := .empty) : ByteArray :=
  match e with
  | .bvar n => pushNat (pushTag buf 0x01) n
  | .fvar id => pushName (pushTag buf 0x02) id.name
  | .mvar id => pushName (pushTag buf 0x03) id.name
  | .sort l => pushLevel (pushTag buf 0x04) l
  | .const name levels =>
    let buf := pushName (pushTag buf 0x05) name
    levels.foldl (fun b l => pushLevel b l) buf
  | .app f a =>
    let buf := serializeExpr f (pushTag buf 0x06)
    serializeExpr a buf
  | .lam _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x07) bi
    let buf := serializeExpr t buf
    serializeExpr b buf
  | .forallE _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x08) bi
    let buf := serializeExpr t buf
    serializeExpr b buf
  | .letE _ t v b _ =>
    let buf := serializeExpr t (pushTag buf 0x09)
    let buf := serializeExpr v buf
    serializeExpr b buf
  | .lit (.natVal n) => pushNat (pushTag buf 0x0A) n
  | .lit (.strVal s) => pushString (pushTag buf 0x0B) s
  | .mdata _ e => serializeExpr e buf
  | .proj t i e =>
    let buf := pushName (pushTag buf 0x0C) t
    let buf := pushNat buf i
    serializeExpr e buf

/-! ## Content-Based Serialization

Like serializeExpr but at `.const name`, emits the 32-byte hash from the
hash table instead of the name string. Falls back to name if not in table. -/

/-- Serialize an Expr for content-based hashing. At `.const name`, emits the
    32-byte content hash of the referenced declaration from the table. -/
partial def serializeExprContent (e : Expr) (hashTable : Std.HashMap Name ByteArray)
    (buf : ByteArray := .empty) : ByteArray :=
  match e with
  | .bvar n => pushNat (pushTag buf 0x01) n
  | .fvar id => pushName (pushTag buf 0x02) id.name
  | .mvar id => pushName (pushTag buf 0x03) id.name
  | .sort l => pushLevel (pushTag buf 0x04) l
  | .const name levels =>
    let buf := pushTag buf 0x05
    let buf := match hashTable.get? name with
      | some hashBytes => buf ++ hashBytes  -- embed 32-byte content hash
      | none => pushName buf name           -- fallback to name
    levels.foldl (fun b l => pushLevel b l) buf
  | .app f a =>
    let buf := serializeExprContent f hashTable (pushTag buf 0x06)
    serializeExprContent a hashTable buf
  | .lam _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x07) bi
    let buf := serializeExprContent t hashTable buf
    serializeExprContent b hashTable buf
  | .forallE _ t b bi =>
    let buf := pushBinderInfo (pushTag buf 0x08) bi
    let buf := serializeExprContent t hashTable buf
    serializeExprContent b hashTable buf
  | .letE _ t v b _ =>
    let buf := serializeExprContent t hashTable (pushTag buf 0x09)
    let buf := serializeExprContent v hashTable buf
    serializeExprContent b hashTable buf
  | .lit (.natVal n) => pushNat (pushTag buf 0x0A) n
  | .lit (.strVal s) => pushString (pushTag buf 0x0B) s
  | .mdata _ e => serializeExprContent e hashTable buf
  | .proj t i e =>
    let buf := pushName (pushTag buf 0x0C) t
    let buf := pushNat buf i
    serializeExprContent e hashTable buf

/-! ## Hex Formatting -/

/-- Format a ByteArray hash as a hex string. -/
def toHex := toHex256

/-! ## Declaration Hash Structure -/

/-- Sentinel value hash for theorems (proof irrelevance). -/
def proofIrrelevantHash : String := "PROOF_IRRELEVANT"

/-- Hash mode: name-based uses constant names, content-based uses Merkle DAG. -/
inductive HashMode where
  | nameBased
  | contentBased
  deriving Repr, BEq

/-- Content-addressed hash data for a single declaration. -/
structure DeclHash where
  name       : Name
  module     : Name            -- source module
  kind       : String
  typeHash   : String          -- hex hash of canonicalized type
  valueHash  : Option String   -- hex hash of canonicalized value, or sentinel
  ppType     : String          -- pretty-printed type
  typeBytes  : ByteArray       -- serialized canonical type Expr
  typeDeps   : Array Name      -- constants referenced in the type
  valueDeps  : Array Name      -- constants referenced in the value
  deriving Inhabited

/-- Resolve the module that owns a declaration, or `.anonymous` if not found. -/
def getModuleName (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx =>
    let mods := env.allImportedModuleNames
    if h : idx.toNat < mods.size then mods[idx.toNat] else .anonymous
  | none => .anonymous

/-! ## Topological Sort for Content-Based Hashing -/

/-- Topological sort: returns names in dependency order (foundations first).
    `depGraph[name]` = names that `name`'s type depends on. -/
private def topologicalSort (depGraph : Std.HashMap Name (Array Name))
    (allNames : Array Name) : Array Name := Id.run do
  let nameSet := allNames.foldl (fun acc n => acc.insert n) ({} : NameSet)

  -- Build reverse graph and in-degree counts
  let mut reverseGraph : Std.HashMap Name (Array Name) := {}
  let mut inDeg : Std.HashMap Name Nat := {}
  for name in allNames do
    inDeg := inDeg.insert name 0
    reverseGraph := reverseGraph.insert name #[]

  for name in allNames do
    let deps := depGraph.getD name #[]
    let mut count := 0
    for dep in deps do
      if nameSet.contains dep then
        count := count + 1
        let prev := reverseGraph.getD dep #[]
        reverseGraph := reverseGraph.insert dep (prev.push name)
    inDeg := inDeg.insert name count

  -- Kahn's algorithm: start with nodes that have no dependencies
  let mut queue : Array Name := #[]
  for name in allNames do
    if inDeg.getD name 0 == 0 then
      queue := queue.push name

  let mut result : Array Name := #[]
  let mut qi : Nat := 0
  while qi < queue.size do
    let name := queue[qi]!
    result := result.push name
    for dependent in (reverseGraph.getD name #[]) do
      let deg := inDeg.getD dependent 1
      inDeg := inDeg.insert dependent (deg - 1)
      if deg - 1 == 0 then
        queue := queue.push dependent
    qi := qi + 1

  -- Any remaining names not in result are in cycles — append them at the end
  if result.size < allNames.size then
    for name in allNames do
      unless result.contains name do
        result := result.push name

  return result

/-! ## Batch Hash Computation

For L1, types are normalized with native `whnf` via micro-batches (fresh MetaM
per batch of ≤10 declarations) to prevent state accumulation → SIGSEGV.
Values always use L0 (pure) canonicalization — whnf on definition values causes
cumulative process-level memory growth that crashes after ~30k declarations
regardless of batch size. L0 uses a single session.

See `docs/whnf-native-crash.md` for the full crash analysis. -/

/-- Default micro-batch size for L1 whnf processing. Each batch gets a fresh
    MetaM session to prevent native whnf state accumulation crashes.
    Empirically: batch 10 works, batch 20 crashes. -/
private def defaultL1BatchSize : Nat := 10

/-- Intermediate hash data before pretty-printing (avoids ppExpr in whnf batch). -/
private structure PreDeclHash where
  name       : Name
  module     : Name
  kind       : String
  typeHash   : String
  valueHash  : Option String
  canonType  : Expr           -- for ppExpr in a separate pass
  typeBytes  : ByteArray
  typeDeps   : Array Name
  valueDeps  : Array Name
  deriving Inhabited

/-- Build the canonicalization function for a given level. -/
private def mkCanonFn (level : CanonLevel) : Expr → MetaM Expr := fun e =>
  match level with
  | .l0 => pure (canonicalizeL0 e)
  | .l1 => canonicalizeL1 e

/-- Hash the value of a declaration using L0 canonicalization.
    Values always use L0 — whnf on definition values causes cumulative
    memory growth → SIGSEGV after ~30k declarations.
    `serialize` is the serialization strategy (name-based or content-based). -/
private def hashValue (ci : ConstantInfo)
    (serialize : Expr → ByteArray) : MetaM (Option String × Array Name) := do
  match ci with
  | .thmInfo ti =>
    let vdeps := (collectConstants ti.value).toList.toArray
    pure (some proofIrrelevantHash, vdeps)
  | .defnInfo di =>
    let canonVal := canonicalizeL0 di.value
    let vs := serialize canonVal
    let vhBytes ← sha256 vs
    let vh := toHex vhBytes
    let vdeps := (collectConstants di.value).toList.toArray
    pure (some vh, vdeps)
  | .opaqueInfo oi =>
    let canonVal := canonicalizeL0 oi.value
    let vs := serialize canonVal
    let vhBytes ← sha256 vs
    let vh := toHex vhBytes
    let vdeps := (collectConstants oi.value).toList.toArray
    pure (some vh, vdeps)
  | _ => pure (none, #[])

/-- Phase 1: Canonicalize + hash a batch in a single MetaM session (no ppExpr).
    Returns pre-hashes and the number of declarations that fell back to L0. -/
private def hashBatchPhase1 (env : Environment) (batch : Array (Name × ConstantInfo))
    (canonFn : Expr → MetaM Expr) : IO (Array PreDeclHash × Nat) := do
  runMetaM env do
    let mut results : Array PreDeclHash := #[]
    let mut fallbacks : Nat := 0
    for (name, ci) in batch do
      let canonType ← try
        canonFn ci.type
      catch e =>
        fallbacks := fallbacks + 1
        IO.eprintln s!"  Warning: L1 failed on {name}: {← e.toMessageData.toString}"
        pure (canonicalizeL0 ci.type)
      let serialized := serializeExpr canonType
      let hashBytes ← sha256 serialized
      let typeH := toHex hashBytes
      let typeDeps := (collectConstants ci.type).toList.toArray
      let mod := getModuleName env name

      let (valueH, valueDeps) ← hashValue ci serializeExpr

      results := results.push {
        name, module := mod, kind := constantKind ci, typeHash := typeH,
        valueHash := valueH, canonType, typeBytes := serialized,
        typeDeps, valueDeps
      }
    return (results, fallbacks)

/-- Phase 2: Pretty-print canonical types in a fresh MetaM session (no whnf pressure). -/
private def hashBatchPhase2 (env : Environment)
    (preHashes : Array PreDeclHash) : IO (Array DeclHash) := do
  runMetaM env do
    let mut results : Array DeclHash := #[]
    for ph in preHashes do
      let fmt ← ppExpr ph.canonType
      let ppT := fmt.pretty
      results := results.push {
        name := ph.name, module := ph.module, kind := ph.kind,
        typeHash := ph.typeHash, valueHash := ph.valueHash,
        ppType := ppT, typeBytes := ph.typeBytes,
        typeDeps := ph.typeDeps, valueDeps := ph.valueDeps
      }
    return results

/-- Number of declarations to accumulate before flushing PreDeclHash → DeclHash.
    Bounds the number of live canonical Expr objects in memory to prevent
    process-level memory growth that causes SIGSEGV in whnf. -/
private def flushInterval : Nat := 5000

/-- Compute name-based hashes for all declarations.
    For L0: single MetaM session (pure, no crash risk).
    For L1: micro-batches with fresh MetaM per batch (default 10).
    Every `flushInterval` declarations, ppExpr is run and Expr objects are
    released to prevent process memory growth.
    Pass `batchSize` to override (0 = use defaults). -/
def computeNameBasedHashes (env : Environment) (decls : Array (Name × ConstantInfo))
    (level : CanonLevel) (batchSize : Nat := 0) : IO (Array DeclHash) := do
  let canonFn := mkCanonFn level
  let bs := if batchSize > 0 then batchSize
            else if level == .l1 then defaultL1BatchSize else decls.size
  let mut allResults : Array DeclHash := #[]
  let mut pendingPre : Array PreDeclHash := #[]
  let mut totalFallbacks : Nat := 0
  let mut batchStart : Nat := 0
  while batchStart < decls.size do
    let batchEnd := min (batchStart + bs) decls.size
    if batchStart % 1000 == 0 then
      IO.eprintln s!"  Normalizing: {batchStart}/{decls.size}"
    let batch := decls[batchStart:batchEnd]
    let (batchResults, fallbacks) ← hashBatchPhase1 env batch canonFn
    pendingPre := pendingPre ++ batchResults
    totalFallbacks := totalFallbacks + fallbacks
    batchStart := batchEnd
    -- Flush: ppExpr pending PreDeclHashes and release canonical Expr objects
    if pendingPre.size ≥ flushInterval || batchStart ≥ decls.size then
      if level == .l1 then
        IO.eprintln s!"  Pretty-printing: {pendingPre.size} (total so far: {allResults.size + pendingPre.size})"
      let flushed ← hashBatchPhase2 env pendingPre
      allResults := allResults ++ flushed
      pendingPre := #[]
  if totalFallbacks > 0 then
    IO.eprintln s!"  Warning: {totalFallbacks} declarations fell back to L0 normalization"
  return allResults

/-- Compute content-based (Merkle DAG) hashes for all declarations.
    Processes declarations in topological order so each declaration's hash
    depends on the content hashes of its dependencies, not their names.
    For L1, uses micro-batches with fresh MetaM per batch.
    Pass `batchSize` to override (0 = use defaults). -/
def computeContentBasedHashes (env : Environment) (decls : Array (Name × ConstantInfo))
    (level : CanonLevel) (batchSize : Nat := 0) : IO (Array DeclHash) := do
  -- Build dependency graph and topological order (pure computation)
  let mut depGraph : Std.HashMap Name (Array Name) := {}
  let mut declMap : Std.HashMap Name ConstantInfo := {}
  let mut allNames : Array Name := #[]
  for (name, ci) in decls do
    let typeDeps := (collectConstants ci.type).toList.toArray
    depGraph := depGraph.insert name typeDeps
    declMap := declMap.insert name ci
    allNames := allNames.push name
  let sorted := topologicalSort depGraph allNames

  let canonFn := mkCanonFn level

  -- Content-based hashing is sequential (each hash depends on predecessors),
  -- but we batch MetaM sessions to prevent whnf state accumulation.
  let bs := if batchSize > 0 then batchSize
            else if level == .l1 then defaultL1BatchSize else sorted.size
  let mut hashTable : Std.HashMap Name ByteArray := {}
  let mut preResults : Std.HashMap Name (PreDeclHash × ByteArray) := {}
  let mut batchStart : Nat := 0

  -- Phase 1: canonicalize + hash (in batches, no ppExpr)
  while batchStart < sorted.size do
    let batchEnd := min (batchStart + bs) sorted.size
    if batchStart % 1000 == 0 then
      IO.eprintln s!"  Normalizing: {batchStart}/{sorted.size}"
    let batchNames := sorted[batchStart:batchEnd]
    let ht := hashTable
    let (batchResults, newHT) ← runMetaM env do
      let mut localResults : Array (Name × PreDeclHash × ByteArray) := #[]
      let mut localHT := ht
      for name in batchNames do
        let some ci := declMap.get? name | continue
        let canonType ← try canonFn ci.type catch _ => pure (canonicalizeL0 ci.type)
        let serialized := serializeExprContent canonType localHT
        let hashBytes ← sha256 serialized
        let typeHex := toHex hashBytes
        let typeDeps := (collectConstants ci.type).toList.toArray
        let mod := getModuleName env name
        localHT := localHT.insert name hashBytes

        let (valueH, valueDeps) ← hashValue ci (fun e => serializeExprContent e localHT)

        localResults := localResults.push (name, {
          name, module := mod, kind := constantKind ci, typeHash := typeHex,
          valueHash := valueH, canonType, typeBytes := serialized,
          typeDeps, valueDeps
        }, hashBytes)
      return (localResults, localHT)

    for (name, ph, hb) in batchResults do
      preResults := preResults.insert name (ph, hb)
    hashTable := newHT
    batchStart := batchEnd

  -- Phase 2: pretty-print canonical types (fresh MetaM, no whnf pressure)
  IO.eprintln s!"  Pretty-printing: {preResults.size} declarations..."
  let allPreHashes := sorted.filterMap fun name =>
    (preResults.get? name).map (·.1)
  let finalHashes ← hashBatchPhase2 env allPreHashes

  -- Restore original declaration order
  let finalMap := finalHashes.foldl (fun acc dh => acc.insert dh.name dh) ({} : Std.HashMap Name DeclHash)
  let mut ordered : Array DeclHash := #[]
  for (name, _) in decls do
    if let some dh := finalMap.get? name then
      ordered := ordered.push dh
  return ordered

end CA.ExprHash
