import Lean

open Lean Meta

namespace CA.Canonical

/-! ## Level 0 Canonicalization (Pure)

Level 0 ensures α-equivalence:
- Canonicalizes universe parameter names to positional indices (`u_0`, `u_1`, ...)
- Strips `.mdata` annotations (irrelevant to mathematical content)
- Binder names are NOT included in Lean 4's `Expr.hash`, so no need to strip them
  for hashing. We still provide a function for display/serialization purposes.
-/

/-- Collect all `Level.param` names from a `Level`, preserving first-occurrence order. -/
partial def collectLevelParams (l : Level)
    (seen : Std.HashSet Name) (order : Array Name) : Std.HashSet Name × Array Name :=
  match l with
  | .param name =>
    if seen.contains name then (seen, order)
    else (seen.insert name, order.push name)
  | .succ l => collectLevelParams l seen order
  | .max l1 l2 =>
    let (seen, order) := collectLevelParams l1 seen order
    collectLevelParams l2 seen order
  | .imax l1 l2 =>
    let (seen, order) := collectLevelParams l1 seen order
    collectLevelParams l2 seen order
  | .zero => (seen, order)
  | .mvar _ => (seen, order)

/-- Walk an `Expr` to collect all universe parameter names in
    first-occurrence order.

    Sharing-aware: a subterm that has already been visited (structurally
    equal, `ExprStructEq`) contributes nothing new, so it is skipped, and a subterm without
    level parameters (`Expr.hasLevelParam`) is not entered at all. The
    order of first occurrences is exactly the plain DFS order — the
    result is identical to a naive walk, but the cost is the size of the
    DAG rather than of the unfolded tree (the naive walk was exponential
    on `omega`/`decide` proof terms). -/
partial def collectExprUnivParams (e : Expr)
    (seen : Std.HashSet Name) (order : Array Name) : Std.HashSet Name × Array Name :=
  let (_, seen, order) := go e {} seen order
  (seen, order)
where
  go (e : Expr) (visited : Std.HashSet ExprStructEq) (seen : Std.HashSet Name) (order : Array Name)
      : Std.HashSet ExprStructEq × Std.HashSet Name × Array Name :=
    if !e.hasLevelParam then (visited, seen, order)
    else if visited.contains ⟨e⟩ then (visited, seen, order)
    else
      let visited := visited.insert ⟨e⟩
      match e with
      | .const _ levels =>
        let (seen, order) := levels.foldl (fun (seen, order) l => collectLevelParams l seen order) (seen, order)
        (visited, seen, order)
      | .sort level =>
        let (seen, order) := collectLevelParams level seen order
        (visited, seen, order)
      | .app f a =>
        let (visited, seen, order) := go f visited seen order
        go a visited seen order
      | .lam _ ty body _ =>
        let (visited, seen, order) := go ty visited seen order
        go body visited seen order
      | .forallE _ ty body _ =>
        let (visited, seen, order) := go ty visited seen order
        go body visited seen order
      | .letE _ ty value body _ =>
        let (visited, seen, order) := go ty visited seen order
        let (visited, seen, order) := go value visited seen order
        go body visited seen order
      | .mdata _ e => go e visited seen order
      | .proj _ _ e => go e visited seen order
      | _ => (visited, seen, order)

/-- Build canonical mapping: first occurrence → `u_0`, `u_1`, ... -/
def buildCanonicalUnivMapping (params : Array Name) : Std.HashMap Name Name := Id.run do
  let mut mapping : Std.HashMap Name Name := {}
  for i in [:params.size] do
    mapping := mapping.insert params[i]! (Name.mkSimple s!"u_{i}")
  return mapping

/-- Apply canonical mapping to a `Level`. -/
partial def canonicalizeLevel (l : Level) (mapping : Std.HashMap Name Name) : Level :=
  match l with
  | .param name => .param (mapping.getD name name)
  | .succ l => .succ (canonicalizeLevel l mapping)
  | .max l1 l2 => .max (canonicalizeLevel l1 mapping) (canonicalizeLevel l2 mapping)
  | .imax l1 l2 => .imax (canonicalizeLevel l1 mapping) (canonicalizeLevel l2 mapping)
  | l => l

/-- Apply canonical universe mapping throughout an `Expr`. Also strips
    `.mdata`. Implemented with `Expr.replace` (the runtime's cached,
    sharing-preserving traversal): unchanged subterms are the same
    objects as in the input, so a DAG-shaped proof term stays a DAG. -/
partial def canonicalizeExprUnivs (e : Expr) (mapping : Std.HashMap Name Name) : Expr :=
  e.replace fun s => match s with
    | .const name levels =>
      some (.const name (levels.map fun l => canonicalizeLevel l mapping))
    | .sort level => some (.sort (canonicalizeLevel level mapping))
    | .mdata _ inner => some (canonicalizeExprUnivs inner mapping)
    | _ => none

/-- Strip `.mdata` recursively without changing anything else
    (sharing-preserving, via `Expr.replace`). -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .mdata _ inner => some (stripMData inner)
    | _ => none

/-- Level 0 canonicalization (pure):
    1. Collect universe params in first-occurrence order
    2. Rename to positional names (u_0, u_1, ...)
    3. Strip `.mdata` annotations

    Every step preserves sharing (see the helpers above); the previous
    implementation rebuilt the whole unfolded tree, which for a
    DAG-shaped proof term of a few million shared nodes meant tens of
    gigabytes of fresh `Expr` nodes — the memory blow-up that killed the
    first schema-v3 store rebuild (2026-08-18). -/
def canonicalizeL0 (e : Expr) : Expr :=
  if !e.hasLevelParam then
    stripMData e
  else
    let (_, params) := collectExprUnivParams e {} #[]
    if params.isEmpty then
      stripMData e
    else
      let mapping := buildCanonicalUnivMapping params
      canonicalizeExprUnivs e mapping

/-! ## Level 1 Canonicalization (MetaM)

Level 1 extends Level 0 with reducible-transparency normalization via
`deepNormalize`, which recursively applies `whnf` at every subexpression
under `withTransparency .reducible`. Properly opens binders with
`withLocalDecl` to avoid loose-bvar panics. Handles δ/β/ι/ζ/projection
reduction.

**Caveat:** Native `whnf` causes SIGSEGV after ~15-25k declarations in a
single MetaM session due to state accumulation (see `docs/whnf-native-crash.md`).
Callers must use micro-batching (fresh `runMetaM` per batch of ≤10 declarations).
`ExprHash.computeNameBasedHashes` handles this automatically.
-/

/-- Maximum recursion depth for `deepNormalize`. -/
def maxNormDepth : Nat := 256

/-- Deep normalization: recursively apply native `whnf` at every subexpression
    under reducible transparency. Properly opens binders with `withLocalDecl`
    to avoid "loose bvar" panics. Requires micro-batching to avoid SIGSEGV
    from MetaM state accumulation (see `docs/whnf-native-crash.md`). -/
partial def deepNormalize (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  if depth ≥ maxNormDepth then return e
  withTransparency .reducible do
    let e ← whnf e
    match e with
    | .app f a =>
      return .app (← deepNormalize f (depth + 1)) (← deepNormalize a (depth + 1))
    | .lam n t b bi =>
      let t' ← deepNormalize t (depth + 1)
      withLocalDecl n bi t' fun x => do
        let b' ← deepNormalize (b.instantiate1 x) (depth + 1)
        mkLambdaFVars #[x] b'
    | .forallE n t b bi =>
      let t' ← deepNormalize t (depth + 1)
      withLocalDecl n bi t' fun x => do
        let b' ← deepNormalize (b.instantiate1 x) (depth + 1)
        mkForallFVars #[x] b'
    | .letE _ _ v b _ =>
      let v' ← deepNormalize v (depth + 1)
      deepNormalize (b.instantiate1 v') (depth + 1)
    | .mdata _ e => deepNormalize e depth
    | .proj t i e =>
      let e' ← deepNormalize e (depth + 1)
      whnf (.proj t i e')
    | e => return e

/-- Level 1 normalization: native whnf deep normalization + Level 0. -/
def canonicalizeL1 (e : Expr) : MetaM Expr := do
  let normalized ← deepNormalize e
  return canonicalizeL0 normalized

/-- Canonicalization level selector. -/
inductive CanonLevel where
  | l0  -- Pure: universe renaming + mdata stripping
  | l1  -- MetaM: reducible normalization + L0
  deriving Repr, BEq

/-- Run a MetaM computation in IO with a given environment. -/
def runMetaM (env : Environment) (action : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "", fileMap := .ofString "" }
  let st : Core.State := { env }
  let (result, _) ← (MetaM.run' action).toIO ctx st
  return result

end CA.Canonical
