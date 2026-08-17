import Lean
import Lean.Elab.Frontend
import CA.RefHash

/-!
Test executable for `CA.RefHash`. Elaborates a small source string against
`Init`, computes ids with the whole of `Init` as the base table, and
checks the semantic properties the scheme promises:

* names never enter an id (α-renamed declarations get equal ids);
* theorems: equal statements ⇒ equal `stmt`/`ref`, different proofs ⇒
  different `decl`;
* definitions: equal types but different values ⇒ equal `stmt`, different
  `decl`/`ref` — and a statement *about* them differs accordingly;
* mutual / inductive blocks: members share a block id, get distinct
  member indices, and the whole thing is deterministic across runs;
* with a complete base table nothing is unresolved.
-/

open Lean CA.RefHash

private def src : String := "
def A : Type := Nat
def B : Type := Bool
def f (n : Nat) : Nat := n + 1
def g (n : Nat) : Nat := n + 1
def h (n : Nat) : Nat := n + 2
theorem t1 : (1 : Nat) + 1 = 2 := rfl
theorem t2 : (1 : Nat) + 1 = 2 := by decide
theorem uses_f : f 0 = 1 := rfl
theorem uses_g : g 0 = 1 := rfl
theorem uses_h : h 0 = 2 := rfl
mutual
  def ev : Nat → Bool
    | 0 => true
    | n+1 => od n
  def od : Nat → Bool
    | 0 => false
    | n+1 => ev n
end
inductive T where
  | a | b
inductive T2 where
  | a | b
"

private unsafe def enableInitImpl : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitImpl] private opaque enableInit : IO Unit

private def elabSource (source : String) : IO Environment := do
  enableInit
  let some env ← Elab.runFrontend source {} "<refhash-test>" `RefHashTest
    | throw (IO.userError "elaboration failed")
  return env

private def b58 := CA.RefHash.toB58

def main : IO UInt32 := do
  IO.println "refhash-test: init search path"; (← IO.getStdout).flush
  initSearchPath (← findSysroot)
  IO.println "refhash-test: elaborating source"; (← IO.getStdout).flush
  let env ← elabSource src
  IO.println "refhash-test: elaborated"; (← IO.getStdout).flush

  -- Base table: every constant already in the environment before ours
  -- (i.e. Init), computed foundations-first. Also a rough perf probe.
  let mut baseDecls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    baseDecls := baseDecls.push (n, ci)
  IO.println s!"Base: {baseDecls.size} Init constants"
  let t0 ← IO.monoMsNow
  let (baseIds, base) ← computeIds baseDecls
  let t1 ← IO.monoMsNow
  let unresolvedBase := baseIds.foldl (fun n d => n + d.unresolved.size) 0
  IO.println s!"  ids computed in {t1 - t0} ms; unresolved refs (total): {unresolvedBase}"
  let mut shown := 0
  for d in baseIds do
    if !d.unresolved.isEmpty && shown < 8 then
      IO.println s!"    {d.name} → unresolved {d.unresolved.toList.take 4}"
      shown := shown + 1

  -- Our declarations.
  let oursRef ← IO.mkRef (#[] : Array (Name × ConstantInfo))
  env.constants.map₂.forM fun n ci => do
    oursRef.modify (·.push (n, ci))
  let ours ← oursRef.get
  let (ids, _) ← computeIds ours base
  let byName : Std.HashMap Name DeclIds := ids.foldl (fun m d => m.insert d.name d) {}
  let get (n : Name) : IO DeclIds := do
    match byName.get? n with
    | some d => pure d
    | none => throw (IO.userError s!"missing ids for {n}")

  let check (label : String) (ok : Bool) : IO Unit := do
    if ok then IO.println s!"  ✓ {label}"
    else IO.println s!"  ✗ {label}"
  let mut fails : Array String := #[]
  let assert (label : String) (ok : Bool) : IO (Array String) := do
    check label ok
    return if ok then #[] else #[label]

  IO.println "Properties:"
  let A ← get `A; let B ← get `B
  let f ← get `f; let g ← get `g; let h ← get `h
  let t1' ← get `t1; let t2' ← get `t2
  let uf ← get `uses_f; let ug ← get `uses_g; let uh ← get `uses_h
  let ev ← get `ev; let od ← get `od
  let T ← get `T; let Ta ← get `T.a; let Tb ← get `T.b; let Trec ← get `T.rec
  let T2 ← get `T2

  fails := fails ++ (← assert "no unresolved references with a complete base"
    (ids.all (·.unresolved.isEmpty)))
  fails := fails ++ (← assert "A, B : Type share a statement id" (A.stmt == B.stmt))
  fails := fails ++ (← assert "A, B : Type have different decl ids" (A.decl != B.decl))
  fails := fails ++ (← assert "f, g (α-renamed) have equal decl ids — names never enter"
    (f.decl == g.decl && f.ref == g.ref))
  fails := fails ++ (← assert "f, h: same type ⇒ same stmt" (f.stmt == h.stmt))
  fails := fails ++ (← assert "f, h: different value ⇒ different decl and ref"
    (f.decl != h.decl && f.ref != h.ref))
  fails := fails ++ (← assert "t1, t2: same statement ⇒ same stmt and ref (proof irrelevance)"
    (t1'.stmt == t2'.stmt && t1'.ref == t2'.ref))
  fails := fails ++ (← assert "t1, t2: different proofs ⇒ different decl" (t1'.decl != t2'.decl))
  fails := fails ++ (← assert "uses_f, uses_g: statements about equal content are equal"
    (uf.stmt == ug.stmt))
  fails := fails ++ (← assert "uses_f, uses_h: statements about different content differ"
    (uf.stmt != uh.stmt))
  fails := fails ++ (← assert "ev, od form one block with distinct indices"
    (match ev.block, od.block with
     | some (b1, i1), some (b2, i2) => b1 == b2 && i1 != i2
     | _, _ => false))
  fails := fails ++ (← assert "T, T.a, T.b form one block (the SCC); T.rec is a downstream node"
    (match T.block, Ta.block, Tb.block with
     | some (b, _), some (b1, _), some (b2, _) => b == b1 && b1 == b2 && Trec.block.isNone
     | _, _, _ => false))
  fails := fails ++ (← assert "T, T2 (α-renamed inductives) have equal decl ids" (T.decl == T2.decl))
  fails := fails ++ (← assert "T.a ≠ T.b" (Ta.decl != Tb.decl))

  -- Determinism: recompute and compare every id.
  let (ids2, _) ← computeIds ours base
  let same := ids.size == ids2.size &&
    (ids.zip ids2).all fun (a, b) => a.name == b.name && a.stmt == b.stmt && a.decl == b.decl && a.ref == b.ref
  fails := fails ++ (← assert "deterministic across runs" same)

  -- Order independence: reversed input yields the same ids.
  let (ids3, _) ← computeIds ours.reverse base
  let m3 : Std.HashMap Name DeclIds := ids3.foldl (fun m d => m.insert d.name d) {}
  let sameOrder := ids.all fun d => match m3.get? d.name with
    | some d3 => d3.stmt == d.stmt && d3.decl == d.decl
    | none => false
  fails := fails ++ (← assert "input order does not matter" sameOrder)

  IO.println ""
  IO.println s!"  f     stmt={b58 f.stmt}"
  IO.println s!"  f     decl={b58 f.decl}"
  IO.println s!"  t1    stmt={b58 t1'.stmt}  decl={b58 t1'.decl}"
  IO.println s!"  t2    stmt={b58 t2'.stmt}  decl={b58 t2'.decl}"
  IO.println s!"  ev    block={(ev.block.map fun (b, i) => s!"{b58 b}#{i}").getD "-"}"
  IO.println s!"  od    block={(od.block.map fun (b, i) => s!"{b58 b}#{i}").getD "-"}"

  let failures := fails.size
  if failures == 0 then
    IO.println "\nAll RefHash tests passed."
    return 0
  else
    IO.println s!"\n{failures} RefHash test(s) FAILED: {fails}"
    return 1
