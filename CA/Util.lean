import Lean

open Lean

namespace CA.Util

/-- Collect the distinct named constants (`.const name _`) appearing in
    an expression, added to `acc`.

    Implemented with `Expr.foldConsts`, which visits each *shared*
    subterm once (pointer-cached), so the cost is the size of the DAG.
    The previous plain structural recursion re-walked every shared
    subterm and was exponential on the DAG-shaped proof terms `omega`,
    `decide` and `simp` produce — a single such term in `Init` or
    `Mathlib` could take minutes, which is what stalled a whole-Mathlib
    id computation before the first component was even hashed
    (2026-08-18). Same result set as before; only the walk changed. -/
def collectConstants (expr : Expr) (acc : Lean.NameSet := {}) : Lean.NameSet :=
  expr.foldConsts acc fun name (a : Lean.NameSet) => a.insert name

/-- Classify a `ConstantInfo` into its kind string. -/
def constantKind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo  _ => "axiom"
  | .defnInfo   _ => "definition"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "constructor"
  | .recInfo    _ => "recursor"

end CA.Util
