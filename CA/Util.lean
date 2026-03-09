import Lean

open Lean

namespace CA.Util

/--
Collect distinct named constants (`.const name _`) appearing in an expression.
-/
partial def collectConstants (expr : Expr) (acc : Lean.NameSet := {}) : Lean.NameSet :=
  match expr with
  | .const name _ => acc.insert name
  | .app f a => collectConstants a (collectConstants f acc)
  | .lam _ ty body _ => collectConstants body (collectConstants ty acc)
  | .forallE _ ty body _ => collectConstants body (collectConstants ty acc)
  | .letE _ ty value body _ => collectConstants body (collectConstants value (collectConstants ty acc))
  | .mdata _ expr => collectConstants expr acc
  | .proj _ _ expr => collectConstants expr acc
  | _ => acc

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
