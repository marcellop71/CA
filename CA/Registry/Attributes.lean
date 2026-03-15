import CA.Registry.Basic
import CA.Util

open Lean
open CA.Util (constantKind)

namespace CA.Registry

private def isDefnInfo : ConstantInfo → Bool
  | .defnInfo _ => true
  | _ => false

/-- Parse optional string description from attribute syntax.
    Handles `@[attr]` and `@[attr "description"]`. -/
private def parseDescription (stx : Syntax) : AttrM String := do
  -- stx structure: `publish (str)?` — stx[0] is "publish", stx[1] is optional group
  if stx.getNumArgs <= 1 then return ""
  let optArg := stx[1]!
  -- optional syntax node: if present, the string literal is its first child
  if optArg.isNone then return ""
  let strNode := optArg[0]!
  match Syntax.isStrLit? strNode with
  | some s => return s
  | none => return ""

/-- Syntax for `@[open_point]` or `@[open_point "description"]`. -/
syntax (name := open_point) "open_point" (str)? : attr

/-- `@[open_point]` or `@[open_point "description"]` — marks a `def X : Prop`
    as an open problem in the formal registry. -/
initialize registerBuiltinAttribute {
  name := `open_point
  descr := "Marks a Prop definition as an open problem"
  applicationTime := .afterCompilation
  add := fun name stx _kind => do
    let env ← getEnv
    let some ci := env.find? name
      | throwError "@[open_point]: unknown declaration '{name}'"
    unless isDefnInfo ci do
      throwError "@[open_point]: '{name}' must be a definition, got {constantKind ci}"
    let ty := ci.type
    unless ty == .sort .zero do
      throwError "@[open_point]: '{name}' must have type Prop, got {ty}"
    let desc ← parseDescription stx
    openPointExt.add name { description := desc }
}

/-- Syntax for `@[publish]` or `@[publish "description"]`. -/
syntax (name := publish) "publish" (str)? : attr

/-- `@[publish]` or `@[publish "description"]` — marks a theorem or definition
    for publication to the formal registry. -/
initialize registerBuiltinAttribute {
  name := `publish
  descr := "Marks a declaration for publication to the formal registry"
  applicationTime := .afterCompilation
  add := fun name stx _kind => do
    let env ← getEnv
    let some _ := env.find? name
      | throwError "@[publish]: unknown declaration '{name}'"
    let desc ← parseDescription stx
    publishExt.add name { description := desc }
}

end CA.Registry
