import Lean.Meta

/-! Read the types of named declarations from the kernel-checked environment.
The output supports manuscript correspondence review; it does not assign
coverage or add mathematical assumptions.
-/

open Lean Elab Command

syntax (name := certificationTypes) "#certification_types" "[" ident,* "]" : command

@[command_elab certificationTypes]
def elaborateCertificationTypes : CommandElab := fun stx => do
  match stx with
  | `(#certification_types [$roots:ident,*]) =>
    let env ← getEnv
    for root in roots.getElems.map Syntax.getId do
      let some info := env.checked.get.find? root
        | throwError "Missing kernel declaration: {root}"
      if info.isUnsafe then
        throwError "Unsafe declaration cannot certify a manuscript claim: {root}"
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      let type ← liftTermElabM do
        withOptions (fun options => options.setBool `pp.fullNames true) do
          return (← Meta.ppExpr info.type).pretty
      let record := Json.mkObj [
        ("name",Json.str root.toString),
        ("kind",Json.str kind),
        ("type",Json.str type)]
      logInfo m!"CERTIFICATION_TYPE {record.compress}"
  | _ => throwUnsupportedSyntax
