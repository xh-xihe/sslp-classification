import Lean
import Lean.Util.CollectAxioms

/-! # Shared-state audit of kernel declaration dependencies

This diagnostic command checks every named root exists, traverses their union
once, and permits exactly the three standard logical axioms. It creates no
mathematical declarations or proof assumptions for any audited theorem.
-/

open Lean Elab Command

syntax (name := certificationAxioms) "#certification_axioms" "[" ident,* "]" : command

@[command_elab certificationAxioms]
def elaborateCertificationAxioms : CommandElab := fun stx => do
  match stx with
  | `(#certification_axioms [$roots:ident,*]) =>
    let names := roots.getElems.map Syntax.getId
    let env ← getEnv
    for root in names do
      if (env.checked.get.find? root).isNone then
        throwError "Missing kernel declaration: {root}"
    let action : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect
    let (_, state) := (action.run env).run {}
    let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
    for axiomName in state.axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected transitive axiom: {axiomName}"
    logInfo m!"CERTIFICATION_AXIOMS_OK roots={names.size} axioms={state.axioms}"
  | _ => throwUnsupportedSyntax
