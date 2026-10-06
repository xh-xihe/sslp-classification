import SixQubit.Orbit36Code
import Lean.Util.CollectAxioms

set_option maxRecDepth 40000
namespace SSLPExplorerCase
open SixQubit.Orbit36Code
noncomputable section

def data0 (x : SS.BitString 6) : ZQ :=
  if num x = 0 then z8 0 0 2 0 0 0 0 0 else
  if num x = 23 then z8 0 0 2 0 0 0 0 0 else
  if num x = 27 then z8 0 0 2 0 0 0 0 0 else
  if num x = 29 then z8 0 0 2 0 0 0 0 0 else
  if num x = 30 then z8 0 0 2 0 0 0 0 0 else
  if num x = 35 then z8 0 2 0 0 0 0 0 0 else
  if num x = 37 then z8 0 (-1) 0 0 0 0 0 1 else
  if num x = 38 then z8 0 (-1) 0 0 0 0 0 (-1) else
  if num x = 41 then z8 0 (-1) 0 0 0 0 0 (-1) else
  if num x = 42 then z8 0 (-1) 0 0 0 0 0 1 else
  if num x = 44 then z8 0 2 0 0 0 0 0 0 else
  if num x = 48 then z8 0 0 2 0 0 0 0 0 else ZQ.zero
theorem data0_matches : ∀ x, data0 x = c0z x := by decide
def state0 : SS.State 6 ℂ := stC data0
theorem state0_matches : state0 = c36 := by
  funext x; simp only [state0, c36, stC, data0_matches]

def data1 (x : SS.BitString 6) : ZQ :=
  if num x = 15 then z8 0 0 2 0 0 0 0 0 else
  if num x = 19 then z8 0 (-2) 0 0 0 0 0 0 else
  if num x = 21 then z8 0 1 0 0 0 0 0 1 else
  if num x = 22 then z8 0 1 0 0 0 0 0 (-1) else
  if num x = 25 then z8 0 1 0 0 0 0 0 (-1) else
  if num x = 26 then z8 0 1 0 0 0 0 0 1 else
  if num x = 28 then z8 0 (-2) 0 0 0 0 0 0 else
  if num x = 33 then z8 0 0 (-2) 0 0 0 0 0 else
  if num x = 34 then z8 0 0 (-2) 0 0 0 0 0 else
  if num x = 36 then z8 0 0 (-2) 0 0 0 0 0 else
  if num x = 40 then z8 0 0 (-2) 0 0 0 0 0 else
  if num x = 63 then z8 0 0 2 0 0 0 0 0 else ZQ.zero
theorem data1_matches : ∀ x, data1 x = c1z x := by decide
def state1 : SS.State 6 ℂ := stC data1
theorem state1_matches : state1 = d36 := by
  funext x; simp only [state1, d36, stC, data1_matches]

def angles : Fin 6 → ZMod 5 := ![1, 1, 1, 1, 2, 3]
theorem fiber0 : ∀ x, data0 x ≠ ZQ.zero → SS.weight angles x = (0 : ZMod 5) := by decide
theorem support0 : SS.SSConditionState angles (0 : ZMod 5) state0 := by
  intro x hx
  apply fiber0 x
  intro hz
  apply hx
  simp [state0, stC, hz, toC_zero]
theorem logical0 (zeta : ℂ) :
    SS.Dact (fun r : ZMod 5 => zeta ^ r.val) angles state0 =
      fun x => zeta ^ 0 * state0 x := by
  simpa using SS.Dact_eq_global_of_SS (fun r : ZMod 5 => zeta ^ r.val) angles (0 : ZMod 5) state0 support0

theorem fiber1 : ∀ x, data1 x ≠ ZQ.zero → SS.weight angles x = (4 : ZMod 5) := by decide
theorem support1 : SS.SSConditionState angles (4 : ZMod 5) state1 := by
  intro x hx
  apply fiber1 x
  intro hz
  apply hx
  simp [state1, stC, hz, toC_zero]
theorem logical1 (zeta : ℂ) :
    SS.Dact (fun r : ZMod 5 => zeta ^ r.val) angles state1 =
      fun x => zeta ^ 4 * state1 x := by
  simpa using SS.Dact_eq_global_of_SS (fun r : ZMod 5 => zeta ^ r.val) angles (4 : ZMod 5) state1 support1

open scoped BigOperators
def totalAngle (x : SS.BitString 6) : Nat := ∑ j, if x j then (angles j).val else 0
theorem residue_eq : ∀ x, totalAngle x % 5 = (SS.weight angles x).val := by decide
def physicalGate (zeta : ℂ) (psi : SS.State 6 ℂ) : SS.State 6 ℂ :=
  fun x => (∏ j, zeta ^ (if x j then (angles j).val else 0)) * psi x
theorem physical_eq (zeta : ℂ) (hz : zeta ^ 5 = 1) (psi : SS.State 6 ℂ) :
    physicalGate zeta psi = SS.Dact (fun r : ZMod 5 => zeta ^ r.val) angles psi := by
  funext x
  have hp : zeta ^ totalAngle x = zeta ^ (totalAngle x % 5) := by
    calc
      zeta ^ totalAngle x = zeta ^ (totalAngle x % 5 + 5 * (totalAngle x / 5)) := by
        rw [Nat.mod_add_div]
      _ = zeta ^ (totalAngle x % 5) := by rw [pow_add, pow_mul, hz, one_pow, mul_one]
  simp only [physicalGate, SS.Dact, Finset.prod_pow_eq_pow_sum]
  change zeta ^ totalAngle x * psi x = _
  rw [hp, residue_eq]
def encode (alpha beta : ℂ) : SS.State 6 ℂ := fun x => alpha * state0 x + beta * state1 x
theorem physical_logical (zeta : ℂ) (hz : zeta ^ 5 = 1) (alpha beta : ℂ) :
    physicalGate zeta (encode alpha beta) = encode (zeta ^ 0 * alpha) (zeta ^ 4 * beta) := by
  rw [physical_eq zeta hz]
  funext x
  have h0 := congrFun (logical0 zeta) x
  have h1 := congrFun (logical1 zeta) x
  simp only [SS.Dact] at h0 h1 ⊢
  simp only [encode]
  calc
    _ = alpha * (zeta ^ (SS.weight angles x).val * state0 x) + beta * (zeta ^ (SS.weight angles x).val * state1 x) := by ring
    _ = _ := by rw [h0, h1]; ring
theorem distance : SS.HasDistance ![state0, state1] 3 := by
  rw [state0_matches, state1_matches]; exact canonical_is_code
theorem normalized0 : SS.innerC state0 state0 = 1 := by
  rw [state0_matches]; exact c36_normalized
theorem normalized1 : SS.innerC state1 state1 = 1 := by
  rw [state1_matches]; exact d36_normalized
theorem orthogonal : SS.innerC state0 state1 = 0 := by
  rw [state0_matches, state1_matches]; exact c36_orthogonal_d36
end
end SSLPExplorerCase

run_cmd do
  let env ← Lean.getEnv
  let roots : Array Lean.Name := #[`SSLPExplorerCase.distance, `SSLPExplorerCase.normalized0, `SSLPExplorerCase.normalized1, `SSLPExplorerCase.orthogonal, `SSLPExplorerCase.logical0, `SSLPExplorerCase.logical1, `SSLPExplorerCase.physical_logical]
  for root in roots do
    if (env.checked.get.find? root).isNone then
      throwError "Missing checked declaration: {root}"
  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for name in state.axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "Unexpected axiom: {name}"
  Lean.logInfo m!"SSLP_CASE_KERNEL_OK roots={roots.size} axioms={state.axioms}"
