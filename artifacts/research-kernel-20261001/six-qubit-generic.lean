import SS.ExactCode
import Lean.Util.CollectAxioms
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace SSLPResearchCase
open SS.ExactAmplitude SS.ExactCode
open scoped BigOperators
def num (s : SS.BitString 6) : Nat := ∑ i, if s i then 2 ^ i.val else 0
def nbit (m : Nat) : SS.BitString 6 := fun i => Nat.testBit m i.val
theorem num_lt : ∀ s, num s < 64 := by decide
theorem nbit_num : ∀ s, nbit (num s) = s := by decide
def c0 (s : SS.BitString 6) : ZQ := if num s = 0 then z8 0 0 2 0 0 0 0 0 else if num s = 23 then z8 0 0 2 0 0 0 0 0 else if num s = 27 then z8 0 0 2 0 0 0 0 0 else if num s = 29 then z8 0 0 2 0 0 0 0 0 else if num s = 30 then z8 0 0 2 0 0 0 0 0 else if num s = 35 then z8 0 2 0 0 0 0 0 0 else if num s = 37 then z8 0 (-1) 0 0 0 0 0 1 else if num s = 38 then z8 0 (-1) 0 0 0 0 0 (-1) else if num s = 41 then z8 0 (-1) 0 0 0 0 0 (-1) else if num s = 42 then z8 0 (-1) 0 0 0 0 0 1 else if num s = 44 then z8 0 2 0 0 0 0 0 0 else if num s = 48 then z8 0 0 2 0 0 0 0 0 else ZQ.zero
def L0 : List (SS.BitString 6) := [nbit 0, nbit 23, nbit 27, nbit 29, nbit 30, nbit 35, nbit 37, nbit 38, nbit 41, nbit 42, nbit 44, nbit 48]
def c1 (s : SS.BitString 6) : ZQ := if num s = 15 then z8 0 0 2 0 0 0 0 0 else if num s = 19 then z8 0 (-2) 0 0 0 0 0 0 else if num s = 21 then z8 0 1 0 0 0 0 0 1 else if num s = 22 then z8 0 1 0 0 0 0 0 (-1) else if num s = 25 then z8 0 1 0 0 0 0 0 (-1) else if num s = 26 then z8 0 1 0 0 0 0 0 1 else if num s = 28 then z8 0 (-2) 0 0 0 0 0 0 else if num s = 33 then z8 0 0 (-2) 0 0 0 0 0 else if num s = 34 then z8 0 0 (-2) 0 0 0 0 0 else if num s = 36 then z8 0 0 (-2) 0 0 0 0 0 else if num s = 40 then z8 0 0 (-2) 0 0 0 0 0 else if num s = 63 then z8 0 0 2 0 0 0 0 0 else ZQ.zero
def L1 : List (SS.BitString 6) := [nbit 15, nbit 19, nbit 21, nbit 22, nbit 25, nbit 26, nbit 28, nbit 33, nbit 34, nbit 36, nbit 40, nbit 63]
def coeff : Fin 2 → SS.BitString 6 → ZQ := ![c0, c1]
def supports : Fin 2 → List (SS.BitString 6) := ![L0, L1]
theorem support_nodup : ∀ j, (supports j).Nodup := by decide
theorem vanishes : ∀ j s, s ∉ supports j → coeff j s = ZQ.zero := by decide
theorem gram_check : ∀ j k, zmat (coeff j) (coeff k) (supports k) (fun _ => false) (fun _ => false) =
    if j = k then z8 120 0 0 0 0 0 0 0 else ZQ.zero := by decide
theorem finite_kl : ∀ m < 64, ∀ z < 64,
    (⟨nbit m, nbit z⟩ : SS.PauliString 6).wt ≤ 2 → ∀ j k,
    zmat (coeff j) (coeff k) (supports k) (nbit m) (nbit z) =
      if j = k then zmat (coeff 0) (coeff 0) (supports 0) (nbit m) (nbit z) else ZQ.zero := by decide
noncomputable section
def states : Fin 2 → SS.State 6 ℂ := fun j => stC (scale 120) (coeff j)
theorem orthonormal : ∀ j k, SS.innerC (states j) (states k) = if j = k then 1 else 0 :=
  orthonormal_of_checks 120 (by decide) coeff supports support_nodup vanishes gram_check
theorem distance : SS.HasDistance states 3 := by
  apply distance_of_checks (scale 120) coeff supports 0 3 support_nodup vanishes
  intro P hw j k
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := finite_kl (num P.x) (num_lt _) (num P.z) (num_lt _) (by rw [hx, hz]; exact hw) j k
  rwa [hx, hz] at h
end
def angles : Fin 6 → Nat := ![1, 1, 1, 1, 2, 3]
def residues : Fin 2 → Nat := ![0, 4]
theorem fiber_check : ∀ j s, coeff j s ≠ ZQ.zero → exponent angles s % 5 = residues j := by decide
theorem gate_action (zeta : ℂ) (hz : zeta ^ 5 = 1) (alpha : Fin 2 → ℂ) :
    physicalGate zeta angles (encode (scale 120) coeff alpha) =
      encode (scale 120) coeff (fun j => zeta ^ residues j * alpha j) :=
  physical_logical zeta 5 hz angles residues (scale 120) coeff fiber_check alpha
end SSLPResearchCase
run_cmd do
  let env ← Lean.getEnv
  let roots : Array Lean.Name := #[`SSLPResearchCase.orthonormal, `SSLPResearchCase.distance, `SSLPResearchCase.gate_action]
  for root in roots do
    if (env.checked.get.find? root).isNone then
      throwError "Missing checked declaration: {root}"
  let action : Lean.CollectAxioms.M Unit := roots.forM Lean.CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for name in state.axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "Unexpected axiom: {name}"
  Lean.logInfo m!"SSLP_CASE_KERNEL_OK roots={roots.size} axioms={state.axioms}"
