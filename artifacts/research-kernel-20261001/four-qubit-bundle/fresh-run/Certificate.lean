import SS.ExactCode
import Lean.Util.CollectAxioms
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace SSLPResearchCase
open SS.ExactAmplitude SS.ExactCode
open scoped BigOperators
def num (s : SS.BitString 4) : Nat := ∑ i, if s i then 2 ^ i.val else 0
def nbit (m : Nat) : SS.BitString 4 := fun i => Nat.testBit m i.val
theorem num_lt : ∀ s, num s < 16 := by decide
theorem nbit_num : ∀ s, nbit (num s) = s := by decide
def c0 (s : SS.BitString 4) : ZQ := if num s = 0 then z8 1 0 0 0 0 0 0 0 else if num s = 15 then z8 1 0 0 0 0 0 0 0 else ZQ.zero
def L0 : List (SS.BitString 4) := [nbit 0, nbit 15]
def c1 (s : SS.BitString 4) : ZQ := if num s = 3 then z8 1 0 0 0 0 0 0 0 else if num s = 12 then z8 1 0 0 0 0 0 0 0 else ZQ.zero
def L1 : List (SS.BitString 4) := [nbit 3, nbit 12]
def coeff : Fin 2 → SS.BitString 4 → ZQ := ![c0, c1]
def supports : Fin 2 → List (SS.BitString 4) := ![L0, L1]
theorem support_nodup : ∀ j, (supports j).Nodup := by decide
theorem vanishes : ∀ j s, s ∉ supports j → coeff j s = ZQ.zero := by decide
theorem gram_check : ∀ j k, zmat (coeff j) (coeff k) (supports k) (fun _ => false) (fun _ => false) =
    if j = k then z8 2 0 0 0 0 0 0 0 else ZQ.zero := by decide
theorem finite_kl : ∀ m < 16, ∀ z < 16,
    (⟨nbit m, nbit z⟩ : SS.PauliString 4).wt ≤ 1 → ∀ j k,
    zmat (coeff j) (coeff k) (supports k) (nbit m) (nbit z) =
      if j = k then zmat (coeff 0) (coeff 0) (supports 0) (nbit m) (nbit z) else ZQ.zero := by decide
noncomputable section
def states : Fin 2 → SS.State 4 ℂ := fun j => stC (scale 2) (coeff j)
theorem orthonormal : ∀ j k, SS.innerC (states j) (states k) = if j = k then 1 else 0 :=
  orthonormal_of_checks 2 (by decide) coeff supports support_nodup vanishes gram_check
theorem distance : SS.HasDistance states 2 := by
  apply distance_of_checks (scale 2) coeff supports 0 2 support_nodup vanishes
  intro P hw j k
  have hx := nbit_num P.x
  have hz := nbit_num P.z
  have h := finite_kl (num P.x) (num_lt _) (num P.z) (num_lt _) (by rw [hx, hz]; exact hw) j k
  rwa [hx, hz] at h
end
def angles : Fin 4 → Nat := ![1, 1, 1, 1]
def residues : Fin 2 → Nat := ![0, 2]
theorem fiber_check : ∀ j s, coeff j s ≠ ZQ.zero → exponent angles s % 4 = residues j := by decide
theorem gate_action (zeta : ℂ) (hz : zeta ^ 4 = 1) (alpha : Fin 2 → ℂ) :
    physicalGate zeta angles (encode (scale 2) coeff alpha) =
      encode (scale 2) coeff (fun j => zeta ^ residues j * alpha j) :=
  physical_logical zeta 4 hz angles residues (scale 2) coeff fiber_check alpha
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
