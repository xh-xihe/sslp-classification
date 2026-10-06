import Orbit2.QuarticCoefficients

namespace Orbit2.Quartic
open scoped BigOperators

structure ReconstructedBlock where
  n : ℕ
  indices : Fin n → Fin 528
  expected : Matrix (Fin n) (Fin n) ℤ
  coefficients : ∀ i j, twiceCoefficient (indices i) (indices j) = expected i j
  block : Fin 111
  energy : ∀ z : Fin 528 → ℂ,
    complexEnergy (fun i j => (expected i j : ℚ)) (fun i => z (indices i)) =
      2 * blockEnergy (checkedBlocks block) z

noncomputable def reconstructedEnergy (B : Fin 111 → ReconstructedBlock) (z : Fin 528 → ℂ) : ℝ :=
  (∑ b, complexEnergy (fun i j => ((B b).expected i j : ℚ))
    (fun i => z ((B b).indices i)))/24

theorem reconstructedEnergy_eq_family (B : Fin 111 → ReconstructedBlock)
    (horder : ∀ b, (B b).block = b) (z : Fin 528 → ℂ) :
    reconstructedEnergy B z = familyEnergy checkedBlocks z := by
  unfold reconstructedEnergy familyEnergy
  simp_rw [ReconstructedBlock.energy, horder]
  rw [← Finset.mul_sum]
  ring

end Orbit2.Quartic
