import MainTheory.Orbit2PrintedQuartic

/-! The literal integer symmetric 528-by-528 Gram matrix, including its 36 zero rows. -/

namespace MainTheory.Orbit2FullGramMatrix

noncomputable section

open Orbit2 Orbit2.Quartic MainTheory.Orbit2RemainingCoordinates
open scoped BigOperators

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem block_properties : ∀ b : Fin 111,∀ i j : Fin (reconstructedBlocks b).n,
    (reconstructedBlocks b).expected i j=(reconstructedBlocks b).expected j i ∧
    (reconstructedBlocks b).expected i j % 2=0 ∧
    (¬Remaining ((reconstructedBlocks b).indices i) → (reconstructedBlocks b).expected i j=0) := by
  decide +kernel

theorem coefficient_properties (r c : Fin 528) :
    twiceCoefficient r c=twiceCoefficient c r ∧ twiceCoefficient r c % 2=0 ∧
      (¬Remaining r → twiceCoefficient r c=0) := by
  obtain ⟨⟨b,i⟩,hr⟩ := blockCoordinate_bijective.2 r
  obtain ⟨⟨d,j⟩,hc⟩ := blockCoordinate_bijective.2 c
  subst r c
  dsimp only [blockCoordinate]
  by_cases h : b=d
  · subst d
    rw [(reconstructedBlocks b).coefficients,(reconstructedBlocks b).coefficients]
    exact block_properties b i j
  · rw [cross_block_zero b d h i j,cross_block_zero d b (Ne.symm h) j i]
    simp

def M : Matrix (Fin 528) (Fin 528) ℤ := fun r c => twiceCoefficient r c/2

theorem twice_M (r c : Fin 528) : 2*M r c=twiceCoefficient r c := by
  have hd : (2 : ℤ)∣twiceCoefficient r c :=
    Int.dvd_iff_emod_eq_zero.mpr (coefficient_properties r c).2.1
  unfold M
  rw [mul_comm,Int.ediv_mul_cancel hd]

theorem symmetric : M.transpose=M := by
  ext r c
  exact congrArg (fun n : ℤ => n/2) (coefficient_properties c r).1

theorem zero_rows (r : Fin 528) (hr : ¬Remaining r) (c : Fin 528) : M r c=0 := by
  simp [M,(coefficient_properties r c).2.2 hr]

def quadraticEnergy (z : Fin 528 → ℂ) : ℂ :=
  ∑ r,∑ c,star (z r)*z c*(M r c : ℂ)

theorem full_energy (z : Fin 528 → ℂ) :
    fullCoefficientEnergy z=2*quadraticEnergy z := by
  unfold fullCoefficientEnergy quadraticEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  rw [← twice_M]
  push_cast
  ring

theorem matrix_identity (t : Fin 32 → ℂ) :
    MainTheory.Orbit2PrintedQuartic.Q t=(quadraticEnergy (quadraticMonomials t)).re/12 := by
  rw [MainTheory.Orbit2PrintedQuartic.Q_identity,orderedPolynomial_eq_fullEnergy,full_energy]
  norm_num [Complex.mul_re]
  ring

end

end MainTheory.Orbit2FullGramMatrix
