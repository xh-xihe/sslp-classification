import Orbit2.FiveQubit

namespace Orbit2.FiveQubit
open scoped BigOperators
open Orbit2.TensorPauli

theorem local_row_zero : ∀ p s t, t ≠ flipSite p s → localG p s t = 0 := by
  decide +kernel

/-- The efficient finite action is exactly the tensor-Pauli matrix action. -/
theorem operator_row (p : Label 5) (s t : Fin 5 → Fin 2) :
    operator p s t = if t = flip p s then (amplitude p s : ℂ) else 0 := by
  by_cases h : t = flip p s
  · subst t
    simp [operator, tensor, localC, Matrix.map_apply, amplitude, map_prod]
  · simp only [h, if_false]
    obtain ⟨i,hi⟩ : ∃ i, t i ≠ flip p s i := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    unfold operator tensor
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [localC, Matrix.map_apply, local_row_zero _ _ _ hi]

theorem operator_seed (p : Label 5) (j : Fin 2) (s : Fin 5 → Fin 2) :
    (∑ t, operator p s t * (seed j t : ℂ)) = (act p (seed j) s : ℂ) := by
  simp_rw [operator_row]
  simp [act, GaussianInt.toComplex_mul]

noncomputable def code : Matrix (Fin 5 → Fin 2) (Fin 2) ℂ := fun s j => (seed j s : ℂ)/8

theorem code_action (p : Label 5) :
    operator p * code = fun s j => (act p (seed j) s : ℂ)/8 := by
  ext s j
  simp only [Matrix.mul_apply, code, ← mul_div_assoc, ← Finset.sum_div]
  rw [operator_seed]

/-- The finite Gaussian certificate proves full complex matrix KL, not just
an integer arithmetic surrogate. -/
theorem code_pure_KL (p : Label 5) (hp : weight p ≤ 2) :
    code.conjTranspose * operator p * code =
      if p = (fun _ => 0) then 1 else 0 := by
  rw [Matrix.mul_assoc, code_action]
  ext j k
  calc
    _ = ((∑ s, star (seed j s) * act p (seed k) s : GaussianInt) : ℂ)/64 := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, code,
        map_sum, GaussianInt.toComplex_mul, GaussianInt.toComplex_star,
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      simp only [star_div₀, star_ofNat, starRingEnd_apply]
      ring
    _ = _ := by
      rw [pure_KL_G p hp j k]
      by_cases h : p = fun _ => 0 <;> by_cases hj : j = k <;>
        norm_num [h, hj, Matrix.one_apply, GaussianInt.toComplex_def]

theorem code_isometry : code.conjTranspose * code = 1 := by
  have h := code_pure_KL (fun _ => 0) (by simp [weight])
  simpa [operator_zero] using h

theorem code_logical : operator ![3,3,3,0,0] * code =
    fun s j => (if j = 0 then 1 else -1) * code s j := by
  rw [code_action]
  ext s j
  rw [logical_G]
  by_cases h : j = 0 <;> simp [h, code, neg_div]

end Orbit2.FiveQubit
