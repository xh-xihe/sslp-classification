import MainTheory.FiniteCubicMoments

/-! # Exact finite phase averages and actual positive moment entries

Fourth-root phases suffice to distinguish cubic occupation counts 0 through 3.
This proves the phase projection independently of the remaining orbit-3
permutation, translation and spectator-Clifford averages.
-/

namespace MainTheory.FinitePhaseAverage

open scoped BigOperators
noncomputable section

theorem fourth_phase_pair (a b : Fin 4) :
    (∑ p : Fin 4, Complex.I ^ (p.val * a.val) *
      star (Complex.I ^ (p.val * b.val))) = if a = b then 4 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [Fin.sum_univ_succ, pow_succ]

variable {J : Type*} [Fintype J] [DecidableEq J]

def character (p a : J → Fin 4) : ℂ := ∏ i, Complex.I ^ ((p i).val * (a i).val)

theorem tensor_pairing (a b : J → Fin 4) :
    (∑ p : J → Fin 4, character p a * star (character p b)) =
      if a = b then (4 : ℂ) ^ Fintype.card J else 0 := by
  classical
  unfold character
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : J) (p : Fin 4) =>
    Complex.I ^ (p.val * (a i).val) * star (Complex.I ^ (p.val * (b i).val)))]
  simp_rw [fourth_phase_pair]
  by_cases h : a = b
  · subst b
    simp
  · rw [if_neg h]
    have hi : ∃ i, a i ≠ b i := by
      by_contra hn
      apply h
      funext i
      by_contra he
      exact hn ⟨i, he⟩
    obtain ⟨i, hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

variable {I : Type*} [Fintype I] [DecidableEq I]

def phaseGram (counts : I → J → Fin 4) (v : I → ℂ) : Matrix I I ℝ :=
  MainTheory.FiniteCubicMoments.realGram (fun p i => character p (counts i) * v i)

omit [DecidableEq I] in
theorem phaseGram_posSemidef (counts : I → J → Fin 4) (v : I → ℂ) :
    (phaseGram counts v).PosSemidef := MainTheory.FiniteCubicMoments.realGram_posSemidef _

omit [Fintype I] [DecidableEq I] in
theorem phaseGram_apply (counts : I → J → Fin 4) (v : I → ℂ) (i j : I) :
    phaseGram counts v i j =
      if counts i = counts j then (4 : ℝ) ^ Fintype.card J *
        (star (v i) * v j).re else 0 := by
  unfold phaseGram
  rw [MainTheory.FiniteCubicMoments.realGram_apply]
  have ht (p : J → Fin 4) :
      (star (character p (counts i) * v i) * (character p (counts j) * v j)).re =
      ((character p (counts j) * star (character p (counts i))) * (star (v i) * v j)).re := by
    rw [star_mul]
    congr 1
    ring
  simp_rw [ht]
  rw [← Complex.re_sum, ← Finset.sum_mul, tensor_pairing]
  by_cases h : counts i = counts j
  · simp only [h, if_true]
    norm_cast
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  · simp [h, Ne.symm h]

end
end MainTheory.FinitePhaseAverage
