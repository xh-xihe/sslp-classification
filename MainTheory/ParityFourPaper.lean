import MainTheory.ParityFourConnectivity
import MainTheory.ParityFourPolytope

/-! Literal Fourier and boundary-support assertions in the parity-four proof. -/

namespace MainTheory.ParityFour

open scoped BigOperators

noncomputable section

theorem probability_character_formula (a : Fin 4 → ℝ) (x : Cube) :
    probability a x = (1 + ∑ i, a i * character (SS.stdBasis i) x) / 8 := by
  simp only [probability, character_single]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem probability_pair_moment_zero (a : Fin 4 → ℝ) (j : Fin 6) (b : Bool) :
    moment (probability a) b (pairMask j) = 0 := by
  rw [moment_points]
  fin_cases j <;> cases b <;>
    norm_num [probability, Fin.sum_univ_succ, parity_point, character_pair,
      pairLeft, pairRight, point_apply, BooleanCube.sign, Fin.succ,
      Nat.testBit, Nat.shiftRight_eq_div_pow] <;> ring

theorem two_body_moment_zero (p : Cube → ℝ) (hp : MomentEquations p)
    (z : Cube) (hz : SS.hammingWt z = 2) (b : Bool) : moment p b z = 0 := by
  have hm : ∃ j, z = pairMask j := by
    have h : ∀ z : Cube, SS.hammingWt z = 2 → ∃ j, z = pairMask j := by decide
    exact h z hz
  obtain ⟨j, rfl⟩ := hm
  rw [momentEquations_probability p hp]
  exact probability_pair_moment_zero _ _ _

theorem interior_probability_positive (a : Fin 4 → ℝ) (ha : ∑ i, |a i| < 1)
    (x : Cube) : 0 < probability a x := by
  have ht : ∀ i, -|a i| ≤ a i * BooleanCube.sign (x i) := by
    intro i
    cases x i <;> simp only [BooleanCube.sign, Bool.false_eq_true, ↓reduceIte,
      mul_one, mul_neg, neg_le_neg_iff]
    · exact neg_abs_le _
    · exact le_abs_self _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
  rw [Finset.sum_neg_distrib] at hs
  unfold probability
  apply div_pos _ (by norm_num)
  linarith

private theorem abs_mul_realSign (r : ℝ) : |r| * Real.sign r = r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [abs_of_neg h, Real.sign_of_neg h]; ring
  · simp
  · rw [abs_of_pos h, Real.sign_of_pos h, mul_one]

theorem boundary_support_formula (a : Fin 4 → ℝ) (ha : ∑ i, |a i| = 1)
    (x : Cube) :
    8 * probability a x =
      ∑ i ∈ Finset.univ.filter (fun i => a i ≠ 0),
        |a i| * (1 + Real.sign (a i) * character (SS.stdBasis i) x) := by
  rw [Finset.sum_filter]
  have hterm (i : Fin 4) :
      (if a i ≠ 0 then |a i| * (1 + Real.sign (a i) * character (SS.stdBasis i) x)
        else 0) = |a i| + a i * character (SS.stdBasis i) x := by
    by_cases hi : a i = 0
    · simp [hi]
    · rw [if_pos hi, mul_add, mul_one, ← mul_assoc, abs_mul_realSign]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ha]
  simp only [character_single, probability]
  ring

private theorem boundary_term_nonnegative (r : ℝ) (b : Bool) :
    0 ≤ |r| * (1 + Real.sign r * BooleanCube.sign b) := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [Real.sign_of_neg h]
    cases b <;> simp [BooleanCube.sign, abs_nonneg]
  · simp
  · rw [Real.sign_of_pos h]
    cases b <;> simp [BooleanCube.sign, abs_nonneg]

private theorem boundary_term_positive_iff (r : ℝ) (b : Bool) :
    0 < |r| * (1 + Real.sign r * BooleanCube.sign b) ↔
      r ≠ 0 ∧ BooleanCube.sign b = Real.sign r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    cases b <;> simp [BooleanCube.sign, ne_of_lt h] <;> linarith
  · simp [BooleanCube.sign]
  · rw [Real.sign_of_pos h, abs_of_pos h]
    cases b <;> norm_num [BooleanCube.sign, ne_of_gt h, h]

theorem boundary_support_positive_iff (a : Fin 4 → ℝ) (ha : ∑ i, |a i| = 1)
    (x : Cube) :
    0 < probability a x ↔
      ∃ i, a i ≠ 0 ∧ character (SS.stdBasis i) x = Real.sign (a i) := by
  have hs := boundary_support_formula a ha x
  rw [Finset.sum_filter] at hs
  have heq : (∑ i, if a i ≠ 0 then
      |a i| * (1 + Real.sign (a i) * character (SS.stdBasis i) x) else 0) =
      ∑ i, |a i| * (1 + Real.sign (a i) * BooleanCube.sign (x i)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i = 0 <;> simp [hi, character_single]
  rw [heq] at hs
  have hn := Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => boundary_term_nonnegative (a i) (x i))
  simp only [Finset.mem_univ, true_and, boundary_term_positive_iff] at hn
  simp only [character_single]
  rw [← hn, ← hs]
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 8)).symm

end
end MainTheory.ParityFour
