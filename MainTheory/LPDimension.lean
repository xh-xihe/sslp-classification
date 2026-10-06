import MainTheory.ActiveFace

/-!
# Dimension of the nonnegative feasible face

The inequalities are retained in the feasible set. A strictly positive feasible
point proves that its affine direction is the equality matrix's actual kernel.
-/

namespace MainTheory.LPDimension

open scoped BigOperators

noncomputable section

variable {r c : Type*} [Fintype r] [Fintype c]

def feasibleSet (A : Matrix r c ℝ) (b : r → ℝ) : Set (c → ℝ) :=
  {p | A.mulVec p = b ∧ ∀ j, 0 ≤ p j}

private theorem exists_small_positive (p v : c → ℝ) (hp : ∀ i, 0 < p i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε * |v i| < p i := by
  classical
  have hfinite : ∀ s : Finset c, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε * |v i| < p i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hs⟩ := ih
      let δ := p i / (|v i| + 1)
      have hd : 0 < δ := div_pos (hp i) (by positivity)
      refine ⟨min ε δ, lt_min hε hd, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hij | hj
      · subst j
        have hbound : δ * |v i| < p i := by
          dsimp [δ]
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < |v i| + 1)]
          nlinarith [hp i]
        exact (mul_le_mul_of_nonneg_right (min_le_right ε δ) (abs_nonneg _)).trans_lt hbound
      · exact (mul_le_mul_of_nonneg_right (min_le_left ε δ) (abs_nonneg _)).trans_lt (hs j hj)
  simpa using hfinite Finset.univ

omit [Fintype r] in
/-- Nonnegativity removes no affine direction when a positive feasible point exists. -/
theorem direction_eq_kernel_of_positive (A : Matrix r c ℝ) (b : r → ℝ)
    (p : c → ℝ) (heq : A.mulVec p = b) (hpos : ∀ i, 0 < p i) :
    (affineSpan ℝ (feasibleSet A b)).direction = LinearMap.ker A.mulVecLin := by
  apply le_antisymm
  · rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    change A.mulVec (x - y) = 0
    rw [Matrix.mulVec_sub, hx.1, hy.1, sub_self]
  · intro v hv
    have hv0 : A.mulVec v = 0 := hv
    obtain ⟨ε, hε, hsmall⟩ := exists_small_positive p v hpos
    have hp : p ∈ feasibleSet A b := ⟨heq, fun i => (hpos i).le⟩
    have hq : p + ε • v ∈ feasibleSet A b := by
      constructor
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, heq, hv0, smul_zero, add_zero]
      · intro i
        change 0 ≤ p i + ε * v i
        have hh := hsmall i
        have hneg := neg_abs_le (v i)
        have hmul := mul_le_mul_of_nonneg_left hneg hε.le
        nlinarith
    have hmem := AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hq) (mem_affineSpan ℝ hp)
    have hscaled : ε • v ∈ (affineSpan ℝ (feasibleSet A b)).direction := by
      simpa only [vsub_eq_sub, add_sub_cancel_left] using hmem
    exact (Submodule.smul_mem_iff _ hε.ne').mp hscaled

omit [Fintype r] in
/-- The paper's LP dimension formula, with every coordinate active. -/
theorem finrank_eq_card_sub_rank_of_positive (A : Matrix r c ℝ) (b : r → ℝ)
    (p : c → ℝ) (heq : A.mulVec p = b) (hpos : ∀ i, 0 < p i) :
    Module.finrank ℝ (affineSpan ℝ (feasibleSet A b)).direction =
      Fintype.card c - A.rank := by
  rw [direction_eq_kernel_of_positive A b p heq hpos]
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at h
  exact Nat.eq_sub_of_add_eq' h

end

end MainTheory.LPDimension
