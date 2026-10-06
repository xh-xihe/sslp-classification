import MainTheory.LocalTensorKernel

/-! # Squared coefficient norms in blocks preserved by a unitary matrix -/

namespace MainTheory.BlockUnitaryNorm

open scoped Matrix

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sum_normSq_mulVec (U : Matrix I I ℂ) (hU : star U * U = 1) (v : I → ℂ) :
    ∑ i, Complex.normSq ((U *ᵥ v) i) = ∑ i, Complex.normSq (v i) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  change star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change (star v ᵥ* (star U * U)) ⬝ᵥ v = _
  rw [hU, Matrix.vecMul_one]

omit [DecidableEq I] in
theorem mulVec_mask (U : Matrix I I ℂ) (label : I → ℕ)
    (hblock : ∀ i j, label i ≠ label j → U i j = 0) (v : I → ℂ) (k : ℕ) :
    U *ᵥ (fun j => if label j = k then v j else 0) =
      fun i => if label i = k then (U *ᵥ v) i else 0 := by
  funext i
  by_cases hi : label i = k
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    by_cases hj : label j = k
    · rw [if_pos hj]
    · rw [if_neg hj, hblock i j (by omega), zero_mul, zero_mul]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    dsimp only
    by_cases hj : label j = k
    · rw [if_pos hj, hblock i j (by omega), zero_mul]
    · rw [if_neg hj, mul_zero]

/-- Every invariant coefficient block has its own conserved squared norm. -/
theorem sum_normSq_block (U : Matrix I I ℂ) (hU : star U * U = 1)
    (label : I → ℕ) (hblock : ∀ i j, label i ≠ label j → U i j = 0)
    (v : I → ℂ) (k : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i => label i = k), Complex.normSq ((U *ᵥ v) i)) =
      ∑ i ∈ Finset.univ.filter (fun i => label i = k), Complex.normSq (v i) := by
  have h := sum_normSq_mulVec U hU (fun i => if label i = k then v i else 0)
  rw [mulVec_mask U label hblock v k] at h
  simpa only [apply_ite, Complex.normSq_zero, Finset.sum_filter] using h

end

end MainTheory.BlockUnitaryNorm
