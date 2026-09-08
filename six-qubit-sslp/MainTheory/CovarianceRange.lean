import MainTheory.Covariance

/-!
# `eq:V-r`: the range of the covariance matrix

`lem:common-affine-span` introduces

  `V := range Sigma`,   `r := dim V`,

and then uses `mu + V = aff(T_0) = aff(T_1)` (`eq:affine-V`).  Until now this
repository never formed that object.  `MainTheory/Covariance.lean` works
throughout with `Submodule.span R (Set.range fun k => pt k - mu)`, the span of
the centred support, and its own module docstring asserts

  "so the range of `Sigma` is the span of the centred support, and the affine
   span is recovered as `mu + range Sigma`"

in prose only: there is no `LinearMap.range`, `mulVec` or `Matrix.rank` applied
to `cov` anywhere in the file.  So the display's `V` was undefined in Lean, `r`
was read off the affine span instead, and the equality of the two readings --
which is what licenses calling them both `r` -- was assumed.

This file proves it.

The route is not the manuscript's positivity argument but the factorisation
`Sigma = A A^T` with `A i k = sqrt(p k) (pt k i - mu i)`, which is available
because the weights are positive.  Then `range (A A^T) <= range A` is immediate
and `rank (A A^T) = rank A` is Mathlib's `rank_self_mul_conjTranspose`, so the
two subspaces agree by dimension.  The columns of `A` are the centred support
points rescaled by nonzero factors, so their span is the manuscript's.

`Covariance.quad_eq_sum_sq`, the repository's existing `eq:covariance-quadratic`,
is the manuscript's own route to the same fact and is left where it is; it is
used for the positivity half of the affine-span lemma, not for this.
-/

namespace MainTheory.CovarianceRange

open MainTheory.Covariance
open scoped Matrix

variable {n : ℕ} {iota : Type*} [Fintype iota]

/-- The square-root factor of a positively weighted covariance matrix:
`A i k = sqrt (p k) * (pt k i - mu i)`. -/
noncomputable def sqrtFactor (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu : Fin n → ℝ) : Matrix (Fin n) iota ℝ :=
  fun i k => Real.sqrt (p k) * (pt k i - mu i)

/-- **`Sigma = A A^T`.**  Only nonnegativity of the weights is needed. -/
theorem cov_eq_mul_transpose (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu : Fin n → ℝ) (hp : ∀ k, 0 ≤ p k) :
    cov p pt mu = sqrtFactor p pt mu * (sqrtFactor p pt mu)ᵀ := by
  funext i j
  simp only [cov, Matrix.mul_apply, Matrix.transpose_apply, sqrtFactor]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : Real.sqrt (p k) * Real.sqrt (p k) = p k := Real.mul_self_sqrt (hp k)
  calc p k * (pt k i - mu i) * (pt k j - mu j)
      = (Real.sqrt (p k) * Real.sqrt (p k)) * (pt k i - mu i) * (pt k j - mu j) := by
        rw [hk]
    _ = Real.sqrt (p k) * (pt k i - mu i) * (Real.sqrt (p k) * (pt k j - mu j)) := by
        ring

omit [Fintype iota] in
/-- The columns of the square-root factor are the centred support points,
rescaled by nonzero factors, so they span the same subspace. -/
theorem span_col_sqrtFactor (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu : Fin n → ℝ) (hp : ∀ k, 0 < p k) :
    Submodule.span ℝ (Set.range (sqrtFactor p pt mu).col)
      = Submodule.span ℝ (Set.range fun k => pt k - mu) := by
  have hcol : ∀ k, (sqrtFactor p pt mu).col k = Real.sqrt (p k) • (pt k - mu) := by
    intro k
    funext i
    simp [sqrtFactor, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
  have hne : ∀ k, Real.sqrt (p k) ≠ 0 := fun k =>
    ne_of_gt (Real.sqrt_pos.2 (hp k))
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [hcol k]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show pt k - mu ∈ Submodule.span ℝ (Set.range (sqrtFactor p pt mu).col)
    have hk : pt k - mu = (Real.sqrt (p k))⁻¹ • (sqrtFactor p pt mu).col k := by
      rw [hcol k, smul_smul, inv_mul_cancel₀ (hne k), one_smul]
    rw [hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **`eq:V-r`.**  The range of the covariance matrix is the span of the
centred support, so the manuscript's `V` and the repository's centred-support
span are the same subspace and `r` has one meaning. -/
theorem range_cov_eq_span (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu : Fin n → ℝ) (hp : ∀ k, 0 < p k) :
    LinearMap.range (Matrix.mulVecLin (cov p pt mu))
      = Submodule.span ℝ (Set.range fun k => pt k - mu) := by
  classical
  set A := sqrtFactor p pt mu with hA
  have hcov : cov p pt mu = A * Aᵀ :=
    cov_eq_mul_transpose p pt mu fun k => (hp k).le
  have hstar : (Aᴴ : Matrix iota (Fin n) ℝ) = Aᵀ := by
    funext k i
    simp [Matrix.conjTranspose_apply]
  have hle : LinearMap.range (Matrix.mulVecLin (A * Aᵀ))
      ≤ LinearMap.range (Matrix.mulVecLin A) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨Aᵀ.mulVec v, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    exact Matrix.mulVec_mulVec v A Aᵀ
  have hrank : (A * Aᵀ).rank = A.rank := by
    have := Matrix.rank_self_mul_conjTranspose A
    rwa [hstar] at this
  have heq : LinearMap.range (Matrix.mulVecLin (A * Aᵀ))
      = LinearMap.range (Matrix.mulVecLin A) :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  rw [hcov, heq, Matrix.range_mulVecLin, hA]
  exact span_col_sqrtFactor p pt mu hp

/-- **`eq:affine-V`, the middle term.**  With `V` now defined, the affine span
of the support is `mu + V` whenever `mu` lies in it. -/
theorem affineSpan_eq_mu_add_range (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu : Fin n → ℝ) (hp : ∀ k, 0 < p k)
    (hmu : mu ∈ affineSpan ℝ (Set.range pt)) :
    (affineSpan ℝ (Set.range pt)).direction
      = LinearMap.range (Matrix.mulVecLin (cov p pt mu)) := by
  rw [range_cov_eq_span p pt mu hp, ← centeredHull_eq_affineSpan pt mu hmu,
    centeredHull, AffineSubspace.direction_mk']

end MainTheory.CovarianceRange
