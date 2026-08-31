import MainTheory.D3LogicalSecondEigenvector

/-!
# Normalizing the two logical eigenvectors

This file normalizes a nonzero vector in the concrete coordinate space
`Fin 2 → ℂ`.  The norm is defined explicitly from `Complex.normSq`, so the
proof does not rely on silently identifying the plain function type with a
bundled Euclidean space.  The normalized vector and its normalized explicit
perpendicular are proved orthonormal for `coordinateInner`.
-/

namespace MainTheory.D3LogicalNormalization

open MainTheory
open MainTheory.D3LogicalCoordinateUnitary
open MainTheory.D3LogicalSecondEigenvector
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Squared Euclidean norm of a two-component complex vector. -/
def coordinateNormSq (v : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (v 0) + Complex.normSq (v 1)

/-- Euclidean norm of a two-component complex vector. -/
def coordinateNorm (v : Fin 2 → ℂ) : ℝ :=
  Real.sqrt (coordinateNormSq v)

/-- The custom coordinate inner product on a vector with itself is exactly
the real squared norm, embedded into `ℂ`. -/
theorem coordinateInner_self_eq_normSq (v : Fin 2 → ℂ) :
    coordinateInner v v = (coordinateNormSq v : ℂ) := by
  unfold coordinateInner coordinateNormSq
  rw [Fin.sum_univ_two]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- The squared coordinate norm is positive on a nonzero vector. -/
theorem coordinateNormSq_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    0 < coordinateNormSq v := by
  unfold coordinateNormSq
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Complex.normSq_pos.mpr h1)
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h0)
      (Complex.normSq_nonneg _)

/-- The coordinate norm itself is positive on a nonzero vector. -/
theorem coordinateNorm_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    0 < coordinateNorm v := by
  exact Real.sqrt_pos.2 (coordinateNormSq_pos hv)

/-- Squaring the coordinate norm recovers the squared norm. -/
theorem coordinateNorm_sq (v : Fin 2 → ℂ) :
    coordinateNorm v ^ 2 = coordinateNormSq v := by
  exact Real.sq_sqrt
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

/-- Normalize a logical coordinate vector by its explicit real norm. -/
def normalized (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ((coordinateNorm v : ℂ)⁻¹) • v

/-- Linearity of the coordinate product in its second input. -/
theorem coordinateInner_smul_right (a : ℂ) (v z : Fin 2 → ℂ) :
    coordinateInner v (a • z) = a * coordinateInner v z := by
  simp [coordinateInner, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- Hermitian conjugate symmetry of the explicit coordinate product. -/
theorem coordinateInner_conj_symm (v z : Fin 2 → ℂ) :
    coordinateInner z v = star (coordinateInner v z) := by
  simp [coordinateInner, Fin.sum_univ_two]
  ring

/-- A normalized nonzero coordinate vector has self-inner-product one. -/
@[simp] theorem coordinateInner_normalized_self
    {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    coordinateInner (normalized v) (normalized v) = 1 := by
  have hr : (coordinateNorm v : ℂ) ≠ 0 := by
    exact_mod_cast (coordinateNorm_pos hv).ne'
  have hstar : star ((coordinateNorm v : ℂ)⁻¹) =
      (coordinateNorm v : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  have hsq : (coordinateNorm v : ℂ) ^ 2 =
      (coordinateNormSq v : ℂ) := by
    exact_mod_cast coordinateNorm_sq v
  unfold normalized
  rw [coordinateInner_smul_left, coordinateInner_smul_right,
    coordinateInner_self_eq_normSq, hstar, ← hsq]
  field_simp [hr]

/-- The two separately normalized complementary vectors remain orthogonal. -/
@[simp] theorem coordinateInner_normalized_perpendicular
    (v : Fin 2 → ℂ) :
    coordinateInner (normalized v)
      (normalized (perpendicular v)) = 0 := by
  unfold normalized
  rw [coordinateInner_smul_left, coordinateInner_smul_right,
    coordinateInner_perpendicular]
  ring

/-- Orthogonality in the reverse order. -/
@[simp] theorem coordinateInner_normalized_perpendicular_rev
    (v : Fin 2 → ℂ) :
    coordinateInner (normalized (perpendicular v))
      (normalized v) = 0 := by
  rw [coordinateInner_conj_symm,
    coordinateInner_normalized_perpendicular]
  exact star_zero ℂ

end

end MainTheory.D3LogicalNormalization
