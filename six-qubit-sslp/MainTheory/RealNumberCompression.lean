import MainTheory.NumberKernelKL

namespace MainTheory.DiagonalInfinitesimal

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells

noncomputable section

variable {n : ℕ}

theorem numberKernel_star (j : Fin n) : star (numberKernel j) = numberKernel j := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [numberKernel, Matrix.star_apply, Matrix.diagonal_apply_eq]
    split <;> simp
  · simp [numberKernel, Matrix.star_apply, Matrix.diagonal, hxy, Ne.symm hxy]

/-- Hermitian scalar compression may always use a real scalar, even for the
zero projector; no nonzero-rank cancellation is smuggled into this step. -/
theorem numberKernel_compression_real {K d : ℕ}
    (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    ∃ μ : Fin n → ℝ, ∀ j,
      (CodeProjector.ofFrame C.frame).kernel * numberKernel j *
        (CodeProjector.ofFrame C.frame).kernel = (μ j : ℂ) • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨mu, hmu⟩ := numberKernel_compression C hd
  let P := CodeProjector.ofFrame C.frame
  refine ⟨fun j => (mu j).re, fun j => ?_⟩
  have hh := congrArg star (hmu j)
  simp only [star_mul, star_smul, (CodeProjector.ofFrame C.frame).hermitian,
    numberKernel_star] at hh
  have hs : star (mu j) • P.kernel = mu j • P.kernel := by
    rw [← hh]
    simpa only [Matrix.mul_assoc] using hmu j
  have hr : ((mu j).re : ℂ) = (mu j + star (mu j)) / 2 := by
    apply Complex.ext <;> simp
  change P.kernel * numberKernel j * P.kernel = ((mu j).re : ℂ) • P.kernel
  rw [hmu, hr, div_eq_inv_mul, mul_smul, add_smul, hs]
  module

/-- Exactly the real c_h and exp(2 pi i t c_h) appearing in the paper. -/
theorem exact_code_one_parameter_real_scalar {K d : ℕ}
    (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d) (h : Fin n → ℝ)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup (CodeProjector.ofFrame C.frame)) :
    ∃ μ : Fin n → ℝ, ∀ t : ℝ,
      operator (expAngles (t • h)) * (CodeProjector.ofFrame C.frame).kernel =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) *
          ((∑ j, h j * μ j : ℝ) : ℂ)) • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨μ, hμ⟩ := numberKernel_compression_real C hd
  refine ⟨μ, fun t => ?_⟩
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
    one_parameter_scalar (CodeProjector.ofFrame C.frame) h (fun j => (μ j : ℂ)) hμ hp t

end

end MainTheory.DiagonalInfinitesimal
