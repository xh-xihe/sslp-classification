import Mathlib

namespace MainTheory.ProbabilityPhaseParametrization

theorem exists_phase (z : ℂ) (p : ℝ) (hp : Complex.normSq z = p) :
    ∃ alpha : ℝ, z = (Real.sqrt p : ℂ) * Complex.exp (Complex.I * (alpha : ℂ)) := by
  refine ⟨Complex.arg z, ?_⟩
  rw [← hp, ← Complex.norm_def, mul_comm Complex.I]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

end MainTheory.ProbabilityPhaseParametrization
