import MainTheory.DiagonalInfinitesimal
import MainTheory.ProjectorCompression

namespace MainTheory.DiagonalInfinitesimal

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells

noncomputable section

variable {n K d : ℕ}

theorem numberKernel_eq_half_one_sub (j : Fin n) :
    numberKernel j = (2 : ℂ)⁻¹ •
      (1 - MainTheory.PauliKernelTrace.pauliKernel (MainTheory.NumberOperator.zPauli j)) := by
  classical
  ext x y
  let ψ : SS.State n ℂ := fun z => if z = y then 1 else 0
  have he := congrFun (numberKernel_action j ψ) x
  change kernelAction (numberKernel j) ψ x =
    (ψ x - SS.pauliAct (MainTheory.NumberOperator.zPauli j) ψ x) / 2 at he
  rw [← MainTheory.PauliKernelTrace.kernelAction_pauliKernel] at he
  simpa [kernelAction, ψ, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using he

/-- Actual distance at least two supplies every number-operator compression. -/
theorem numberKernel_compression (C : MainTheory.CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) : ∃ μ : Fin n → ℂ, ∀ j,
      (CodeProjector.ofFrame C.frame).kernel * numberKernel j *
        (CodeProjector.ofFrame C.frame).kernel = μ j • (CodeProjector.ofFrame C.frame).kernel := by
  have hz : ∀ j : Fin n, ∃ lam : ℂ,
      (CodeProjector.ofFrame C.frame).kernel *
        MainTheory.PauliKernelTrace.pauliKernel (MainTheory.NumberOperator.zPauli j) *
        (CodeProjector.ofFrame C.frame).kernel = lam • (CodeProjector.ofFrame C.frame).kernel := by
    intro j
    apply MainTheory.ProjectorCompression.pauli_compression
    have hw : (MainTheory.NumberOperator.zPauli j).wt ≤ 1 := SixQubit.wt_pureZ_single j
    omega
  choose lam hlam using hz
  refine ⟨fun j => (2 : ℂ)⁻¹ * (1 - lam j), ?_⟩
  intro j
  rw [numberKernel_eq_half_one_sub, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    (CodeProjector.ofFrame C.frame).idempotent, hlam]
  module

/-- A genuine exact KL code detects the infinitesimal generator of every
physical diagonal one-parameter stabilizer, so its projective action is trivial. -/
theorem exact_code_one_parameter_scalar (C : MainTheory.CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) (h : Fin n → ℝ)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup (CodeProjector.ofFrame C.frame)) :
    ∃ μ : Fin n → ℂ, ∀ t : ℝ,
      operator (expAngles (t • h)) * (CodeProjector.ofFrame C.frame).kernel =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) *
          (∑ j, (h j : ℂ) * μ j)) • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨μ, hμ⟩ := numberKernel_compression C hd
  exact ⟨μ, fun t => one_parameter_scalar _ h μ hμ hp t⟩

end

end MainTheory.DiagonalInfinitesimal
