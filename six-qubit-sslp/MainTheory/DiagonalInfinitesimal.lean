import MainTheory.PhysicalStabilizerTopology
import MainTheory.NumberOperator

namespace MainTheory.DiagonalInfinitesimal

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells

noncomputable section

variable {n : ℕ}

def numberKernel (j : Fin n) : OperatorKernel n :=
  Matrix.diagonal fun x => if x j then 1 else 0

def hamiltonian (h : Fin n → ℝ) : OperatorKernel n :=
  Matrix.diagonal fun x => (angle h x : ℂ)

theorem numberKernel_action (j : Fin n) (ψ : SS.State n ℂ) :
    kernelAction (numberKernel j) ψ = MainTheory.NumberOperator.numberOp j ψ := by
  funext x
  rw [MainTheory.NumberOperator.numberOp_apply]
  simp only [kernelAction, numberKernel, Matrix.diagonal_apply]
  simp

theorem hamiltonian_eq_sum (h : Fin n → ℝ) :
    hamiltonian h = ∑ j, (h j : ℂ) • numberKernel j := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [hamiltonian, Matrix.diagonal_apply_eq, angle, Complex.ofReal_sum,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, numberKernel]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp
  · simp [hamiltonian, numberKernel, Matrix.sum_apply, hxy]

theorem operator_entry (t : ℝ) (h : Fin n → ℝ) (x y : SS.BitString n) :
    operator (expAngles (t • h)) x y =
      if x = y then Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (t : ℂ) * (angle h x : ℂ)) else 0 := by
  simp only [operator, Matrix.diagonal_apply, phase_expAngles, angle_smul,
    Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- If every time of the one-parameter diagonal group preserves P, its
diagonal infinitesimal generator commutes with P. -/
theorem hamiltonian_commutes (P : CodeProjector n) (h : Fin n → ℝ)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup P) :
    hamiltonian h * P.kernel = P.kernel * hamiltonian h := by
  ext x y
  simp only [hamiltonian, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hxy : P.kernel x y = 0
  · simp [hxy]
  have he : angle h x = angle h y := by
    by_contra hn
    have hd : angle h x - angle h y ≠ 0 := sub_ne_zero.mpr hn
    let t : ℝ := 1 / (2 * (angle h x - angle h y))
    have hphase := hp t x y hxy
    rw [phase_expAngles, phase_expAngles, ← div_eq_one, ← Circle.exp_sub,
      angle_smul, angle_smul] at hphase
    have harg : 2 * Real.pi * (t * angle h x) -
        2 * Real.pi * (t * angle h y) = Real.pi := by
      dsimp [t]
      field_simp [hd]
    rw [harg] at hphase
    exact Circle.exp_pi_ne_one hphase
  rw [he]
  ring

theorem hamiltonian_compression (P : CodeProjector n) (h : Fin n → ℝ)
    (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel) :
    P.kernel * hamiltonian h * P.kernel =
      (∑ j, (h j : ℂ) * μ j) • P.kernel := by
  rw [hamiltonian_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
  rw [Finset.sum_smul]

theorem hamiltonian_on_code (P : CodeProjector n) (h : Fin n → ℝ)
    (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup P) :
    hamiltonian h * P.kernel = (∑ j, (h j : ℂ) * μ j) • P.kernel := by
  rw [← hamiltonian_compression P h μ hμ, ← hamiltonian_commutes P h hp,
    Matrix.mul_assoc, P.idempotent]

/-- The one-parameter physical group acts as a scalar on the full code
projector; the proof is entrywise and uses no differentiation oracle. -/
theorem one_parameter_scalar (P : CodeProjector n) (h : Fin n → ℝ)
    (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup P) (t : ℝ) :
    operator (expAngles (t • h)) * P.kernel =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) *
        (∑ j, (h j : ℂ) * μ j)) • P.kernel := by
  ext x y
  rw [operator, Matrix.diagonal_mul]
  change (phase (expAngles (t • h)) x : ℂ) * P.kernel x y = _
  simp only [phase_expAngles, angle_smul, Circle.coe_exp, Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : P.kernel x y = 0
  · simp [hxy]
  have hentry := congrFun (congrFun (hamiltonian_on_code P h μ hμ hp) x) y
  simp only [hamiltonian, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at hentry
  have hv := mul_right_cancel₀ hxy hentry
  congr 2
  push_cast
  rw [← hv]
  ring

end

end MainTheory.DiagonalInfinitesimal
