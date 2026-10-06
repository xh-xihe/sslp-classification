import MainTheory.NumberKernelKL
import MainTheory.FiniteImageComponents

namespace MainTheory.PhysicalRelativeAction

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.DiagonalInfinitesimal

noncomputable section

variable {n : ℕ}

def relativeAction (P : CodeProjector n) (x₀ : SS.BitString n) (u : Torus n) : OperatorKernel n :=
  ((phase u x₀ : ℂ))⁻¹ • (operator u * P.kernel)

theorem angle_sub (θ η : Fin n → ℝ) (x : SS.BitString n) :
    angle (θ - η) x = angle θ x - angle η x := by
  simp only [angle, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp

theorem same_cell_direction (P : CodeProjector n) (a : Labels n)
    (θ η : Fin n → ℝ) (hθ : θ ∈ cell P a) (hη : η ∈ cell P a) :
    ∀ t : ℝ, expAngles (t • (θ - η)) ∈ stabilizerSubgroup P := by
  intro t x y hxy
  rw [phase_expAngles, phase_expAngles, angle_smul, angle_smul]
  have he : angle (θ - η) x = angle (θ - η) y := by
    rw [angle_sub, angle_sub]
    have ht := hθ x y hxy
    have hu := hη x y hxy
    linarith
  rw [he]

theorem same_cell_relativeAction (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (x₀ y₀ : SS.BitString n) (hp₀ : P.kernel x₀ y₀ ≠ 0)
    (a : Labels n) (θ η : Fin n → ℝ) (hθ : θ ∈ cell P a) (hη : η ∈ cell P a) :
    relativeAction P x₀ (expAngles θ) = relativeAction P x₀ (expAngles η) := by
  have hH := hamiltonian_on_code P (θ - η) μ hμ (same_cell_direction P a θ η hθ hη)
  have he₀ := congrFun (congrFun hH x₀) y₀
  simp only [hamiltonian, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at he₀
  have hz := mul_right_cancel₀ hp₀ he₀
  ext x y
  simp only [relativeAction, Matrix.smul_apply, smul_eq_mul, operator, Matrix.diagonal_mul]
  by_cases hxy : P.kernel x y = 0
  · simp [hxy]
  have he := congrFun (congrFun hH x) y
  simp only [hamiltonian, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at he
  have hx := mul_right_cancel₀ hxy he
  have hangle : angle (θ - η) x = angle (θ - η) x₀ :=
    Complex.ofReal_injective (hx.trans hz.symm)
  rw [angle_sub, angle_sub] at hangle
  have hphase : phase (expAngles θ) x / phase (expAngles θ) x₀ =
      phase (expAngles η) x / phase (expAngles η) x₀ := by
    rw [phase_expAngles, phase_expAngles, phase_expAngles, phase_expAngles,
      ← Circle.exp_sub, ← Circle.exp_sub]
    congr 1
    linear_combination (2 * Real.pi) * hangle
  have hc := congrArg (fun z : Circle => (z : ℂ)) hphase
  simp only [div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv] at hc
  calc
    _ = ((phase (expAngles θ) x : ℂ) * (phase (expAngles θ) x₀ : ℂ)⁻¹) * P.kernel x y := by ring
    _ = ((phase (expAngles η) x : ℂ) * (phase (expAngles η) x₀ : ℂ)⁻¹) * P.kernel x y := by rw [hc]
    _ = _ := by ring

theorem finite_relativeAction_range (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (x₀ y₀ : SS.BitString n) (hp₀ : P.kernel x₀ y₀ ≠ 0) :
    (Set.range (fun u : stabilizerSubgroup P => relativeAction P x₀ u.val)).Finite := by
  classical
  choose a θ hθ using cells_cover P
  apply MainTheory.FiniteImageComponents.finite_range_of_label _ a
  intro u v huv
  have hv : (θ v).val ∈ cell P (a u) := by simpa only [huv] using (θ v).property
  have he := same_cell_relativeAction P μ hμ x₀ y₀ hp₀ (a u)
    (θ u).val (θ v).val (θ u).property hv
  have huval := congrArg Subtype.val (hθ u)
  have hvval := congrArg Subtype.val (hθ v)
  change expAngles (θ u).val = u.val at huval
  change expAngles (θ v).val = v.val at hvval
  simpa only [huval, hvval] using he

end

end MainTheory.PhysicalRelativeAction
