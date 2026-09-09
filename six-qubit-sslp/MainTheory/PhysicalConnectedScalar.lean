import MainTheory.PhysicalRelativeAction

namespace MainTheory.PhysicalRelativeAction

open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.DiagonalInfinitesimal

noncomputable section

variable {n : ℕ}

theorem phase_continuous (x : SS.BitString n) : Continuous (fun u : Torus n => phase u x) := by
  unfold phase
  apply continuous_finset_prod
  intro j _
  cases x j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact continuous_const
  · exact continuous_apply j

theorem operator_continuous : Continuous (operator (n := n)) := by
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro x
  exact (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).comp (phase_continuous x)

theorem relativeAction_continuous (P : CodeProjector n) (x₀ : SS.BitString n) :
    Continuous (relativeAction P x₀) := by
  have hc := (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).comp
    (phase_continuous x₀).inv
  exact hc.smul (operator_continuous.mul continuous_const)

theorem relativeAction_one (P : CodeProjector n) (x₀ : SS.BitString n) :
    relativeAction P x₀ (1 : Torus n) = P.kernel := by
  simp [relativeAction, operator, phase]

/-- Every element of the entire unit connected component acts as a physical
scalar on P. This is stronger than checking individual one-parameter curves. -/
theorem connected_component_scalar (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (x₀ y₀ : SS.BitString n) (hp₀ : P.kernel x₀ y₀ ≠ 0)
    (u : stabilizerSubgroup P) (hu : u ∈ connectedComponent (1 : stabilizerSubgroup P)) :
    operator u.val * P.kernel = (phase u.val x₀ : ℂ) • P.kernel := by
  have he := MainTheory.FiniteImageComponents.constant_on_component
    (fun v : stabilizerSubgroup P => relativeAction P x₀ v.val)
    ((relativeAction_continuous P x₀).comp continuous_subtype_val)
    (finite_relativeAction_range P μ hμ x₀ y₀ hp₀) hu
  change relativeAction P x₀ u.val = relativeAction P x₀ 1 at he
  rw [relativeAction_one] at he
  have hs := congrArg (fun A : OperatorKernel n => (phase u.val x₀ : ℂ) • A) he
  simpa [relativeAction, smul_smul, Circle.coe_ne_zero] using hs

theorem connected_component_scalar_exists (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (u : stabilizerSubgroup P) (hu : u ∈ connectedComponent (1 : stabilizerSubgroup P)) :
    ∃ z : Circle, operator u.val * P.kernel = (z : ℂ) • P.kernel := by
  by_cases hzero : P.kernel = 0
  · exact ⟨1, by simp [hzero]⟩
  have hentry : ∃ x y, P.kernel x y ≠ 0 := by
    by_contra! hall
    apply hzero
    ext x y
    exact hall x y
  obtain ⟨x, y, hxy⟩ := hentry
  exact ⟨phase u.val x, connected_component_scalar P μ hμ x y hxy u hu⟩

theorem exact_code_connected_component_scalar {K d : ℕ}
    (C : MainTheory.CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (u : stabilizerSubgroup (CodeProjector.ofFrame C.frame))
    (hu : u ∈ connectedComponent (1 : stabilizerSubgroup (CodeProjector.ofFrame C.frame))) :
    ∃ z : Circle, operator u.val * (CodeProjector.ofFrame C.frame).kernel =
      (z : ℂ) • (CodeProjector.ofFrame C.frame).kernel := by
  obtain ⟨μ, hμ⟩ := numberKernel_compression C hd
  exact connected_component_scalar_exists _ μ hμ u hu

end

end MainTheory.PhysicalRelativeAction
