import MainTheory.PhysicalTorusFiniteComponents
import MainTheory.FiniteComponentQuotient

namespace MainTheory.PhysicalTorusCells

open scoped BigOperators
open MainTheory.ClassificationLevels

noncomputable section

variable {n : ℕ}

theorem phase_mul (u v : Torus n) (x : SS.BitString n) :
    phase (u * v) x = phase u x * phase v x := by
  simp only [phase, ← Finset.prod_mul_distrib, Pi.mul_apply]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp

theorem phase_inv (u : Torus n) (x : SS.BitString n) :
    phase u⁻¹ x = (phase u x)⁻¹ := by
  simp only [phase, Pi.inv_apply, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp

def stabilizerSubgroup (P : CodeProjector n) : Subgroup (Torus n) where
  carrier := {u | ∀ x y, P.kernel x y ≠ 0 → phase u x = phase u y}
  one_mem' := by simp [phase]
  mul_mem' hu hv := by
    intro x y hxy
    rw [phase_mul, phase_mul, hu x y hxy, hv x y hxy]
  inv_mem' hu := by
    intro x y hxy
    rw [phase_inv, phase_inv, hu x y hxy]

/-- The physical diagonal matrix, with one local phase on each |1> state. -/
def operator (u : Torus n) : OperatorKernel n :=
  Matrix.diagonal fun x => (phase u x : ℂ)

theorem operator_unitary (u : Torus n) :
    star (operator u) * operator u = 1 ∧ operator u * star (operator u) = 1 := by
  have hstar : star (operator u) = Matrix.diagonal (fun x => ((phase u x)⁻¹ : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simpa only [operator, Matrix.star_apply, Matrix.diagonal_apply_eq, Complex.star_def]
        using (Circle.coe_inv_eq_conj (phase u x)).symm
    · simp [operator, Matrix.star_apply, Matrix.diagonal, hxy, Ne.symm hxy]
  rw [hstar, operator, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  constructor <;> congr 1 <;> funext x
  · simpa only [Circle.coe_mul, Circle.coe_inv, Circle.coe_one] using
      congrArg (fun z : Circle => (z : ℂ)) (inv_mul_cancel (phase u x))
  · simpa only [Circle.coe_mul, Circle.coe_inv, Circle.coe_one] using
      congrArg (fun z : Circle => (z : ℂ)) (mul_inv_cancel (phase u x))

theorem mem_stabilizer_iff_commute (P : CodeProjector n) (u : Torus n) :
    u ∈ stabilizerSubgroup P ↔ operator u * P.kernel = P.kernel * operator u := by
  constructor
  · intro hu
    ext x y
    simp only [operator, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : P.kernel x y = 0
    · simp [hxy]
    · rw [hu x y hxy]
      ring
  · intro hu x y hxy
    have h := congrFun (congrFun hu x) y
    simp only [operator, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    apply Circle.coe_injective
    apply mul_right_cancel₀ hxy
    simpa only [mul_comm] using h

/-- The cell-defined group is exactly the physical projector stabilizer
appearing in the manuscript, with its inherited torus topology. -/
theorem mem_stabilizer_iff_conjugate (P : CodeProjector n) (u : Torus n) :
    u ∈ stabilizerSubgroup P ↔ operator u * P.kernel * star (operator u) = P.kernel := by
  rw [mem_stabilizer_iff_commute]
  constructor
  · intro h
    rw [h, Matrix.mul_assoc, (operator_unitary u).2, Matrix.mul_one]
  · intro h
    calc operator u * P.kernel = operator u * P.kernel * (star (operator u) * operator u) := by
            rw [(operator_unitary u).1, Matrix.mul_one]
      _ = P.kernel * operator u := by rw [← Matrix.mul_assoc, h]

/-- The actual finite component-group conclusion T_P / T_P^0. -/
theorem finite_physical_component_group (P : CodeProjector n) :
    Finite ((stabilizerSubgroup P) ⧸ Subgroup.connectedComponentOfOne (stabilizerSubgroup P)) := by
  haveI : Finite (ConnectedComponents (stabilizerSubgroup P)) := finite_connectedComponents P
  exact MainTheory.FiniteComponentQuotient.finite_component_quotient

theorem conjugation_continuous (P : CodeProjector n) :
    Continuous (fun u : Torus n => operator u * P.kernel * star (operator u)) := by
  have hd : Continuous (operator (n := n)) := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    by_cases hxy : x = y
    · subst y
      simp only [operator, Matrix.diagonal_apply_eq, phase]
      apply (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).comp
      apply continuous_finset_prod
      intro j _
      cases x j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact continuous_const
      · exact continuous_apply j
    · simpa only [operator, Matrix.diagonal_apply_ne _ hxy] using
        (continuous_const : Continuous (fun _ : Torus n => (0 : ℂ)))
  exact (hd.mul continuous_const).mul hd.star

end

end MainTheory.PhysicalTorusCells
