import MainTheory.PhysicalTorusCells

namespace MainTheory.PhysicalTorusCells

open scoped BigOperators
open MainTheory.ClassificationLevels

noncomputable section

variable {n : ℕ}

theorem exists_bounded_angles (u : Torus n) :
    ∃ θ : Fin n → ℝ, (∀ j, -1 ≤ θ j ∧ θ j ≤ 1) ∧ expAngles θ = u := by
  let θ : Fin n → ℝ := fun j => Complex.arg (u j) / (2 * Real.pi)
  refine ⟨θ, ?_, ?_⟩
  · intro j
    have hlo := Complex.neg_pi_lt_arg (u j : ℂ)
    have hhi := Complex.arg_le_pi (u j : ℂ)
    have hp : 0 < 2 * Real.pi := by positivity
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith [Real.pi_pos]
    · apply (div_le_iff₀ hp).2
      nlinarith [Real.pi_pos]
  · funext j
    change Circle.exp (2 * Real.pi * (Complex.arg (u j) / (2 * Real.pi))) = u j
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), Circle.exp_arg]

theorem angle_difference_bound (θ : Fin n → ℝ)
    (hθ : ∀ j, -1 ≤ θ j ∧ θ j ≤ 1) (x y : SS.BitString n) :
    |angle θ x - angle θ y| ≤ (n : ℝ) := by
  rw [angle, angle, ← Finset.sum_sub_distrib]
  calc
    |∑ j, ((if x j then θ j else 0) - (if y j then θ j else 0))| ≤
        ∑ j, |(if x j then θ j else 0) - (if y j then θ j else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hj := hθ j
      cases x j <;> cases y j <;> simp only [Bool.false_eq_true,
        ↓reduceIte, sub_zero, zero_sub, sub_self, abs_zero, abs_neg]
      all_goals first | exact zero_le_one | exact abs_le.mpr hj
    _ = (n : ℝ) := by simp

theorem exists_cell_label (P : CodeProjector n) (u : Stabilizer P)
    (θ : Fin n → ℝ) (hθ : ∀ j, -1 ≤ θ j ∧ θ j ≤ 1)
    (hexp : expAngles θ = u.val) : ∃ h : Labels n, θ ∈ cell P h := by
  classical
  have labels : ∀ x y : SS.BitString n, ∃ a : Fin (2 * n + 1),
      P.kernel x y ≠ 0 → angle θ x - angle θ y = a.val - (n : ℝ) := by
    intro x y
    by_cases hxy : P.kernel x y = 0
    · exact ⟨⟨n, by omega⟩, fun hn => (hn hxy).elim⟩
    have he := u.property x y hxy
    rw [← hexp, phase_expAngles, phase_expAngles, Circle.exp_eq_exp] at he
    obtain ⟨k, hk⟩ := he
    have hdiff : angle θ x - angle θ y = (k : ℝ) := by
      have hpi := Real.pi_pos
      nlinarith
    have hb := angle_difference_bound θ hθ x y
    rw [hdiff] at hb
    have hlo : -(n : ℤ) ≤ k := by exact_mod_cast (abs_le.mp hb).1
    have hhi : k ≤ (n : ℤ) := by exact_mod_cast (abs_le.mp hb).2
    have hnonneg : 0 ≤ k + (n : ℤ) := by omega
    refine ⟨⟨(k + (n : ℤ)).toNat, ?_⟩, fun _ => ?_⟩
    · omega
    · rw [hdiff]
      have hc : ((k + (n : ℤ)).toNat : ℝ) = (k : ℝ) + (n : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnonneg
      rw [hc]
      ring
  choose h hh using labels
  exact ⟨h, hh⟩

/-- Every physical stabilizer element belongs to a continuous image of one
of finitely many affine angle cells. -/
theorem cells_cover (P : CodeProjector n) (u : Stabilizer P) :
    ∃ h θ, cellMap P h θ = u := by
  obtain ⟨θ, hθ, he⟩ := exists_bounded_angles u.val
  obtain ⟨h, hh⟩ := exists_cell_label P u θ hθ he
  exact ⟨h, ⟨θ, hh⟩, Subtype.ext he⟩

/-- The physical diagonal stabilizer of any finite-dimensional qubit
projector has finitely many connected components. No code distance is needed. -/
theorem finite_connectedComponents (P : CodeProjector n) :
    Finite (ConnectedComponents (Stabilizer P)) :=
  MainTheory.FiniteConnectedCover.finite_components_of_convex_images
    (cell P) (cellMap P) (cell_convex P) (cellMap_continuous P) (cells_cover P)

end

end MainTheory.PhysicalTorusCells
