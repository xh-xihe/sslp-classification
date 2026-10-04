import MainTheory.Orbit3PauliZeros

/-! # The actual weight-three target of the orbit-3 cubic certificate

All other weight-three traces vanish. On the 120-label target category the
expectations of the actual logical superposition equal the projector traces.
-/

namespace MainTheory.Orbit3Target

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.PhysicalPauliCategories
open MainTheory.Orbit3CategoryBridge MainTheory.OrderTwoScalarBridge
open MainTheory.OrderTwoLabelScalars MainTheory.PauliCategoryAverages
open SixQubit.ParityPauliScalars SixQubit.ParityLogicalState SS.MacWilliams
open SixQubit.Generated

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def targetCategory : ℕ × ℕ × ℕ := (1, 0, 2)

theorem weight_three_categories : ∀ e : Fin 42,
    (Orbit3CategoryRows.errorCategory e).1 + (Orbit3CategoryRows.errorCategory e).2.1 +
        (Orbit3CategoryRows.errorCategory e).2.2 = 3 →
    (Orbit3CategoryRows.errorCategory e).2.2 % 2 = 1 ∨
      Orbit3CategoryRows.errorCategory e = targetCategory ∨
      ∃ c : Fin 5, Orbit3CategoryRows.errorCategory e =
        Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c) := by
  decide +kernel

theorem outside_target_trace_zero (W : Encoder) (P : SS.PauliString 6)
    (hwt : P.wt = 3) (hc : category P ≠ targetCategory) : trProj W.states P = 0 := by
  have hw : (Orbit3CategoryRows.errorCategory (categoryIndex P)).1 +
      (Orbit3CategoryRows.errorCategory (categoryIndex P)).2.1 +
      (Orbit3CategoryRows.errorCategory (categoryIndex P)).2.2 = 3 := by
    rw [categoryIndex_correct, ← category_weight, hwt]
  rcases weight_three_categories (categoryIndex P) hw with hodd | ht | ⟨c, hz⟩
  · rw [categoryIndex_correct] at hodd
    apply odd_trace_zero (orbit3_parity W) P
    rw [chi_bdot, ← activeMask_eq, category_parity, hodd]
    rfl
  · exact (hc ((categoryIndex_correct P).symm.trans ht)).elim
  · exact MainTheory.Orbit3QuadraticZeros.zero_category_trace W c P
      ((categoryIndex_correct P).symm.trans hz)

theorem target_weight (P : SS.PauliString 6) (hc : category P = targetCategory) : P.wt = 3 := by
  rw [category_weight, hc]
  rfl

theorem target_expectation (W : Encoder) (P : SS.PauliString 6)
    (hc : category P = targetCategory) :
    SS.innerC (superposition W.states) (SS.pauliAct P (superposition W.states)) =
      trProj W.states P := by
  rw [innerC_eq_mel, trProj_eq, superposition_commuting W.states (orbit3_parity W) P]
  rw [chi_bdot, ← activeMask_eq, category_parity, hc]
  rfl

theorem target_sum_eq_Aco (W : Encoder) :
    (∑ P : SS.PauliString 6, if category P = targetCategory then
      Complex.normSq (SS.innerC (superposition W.states)
        (SS.pauliAct P (superposition W.states))) else 0) = Aco W.states 3 := by
  unfold Aco
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hc : category P = targetCategory
  · rw [if_pos hc, if_pos (target_weight P hc), target_expectation W P hc]
  · rw [if_neg hc]
    by_cases hw : P.wt = 3
    · rw [if_pos hw, outside_target_trace_zero W P hw hc, Complex.normSq_zero]
    · rw [if_neg hw]

theorem target_mass_eq_A3 (W : Encoder) : mass W.states targetCategory = Aco W.states 3 / 4 := by
  unfold mass a
  have hh (P : SS.PauliString 6) :
      (if category P = targetCategory then Complex.normSq (trProj W.states P) / 4 else 0) =
      (if category P = targetCategory then
        Complex.normSq (SS.innerC (superposition W.states)
          (SS.pauliAct P (superposition W.states))) else 0) / 4 := by
    by_cases hc : category P = targetCategory
    · rw [if_pos hc, if_pos hc, target_expectation W P hc]
    · simp only [hc, if_false, zero_div]
  simp_rw [hh]
  rw [← Finset.sum_div, target_sum_eq_Aco]

end
end MainTheory.Orbit3Target
