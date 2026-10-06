import MainTheory.Orbit3CategoryBridge
import MainTheory.PauliCategoryAverages

/-! # Actual orbit-3 category masses and the Fourier positivity rows

No permutation symmetry or scalar realization hypothesis is imposed on the
encoder. The equality rows, including the shifted-category diagonal relation,
are a subsequent step in the full scalar converse.
-/

namespace MainTheory.Orbit3ScalarCategoryRealization

open MainTheory.CubeCompletionTransport MainTheory.DirectoryEnumeratorImages
open MainTheory.OrderTwoScalarBridge MainTheory.OrderTwoLabelScalars
open MainTheory.Orbit3CategoryBridge MainTheory.PhysicalPauliCategories
open MainTheory.PauliCategoryAverages MainTheory.RationalLinearCertificate
open SixQubit.Generated SixQubit.Generated.Orbit3CategoryRows
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev Encoder := Completion (angleFibers SixQubit.OpenLOrbit3.angle)

def y (W : Encoder) (c : Fin 24) : ℝ := mass W.states (Orbit3Scalar.categories c)

theorem y_nonneg (W : Encoder) (c : Fin 24) : 0 ≤ y W c := mass_nonneg _ _

theorem categories_injective : Function.Injective Orbit3Scalar.categories := by
  intro c d h
  apply columnCode_injective
  apply errorCategory_injective
  rw [(column_category c).1, (column_category d).1]
  exact h

theorem activeMask_eq : activeMask = orbit3Mask := by
  funext i
  fin_cases i <;> decide +kernel

theorem a_zero_outside_columns (W : Encoder) (P : SS.PauliString 6)
    (habsent : ∀ c, columnCode c ≠ categoryIndex P) : a W.states P = 0 := by
  have ho := absent_column_odd (categoryIndex P) habsent
  rw [categoryIndex_correct] at ho
  apply orbit3_a_odd_zero W P
  rw [← activeMask_eq, category_parity, ho]
  rfl

theorem physical_fourier_at_column (P : SS.PauliString 6) (e : Fin 42) (c : Fin 24)
    (hc : categoryIndex P = columnCode c) :
    pairingCoefficient P (errorCategory e) / (32 * (errorSize e : ℝ)) =
      (Orbit3CategoryRows.fourier e c : ℝ) := by
  have ht := congrArg errorTail hc
  rw [categoryIndex_tail, (column_category c).2.1] at ht
  have hs := congrArg errorSpectator hc
  rw [categoryIndex_spectator, (column_category c).2.2] at hs
  have hz : word P 0 = 0 ↔ columnSpectator c = 0 := by
    rw [← hs]
    unfold spectatorIndex
    by_cases h : word P 0 = 0 <;> simp [h]
  have hp : pairingCoefficient P (errorCategory e) =
      (spectatorFactor (word P 0) (errorSpectator e).val : ℝ) *
        (tailCoefficients (columnTail c) (errorTail e) : ℝ) := by
    unfold pairingCoefficient
    rw [← physical_category_pairing_sum]
    have h := physical_pairing_sum P (errorSpectator e) (errorTail e)
    rw [ht] at h
    exact h
  rw [hp, spectatorFactor_formula]
  unfold Orbit3CategoryRows.fourier
  by_cases he : errorSpectator e = 0 <;> by_cases hcs : columnSpectator c = 0 <;>
    simp [he, hcs, hz]

theorem actual_evaluation (W : Encoder) (r : Fin 24 → ℚ)
    (f : SS.PauliString 6 → ℝ)
    (hf : ∀ P c, categoryIndex P = columnCode c → f P = (r c : ℝ)) :
    evaluate r (y W) = ∑ P : SS.PauliString 6, f P * a W.states P := by
  unfold evaluate y
  rw [sum_by_columns]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hc : ∃ c, categoryIndex P = columnCode c
  · obtain ⟨c, hc⟩ := hc
    have hcat := (category_column_iff P c).mpr hc
    rw [hcat, coefficient_at_column _ categories_injective, hf P c hc]
  · have ha : a W.states P = 0 := a_zero_outside_columns W P (by
      intro c h
      exact hc ⟨c, h.symm⟩)
    rw [ha]
    simp

theorem b_average_eq (W : Encoder) (e : Fin 42) :
    evaluate (Orbit3CategoryRows.fourier e) (y W) =
      average (b W.states) (errorCategory e) (errorSize e) := by
  rw [actual_evaluation W (Orbit3CategoryRows.fourier e)
    (fun P => pairingCoefficient P (errorCategory e) / (32 * (errorSize e : ℝ)))
      (fun P c hc => physical_fourier_at_column P e c hc), b_average]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem shadow_average_eq (W : Encoder) (e : Fin 42) :
    evaluate (spin e) (y W) =
      average (shadow W.states) (errorCategory e) (errorSize e) := by
  have hf (P : SS.PauliString 6) (c : Fin 24) (hc : categoryIndex P = columnCode c) :
      pairingCoefficient P (errorCategory e) / (32 * (errorSize e : ℝ)) *
        (-1 : ℝ) ^ P.wt = (spin e c : ℝ) := by
    rw [physical_fourier_at_column P e c hc, category_weight,
      (category_column_iff P c).mpr hc]
    simp [spin]
  rw [actual_evaluation W (spin e)
    (fun P => pairingCoefficient P (errorCategory e) / (32 * (errorSize e : ℝ)) *
      (-1 : ℝ) ^ P.wt) hf, shadow_average]
  simp_rw [div_mul_eq_mul_div, mul_assoc]
  rw [Finset.sum_div]

theorem positive_rows (W : Encoder) (i : Fin 84) :
    0 ≤ evaluate (Orbit3Scalar.positive i) (y W) := by
  have hs : 0 ≤ (errorSize (positiveError i) : ℝ) := Nat.cast_nonneg _
  by_cases hp : i.val % 2 = 0
  · have hr : Orbit3Scalar.positive i = Orbit3CategoryRows.fourier (positiveError i) := by
      funext c
      rw [positive_formula, if_pos hp]
    rw [hr, b_average_eq]
    exact average_nonneg _ _ _ (b_nonneg W.states) hs
  · have hr : Orbit3Scalar.positive i = spin (positiveError i) := by
      funext c
      rw [positive_formula, if_neg hp]
    rw [hr, shadow_average_eq]
    exact average_nonneg _ _ _ (shadow_nonneg W.states) hs

end
end MainTheory.Orbit3ScalarCategoryRealization
