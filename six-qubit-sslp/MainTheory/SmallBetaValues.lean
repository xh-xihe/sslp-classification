import MainTheory.BetaExactValue
import MainTheory.BinaryBetaTinyLower
import MainTheory.Generated.BinaryBetaSmall.Size4.Certificate
import MainTheory.Generated.BinaryBetaFiveFast.Certificate
import MainTheory.Generated.BinaryBetaSixKernel.Certificate
import MainTheory.BetaAtPivotRank

namespace MainTheory.SmallBetaValues

open MainTheory.BetaExists MainTheory.BetaExactValue MainTheory.CoarseFilter

theorem betaOf_zero : betaOf 0 = 1 := by
  apply Nat.le_antisymm
  · exact betaOf_le_of_bound (by decide) (by intro s hs hs0; omega)
  · exact betaOf_pos 0

theorem betaOf_one : betaOf 1 = 1 :=
  betaOf_eq_of_exact MainTheory.BinaryBetaTinyLower.betaExact_one
theorem betaOf_two : betaOf 2 = 1 :=
  betaOf_eq_of_exact MainTheory.BinaryBetaTinyLower.betaExact_two
theorem betaOf_three : betaOf 3 = 2 :=
  betaOf_eq_of_exact MainTheory.BinaryBetaTinyLower.betaExact_three
theorem betaOf_four : betaOf 4 = 3 :=
  betaOf_eq_of_exact MainTheory.Generated.BinaryBetaSmall.Size4.Certificate.betaExact
theorem betaOf_five : betaOf 5 = 5 :=
  betaOf_eq_of_exact MainTheory.Generated.BinaryBetaFiveFast.Certificate.betaExact
theorem betaOf_six : betaOf 6 = 9 :=
  betaOf_eq_of_exact MainTheory.Generated.BinaryBetaSixKernel.Certificate.betaExact

theorem small_values :
    ![betaOf 1, betaOf 2, betaOf 3, betaOf 4, betaOf 5, betaOf 6] =
      (![1, 1, 2, 3, 5, 9] : Fin 6 → ℕ) := by
  rw [betaOf_one, betaOf_two, betaOf_three, betaOf_four, betaOf_five, betaOf_six]

theorem betaOf_eq_threshold {r : ℕ} (hr : 1 ≤ r) (hr6 : r ≤ 6) :
    betaOf r = threshold r := by
  interval_cases r <;> simp [threshold, betaOf_one, betaOf_two, betaOf_three,
    betaOf_four, betaOf_five, betaOf_six]

theorem rMin_spec {q : ℕ} (hq : 2 ≤ q) (hq9 : q ≤ 9) :
    q ≤ betaOf (rMin q) ∧ ∀ r, q ≤ betaOf r → rMin q ≤ r := by
  have hpos : 1 ≤ rMin q := by interval_cases q <;> decide
  have hsmall : rMin q ≤ 6 := by interval_cases q <;> decide
  have hbound : q ≤ threshold (rMin q) := by interval_cases q <;> decide
  refine ⟨by rwa [betaOf_eq_threshold hpos hsmall], ?_⟩
  intro r hr
  by_cases h6 : r ≤ 6
  · by_cases h0 : r = 0
    · subst r
      rw [betaOf_zero] at hr
      omega
    · rw [betaOf_eq_threshold (by omega) h6] at hr
      exact rMin_le_of_le_threshold hq h6 hr
  · omega

theorem rMin_eq_minimum {q : ℕ} (hq : 2 ≤ q) (hq9 : q ≤ 9) :
    rMin q = Nat.find (show ∃ r, q ≤ betaOf r from ⟨rMin q, (rMin_spec hq hq9).1⟩) := by
  apply Nat.le_antisymm
  · exact (rMin_spec hq hq9).2 _ (Nat.find_spec
      (show ∃ r, q ≤ betaOf r from ⟨rMin q, (rMin_spec hq hq9).1⟩))
  · exact Nat.find_min' _ (rMin_spec hq hq9).1

end MainTheory.SmallBetaValues
