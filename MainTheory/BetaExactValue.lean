import MainTheory.BetaExists

namespace MainTheory.BetaExactValue

open MainTheory.BinaryBeta MainTheory.BetaExists MainTheory.SharpClearing

theorem inverseDenominator_of_det_zero {s : ℕ} (C : Matrix (Fin s) (Fin s) ℤ)
    (h : C.det = 0) : inverseDenominator C = 1 := by
  have hr : (ratMatrix C).det = 0 := by
    calc
      (ratMatrix C).det = (C.det : ℚ) := ((Int.castRingHom ℚ).map_det C).symm
      _ = 0 := by rw [h]; rfl
  have hi : (ratMatrix C)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hr])
  apply Nat.dvd_one.mp
  apply inverseDenominator_dvd_of_universallyClears C 1 (by decide)
  intro v
  refine ⟨0, ?_⟩
  intro i
  simp [hi]

theorem betaOf_le_of_bound {N B : ℕ} (hB : 1 ≤ B) (h : BetaBound N B) :
    betaOf N ≤ B := by
  apply Finset.sup_le
  intro s hs
  apply Finset.sup_le
  intro M _
  by_cases hz : s = 0
  · subst s
    have he : inverseDenominator (ofBool M) = 1 := by
      simp [inverseDenominator, MainTheory.Denominator.lcmDen]
    exact he ▸ hB
  · by_cases hd : (ofBool M).det = 0
    · rw [inverseDenominator_of_det_zero _ hd]
      exact hB
    · exact h s (by omega) (by simpa using Finset.mem_range.mp hs)
        (ofBool M) (isZeroOne_ofBool M) hd

theorem betaOf_eq_of_exact {N B : ℕ} (h : BetaExact N B) : betaOf N = B := by
  obtain ⟨s, hs, hsN, C, hC, _, he⟩ := h.attained
  have hpos : 1 ≤ B := by simpa [he] using inverseDenominator_pos C
  apply Nat.le_antisymm (betaOf_le_of_bound hpos h.upper)
  rw [← he]
  exact (le_betaAt hC).trans (Finset.le_sup (f := betaAt)
    (Finset.mem_range.mpr (by omega)))

end MainTheory.BetaExactValue
