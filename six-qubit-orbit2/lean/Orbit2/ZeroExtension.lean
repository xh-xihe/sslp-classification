import Orbit2.Certificate

namespace Orbit2
open scoped BigOperators

/-- Reindex a finite sum through a checked embedding of its nonzero coordinates. -/
theorem sum_active {n d : ℕ} (active : Fin n → Bool) (pos : Fin n → Fin d)
    (embed : Fin d → Fin n) (hpos : ∀ k, pos (embed k) = k)
    (hactive : ∀ k, active (embed k))
    (hembed : ∀ i, active i → embed (pos i) = i) (f : Fin n → ℝ) :
    (∑ i, if active i then f i else 0) = ∑ k, f (embed k) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => pos i)
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hp
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rw [← hembed i hi', ← hembed j hj', hp]
  · intro k _
    exact ⟨embed k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive k⟩, hpos k⟩
  · intro i hi
    rw [hembed i (Finset.mem_filter.mp hi).2]

theorem complexEnergy_expansion {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℂ) :
    complexEnergy M z = ∑ i, ∑ j, (M i j : ℝ) *
      ((z i).re*(z j).re + (z i).im*(z j).im) := by
  simp only [complexEnergy, dotProduct, Matrix.mulVec, realMatrix, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Zero coordinates make no contribution; the remaining Gram energy is exactly
twice the certified energy, over every complex vector. -/
theorem complexEnergy_zero_extension {n d : ℕ}
    (C : Matrix (Fin n) (Fin n) ℚ) (M : Matrix (Fin d) (Fin d) ℚ)
    (active : Fin n → Bool) (pos : Fin n → Fin d) (embed : Fin d → Fin n)
    (hpos : ∀ k, pos (embed k) = k) (hactive : ∀ k, active (embed k))
    (hembed : ∀ i, active i → embed (pos i) = i)
    (hC : ∀ i j, C i j = if active i ∧ active j then 2*M (pos i) (pos j) else 0)
    (z : Fin n → ℂ) : complexEnergy C z = 2 * complexEnergy M (fun k => z (embed k)) := by
  rw [complexEnergy_expansion, complexEnergy_expansion]
  simp_rw [hC]
  have hs : (∑ i, ∑ j, ((if active i ∧ active j then 2*M (pos i) (pos j) else 0 : ℚ) : ℝ) *
      ((z i).re*(z j).re + (z i).im*(z j).im)) =
    ∑ k, ∑ l, (2*M k l : ℝ) *
      ((z (embed k)).re*(z (embed l)).re + (z (embed k)).im*(z (embed l)).im) := by
    calc
      _ = ∑ i, if active i then
          ∑ j, if active j then (2*(M (pos i) (pos j) : ℝ)) *
            ((z i).re*(z j).re + (z i).im*(z j).im) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : active i <;> simp [hi, apply_ite, ite_mul]
      _ = _ := by
        rw [sum_active active pos embed hpos hactive hembed]
        apply Finset.sum_congr rfl
        intro k _
        rw [sum_active active pos embed hpos hactive hembed]
        simp [hpos]
  rw [hs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  push_cast
  ring

end Orbit2
