import MainTheory.OrderTwoLabelScalars
import MainTheory.PhysicalPauliCategories

/-! # Category masses and averages of actual physical Pauli coefficients

The weights below are computed from actual complex encoder columns. Averaging
the individual Fourier identities requires no symmetry of the encoder.
-/

namespace MainTheory.PauliCategoryAverages

open MainTheory.OrderTwoLabelScalars MainTheory.PhysicalPauliCategories
open MainTheory.PauliCategoryFourier SS.ShadowTwisted
open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Category := ℕ × ℕ × ℕ

def mass (psi : Fin 2 → SS.State 6 ℂ) (c : Category) : ℝ :=
  ∑ P : SS.PauliString 6, if category P = c then a psi P else 0

def average (f : SS.PauliString 6 → ℝ) (c : Category) (size : ℝ) : ℝ :=
  (∑ E : SS.PauliString 6, if category E = c then f E else 0) / size

theorem mass_nonneg (psi : Fin 2 → SS.State 6 ℂ) (c : Category) : 0 ≤ mass psi c := by
  apply Finset.sum_nonneg
  intro P _
  split_ifs
  · exact a_nonneg _ _
  · exact le_refl _

theorem individual_zero_of_mass_zero (psi : Fin 2 → SS.State 6 ℂ)
    (c : Category) (hmass : mass psi c = 0) (P : SS.PauliString 6)
    (hc : category P = c) : a psi P = 0 := by
  have h : (if category P = c then a psi P else 0) ≤ mass psi c := by
    exact Finset.single_le_sum (f := fun Q => if category Q = c then a psi Q else 0)
      (fun Q _ => by
      dsimp only
      split_ifs
      · exact a_nonneg _ _
      · exact le_refl _) (Finset.mem_univ P)
  rw [if_pos hc, hmass] at h
  exact le_antisymm h (a_nonneg _ _)

def pairingCoefficient (P : SS.PauliString 6) (c : Category) : ℝ :=
  (spectatorFactor (word P 0) c.1 : ℝ) *
    ((∏ i : Fin 5, factor (word P i.succ)) c.2 : ℝ)

theorem sum_swap (w : SS.PauliString 6 → ℝ) (c : Category) :
    (∑ E : SS.PauliString 6,
      if category E = c then ∑ P : SS.PauliString 6, pairSign E P * w P else 0) =
      ∑ P : SS.PauliString 6, pairingCoefficient P c * w P := by
  have hrow (E : SS.PauliString 6) :
      (if category E = c then ∑ P : SS.PauliString 6, pairSign E P * w P else 0) =
        ∑ P : SS.PauliString 6, (if category E = c then pairSign E P else 0) * w P := by
    by_cases h : category E = c <;> simp [h]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, physical_category_pairing_sum]
  rfl

theorem b_average (psi : Fin 2 → SS.State 6 ℂ) (c : Category) (size : ℝ) :
    average (b psi) c size =
      (∑ P : SS.PauliString 6, pairingCoefficient P c * a psi P) / (32 * size) := by
  unfold average
  simp_rw [b_fourier]
  have hrow (E : SS.PauliString 6) :
      (if category E = c then
        (∑ P : SS.PauliString 6, pairSign E P * a psi P) / 32 else 0) =
      (if category E = c then
        ∑ P : SS.PauliString 6, pairSign E P * a psi P else 0) / 32 := by
    by_cases h : category E = c <;> simp [h]
  simp_rw [hrow]
  rw [← Finset.sum_div, sum_swap, div_div]

theorem shadow_average (psi : Fin 2 → SS.State 6 ℂ) (c : Category) (size : ℝ) :
    average (shadow psi) c size =
      (∑ P : SS.PauliString 6,
        pairingCoefficient P c * ((-1 : ℝ) ^ P.wt * a psi P)) / (32 * size) := by
  unfold average shadow
  have hrow (E : SS.PauliString 6) :
      (if category E = c then
        (∑ P : SS.PauliString 6, (-1 : ℝ) ^ P.wt * pairSign E P * a psi P) / 32 else 0) =
      (if category E = c then
        ∑ P : SS.PauliString 6, pairSign E P * ((-1 : ℝ) ^ P.wt * a psi P)
        else 0) / 32 := by
    by_cases h : category E = c
    · simp only [if_pos h]
      congr 1
      apply Finset.sum_congr rfl
      intro P _
      ring
    · simp [h]
  simp_rw [hrow]
  rw [← Finset.sum_div, sum_swap, div_div]

theorem average_nonneg (f : SS.PauliString 6 → ℝ) (c : Category) (size : ℝ)
    (hf : ∀ E, 0 ≤ f E) (hs : 0 ≤ size) : 0 ≤ average f c size := by
  apply div_nonneg _ hs
  apply Finset.sum_nonneg
  intro E _
  split_ifs
  · exact hf E
  · exact le_refl _

theorem sum_by_columns {C : Type*} [Fintype C] [DecidableEq C]
    (label : C → Category) (r : C → ℝ) (psi : Fin 2 → SS.State 6 ℂ) :
    (∑ c, r c * mass psi (label c)) =
      ∑ P : SS.PauliString 6,
        (∑ c, if category P = label c then r c else 0) * a psi P := by
  unfold mass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : category P = label c <;> simp [h]

theorem coefficient_at_column {C : Type*} [Fintype C] [DecidableEq C]
    (label : C → Category) (hi : Function.Injective label) (r : C → ℝ) (c : C) :
    (∑ d, if label c = label d then r d else 0) = r c := by
  simp [hi.eq_iff]

end
end MainTheory.PauliCategoryAverages
