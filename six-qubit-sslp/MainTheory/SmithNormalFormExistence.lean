import MainTheory.SmithMeasure
import MainTheory.DeterminantalFactor

/-! # Existence of the full normalized integral Smith normal form

An actual positive diagonal reduction exists by the PID module theorem.
Among all such reductions choose one minimizing the sum of prefix products.
Every violation of the divisibility chain admits a genuine unimodular
two-coordinate gcd/lcm step that strictly decreases that natural measure.
Thus the minimum provides the full normalized Smith witness, without any
unproved normal-form or finite-table assumption.
-/

namespace MainTheory.SmithExistence

noncomputable section

variable {s : Type*} [Fintype s] [DecidableEq s] [LinearOrder s]
  [LocallyFiniteOrderBot s]

theorem exists_normalized_smith (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    Nonempty (SharpClearing.SmithWitness C) := by
  classical
  obtain ⟨d₀, hd₀, he₀⟩ := exists_positive_diagonal C hC
  have hex : ∃ m : ℕ, ∃ d : s → ℕ, (∀ i, 0 < d i) ∧
      IntegralEquivalent C (Matrix.diagonal (fun i => (d i : ℤ))) ∧ smithMeasure d = m :=
    ⟨smithMeasure d₀, d₀, hd₀, he₀, rfl⟩
  obtain ⟨d, hd, he, hm⟩ := Nat.find_spec hex
  have hchain : ∀ ⦃i j : s⦄, i ≤ j → d i ∣ d j := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      exact dvd_refl _
    · by_contra hnd
      have hlt : i < j := lt_of_le_of_ne hij heq
      have he' := he.trans (diagonal_gcd_update d hd i j heq)
      have hmin : Nat.find hex ≤ smithMeasure (gcdUpdate d i j) :=
        Nat.find_min' hex ⟨gcdUpdate d i j, gcdUpdate_pos d hd i j, he', rfl⟩
      have hdec := smithMeasure_gcd_lt d hd i j hlt hnd
      omega
  obtain ⟨U, V, hred⟩ := he
  exact ⟨{
    factor := d
    factor_pos := hd
    factor_chain := hchain
    U := U
    Uinv := ↑(U⁻¹)
    V := V
    Vinv := ↑(V⁻¹)
    U_mul_Uinv := U.val_inv
    Uinv_mul_U := U.inv_val
    V_mul_Vinv := V.val_inv
    Vinv_mul_V := V.inv_val
    reduction := hred
  }⟩

/-- The displayed final Smith entry has the paper's sharp inverse-denominator
meaning for the same matrix, not merely for an independently supplied witness. -/
theorem exists_smith_with_sharp_last [Nonempty s]
    (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    ∃ w : SharpClearing.SmithWitness C,
      w.lastFactor = SharpClearing.inverseDenominator C := by
  obtain ⟨w⟩ := exists_normalized_smith C hC
  exact ⟨w, (SharpClearing.inverseDenominator_eq_smithLastFactor w).symm⟩

theorem exists_smith_with_determinantal_last [Nonempty s]
    (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    ∃ w : SharpClearing.SmithWitness C,
      w.lastFactor = DeterminantalFactor.lastInvariantFactor C := by
  obtain ⟨w, hw⟩ := exists_smith_with_sharp_last C hC
  refine ⟨w, ?_⟩
  rw [hw, DeterminantalFactor.inverseDenominator_eq_det_div_cofactorGcd C hC]
  rfl

/-- The manuscript's displayed Smith formula, with unimodularity expressed
as absolute determinant one and every factor positive and in a chain. -/
theorem exists_smith_normal_form {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : C.det ≠ 0) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℕ),
      U.det.natAbs = 1 ∧ V.det.natAbs = 1 ∧ (∀ i, 0 < d i) ∧
      (∀ ⦃i j⦄, i ≤ j → d i ∣ d j) ∧
      U * C * V = Matrix.diagonal (fun i => (d i : ℤ)) := by
  obtain ⟨w⟩ := exists_normalized_smith C hC
  exact ⟨w.U, w.V, w.factor,
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.U_mul_Uinv),
    Int.natAbs_of_isUnit (Matrix.isUnit_det_of_right_inverse w.V_mul_Vinv),
    w.factor_pos, w.factor_chain, w.reduction⟩

end

end MainTheory.SmithExistence
