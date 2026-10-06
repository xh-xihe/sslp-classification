import MainTheory.SmithDiagonalExistence

namespace MainTheory.SmithExistence

open scoped Matrix

noncomputable section

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- Equivalence by two actually invertible integral matrices. -/
def IntegralEquivalent (C D : Matrix s s ℤ) : Prop :=
  ∃ (U V : (Matrix s s ℤ)ˣ), (U : Matrix s s ℤ) * C * (V : Matrix s s ℤ) = D

theorem IntegralEquivalent.refl (C : Matrix s s ℤ) : IntegralEquivalent C C :=
  ⟨1, 1, by simp⟩

theorem IntegralEquivalent.trans {A B C : Matrix s s ℤ}
    (hAB : IntegralEquivalent A B) (hBC : IntegralEquivalent B C) : IntegralEquivalent A C := by
  obtain ⟨U, V, hAB⟩ := hAB
  obtain ⟨S, T, hBC⟩ := hBC
  refine ⟨S * U, V * T, ?_⟩
  simpa only [Units.val_mul, Matrix.mul_assoc, ← hAB] using hBC

theorem IntegralEquivalent.symm {C D : Matrix s s ℤ}
    (h : IntegralEquivalent C D) : IntegralEquivalent D C := by
  obtain ⟨U, V, rfl⟩ := h
  refine ⟨U⁻¹, V⁻¹, ?_⟩
  simp [← Matrix.mul_assoc]

def signUnit (a : ℤ) : ℤ := if 0 ≤ a then 1 else -1

theorem signUnit_sq (a : ℤ) : signUnit a * signUnit a = 1 := by
  unfold signUnit
  split_ifs <;> norm_num

theorem signUnit_mul (a : ℤ) : signUnit a * a = a.natAbs := by
  unfold signUnit
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

def signMatrixUnit (a : s → ℤ) : (Matrix s s ℤ)ˣ where
  val := Matrix.diagonal (fun i => signUnit (a i))
  inv := Matrix.diagonal (fun i => signUnit (a i))
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [signUnit_sq, Matrix.diagonal_one]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [signUnit_sq, Matrix.diagonal_one]

theorem exists_positive_diagonal (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    ∃ d : s → ℕ, (∀ i, 0 < d i) ∧
      IntegralEquivalent C (Matrix.diagonal (fun i => (d i : ℤ))) := by
  obtain ⟨w⟩ := exists_diagonalReduction C hC
  let U : (Matrix s s ℤ)ˣ := ⟨w.U, w.Uinv, w.U_mul_Uinv, w.Uinv_mul_U⟩
  let V : (Matrix s s ℤ)ˣ := ⟨w.V, w.Vinv, w.V_mul_Vinv, w.Vinv_mul_V⟩
  refine ⟨fun i => (w.entry i).natAbs, fun i => Int.natAbs_pos.mpr (w.entry_ne_zero i), ?_⟩
  refine ⟨signMatrixUnit w.entry * U, V, ?_⟩
  change (Matrix.diagonal (fun i => signUnit (w.entry i)) * w.U) * C * w.V = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc w.U, w.reduction,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact signUnit_mul _

end

end MainTheory.SmithExistence
