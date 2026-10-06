import MainTheory.DiagonalInfinitesimal

namespace MainTheory.DiagonalInfinitesimal

open MainTheory.PhysicalTorusCells

noncomputable section

/-- The paper's diagonal gate is literally the matrix exponential of the
weighted sum of number operators. -/
theorem operator_eq_matrix_exp {n : ℕ} (t : ℝ) (h : Fin n → ℝ) :
    operator (expAngles (t • h)) =
      NormedSpace.exp ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) • hamiltonian h) := by
  rw [hamiltonian, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext x y
  rw [operator_entry, Matrix.diagonal_apply]
  congr 1
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rfl

end

end MainTheory.DiagonalInfinitesimal
