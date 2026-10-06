import MainTheory.LocalTensorKernel

/-! # The Pauli coefficient map for an arbitrary unitary two-by-two matrix -/

namespace MainTheory.PauliTransferTwo

open ClassificationLevels

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def pauli : Fin 4 → Mat2 :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

def coefficient (p : Fin 4) (A : Mat2) : ℂ := (1 / 2 : ℂ) * Matrix.trace (pauli p * A)

@[simp] theorem pauli_zero : pauli 0 = 1 := rfl

@[simp] theorem pauli_star (p : Fin 4) : star (pauli p) = pauli p := by
  ext i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.star_apply]

theorem coefficient_pauli (p q : Fin 4) : coefficient p (pauli q) = if p = q then 1 else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [coefficient, pauli, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

theorem pauli_expansion (A : Mat2) : (∑ p, coefficient p A • pauli p) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficient, pauli, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Polarized Parseval identity, retaining both arbitrary complex matrices. -/
theorem coefficient_inner (A B : Mat2) :
    (∑ p, star (coefficient p A) * coefficient p B) =
      (1 / 2 : ℂ) * Matrix.trace (star A * B) := by
  simp [coefficient, pauli, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem trace_conjugate (U : Mat2) (hU : IsOneQubitUnitary U) (A : Mat2) :
    Matrix.trace (U * A * star U) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, hU.1, Matrix.one_mul]

def transfer (U : Mat2) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun p q => coefficient p (U * pauli q * star U)

/-- Arbitrary local unitaries act unitarily on the Pauli coefficient space. -/
theorem transfer_unitary (U : Mat2) (hU : IsOneQubitUnitary U) :
    star (transfer U) * transfer U = 1 ∧ transfer U * star (transfer U) = 1 := by
  have hleft : star (transfer U) * transfer U = 1 := by
    ext q r
    change (∑ p, star (coefficient p (U * pauli q * star U)) *
      coefficient p (U * pauli r * star U)) = _
    rw [coefficient_inner]
    have hprod : star (U * pauli q * star U) * (U * pauli r * star U)
        = U * (pauli q * pauli r) * star U := by
      simp only [star_mul, star_star, pauli_star]
      calc _ = U * pauli q * (star U * U) * pauli r * star U := by simp [Matrix.mul_assoc]
        _ = _ := by rw [hU.1]; simp [Matrix.mul_assoc]
    rw [hprod, trace_conjugate U hU]
    exact coefficient_pauli q r
  exact ⟨hleft, mul_eq_one_comm.1 hleft⟩

/-- Identity and traceless Pauli directions do not mix under local conjugation. -/
theorem transfer_zero_row (U : Mat2) (hU : IsOneQubitUnitary U) (q : Fin 4) :
    transfer U 0 q = if q = 0 then 1 else 0 := by
  rw [transfer, coefficient, pauli_zero, Matrix.one_mul, trace_conjugate U hU]
  simpa only [coefficient, pauli_zero, Matrix.one_mul, eq_comm] using coefficient_pauli 0 q

theorem transfer_zero_column (U : Mat2) (hU : IsOneQubitUnitary U) (p : Fin 4) :
    transfer U p 0 = if p = 0 then 1 else 0 := by
  rw [transfer, pauli_zero, Matrix.mul_one, hU.2]
  exact coefficient_pauli p 0

end

end MainTheory.PauliTransferTwo
