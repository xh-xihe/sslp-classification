import MainTheory.PauliTransferTwo
import MainTheory.BlockUnitaryNorm
import MainTheory.LocalUnitaryClosure

/-! # Tensor Pauli coefficients and conserved weight blocks under arbitrary local unitaries -/

namespace MainTheory.PauliTensorTransfer

open ClassificationLevels LocalTensorKernel PauliTransferTwo
open scoped Matrix

noncomputable section

variable {n : ℕ}

abbrev Word (n : ℕ) := Fin n → Fin 4

def wordKernel (p : Word n) : OperatorKernel n := tensorKernel (fun j => pauli (p j))

def wordWeight (p : Word n) : ℕ := (Finset.univ.filter fun j => p j ≠ 0).card

def tensorTransfer (U : Fin n → Mat2) : Matrix (Word n) (Word n) ℂ :=
  fun p q => ∏ j, transfer (U j) (p j) (q j)

theorem tensorTransfer_unitary (U : Fin n → Mat2) (hU : ∀ j, IsOneQubitUnitary (U j)) :
    star (tensorTransfer U) * tensorTransfer U = 1 ∧
      tensorTransfer U * star (tensorTransfer U) = 1 := by
  have hleft : star (tensorTransfer U) * tensorTransfer U = 1 := by
    ext q r
    simp only [Matrix.mul_apply, Matrix.star_apply, tensorTransfer, star_prod]
    simp_rw [← Finset.prod_mul_distrib]
    have hprod := Fintype.prod_sum (fun j (p : Fin 4) =>
      star (transfer (U j) p (q j)) * transfer (U j) p (r j))
    rw [← hprod]
    have hlocal (j : Fin n) :
        (∑ p : Fin 4, star (transfer (U j) p (q j)) * transfer (U j) p (r j))
          = if q j = r j then 1 else 0 := by
      exact congrFun (congrFun (transfer_unitary (U j) (hU j)).1 (q j)) (r j)
    simp_rw [hlocal]
    classical
    by_cases hqr : q = r
    · subst r
      simp
    · rw [Matrix.one_apply_ne hqr]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hqr
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  exact ⟨hleft, mul_eq_one_comm.1 hleft⟩

theorem tensorTransfer_block (U : Fin n → Mat2) (hU : ∀ j, IsOneQubitUnitary (U j))
    (p q : Word n) (hpq : wordWeight p ≠ wordWeight q) : tensorTransfer U p q = 0 := by
  classical
  by_contra h
  have hlocal : ∀ j, transfer (U j) (p j) (q j) ≠ 0 :=
    fun j => (Finset.prod_ne_zero_iff.1 h) j (Finset.mem_univ j)
  have hzero (j : Fin n) : p j = 0 ↔ q j = 0 := by
    constructor
    · intro hp
      by_contra hq
      have hz : transfer (U j) (p j) (q j) = 0 := by
        rw [hp, transfer_zero_row _ (hU j), if_neg hq]
      exact hlocal j hz
    · intro hq
      by_contra hp
      have hz : transfer (U j) (p j) (q j) = 0 := by
        rw [hq, transfer_zero_column _ (hU j), if_neg hp]
      exact hlocal j hz
  apply hpq
  unfold wordWeight
  congr 1
  exact Finset.filter_congr (fun j _ => not_congr (hzero j))

theorem tensor_basis_expansion (A : Fin n → Mat2) :
    tensorKernel A = ∑ p : Word n, (∏ j, coefficient (p j) (A j)) • wordKernel p := by
  ext x y
  have hA (j : Fin n) : A j (bitIndex (x j)) (bitIndex (y j)) =
      ∑ p : Fin 4, coefficient p (A j) * pauli p (bitIndex (x j)) (bitIndex (y j)) := by
    have h := congrFun (congrFun (pauli_expansion (A j)) (bitIndex (x j))) (bitIndex (y j))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  simp only [tensorKernel, hA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    wordKernel, tensorKernel]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.prod_mul_distrib

theorem conjugate_word_expansion (U : Fin n → Mat2) (q : Word n) :
    tensorKernel U * wordKernel q * star (tensorKernel U) =
      ∑ p : Word n, tensorTransfer U p q • wordKernel p := by
  rw [wordKernel, ← tensorKernel_star, ← tensorKernel_mul, ← tensorKernel_mul]
  exact tensor_basis_expansion (fun j => U j * pauli (q j) * star (U j))

def traces (A : OperatorKernel n) (p : Word n) : ℂ := Matrix.trace (wordKernel p * A)

theorem traces_conjugate (U : Fin n → Mat2) (A : OperatorKernel n) :
    traces (tensorKernel U * A * star (tensorKernel U)) =
      (tensorTransfer (fun j => star (U j))).transpose *ᵥ traces A := by
  funext q
  unfold traces
  have hcycle : Matrix.trace (wordKernel q * (tensorKernel U * A * star (tensorKernel U)))
      = Matrix.trace ((star (tensorKernel U) * wordKernel q * tensorKernel U) * A) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc]
  rw [hcycle]
  have hexp : star (tensorKernel U) * wordKernel q * tensorKernel U =
      ∑ p : Word n, tensorTransfer (fun j => star (U j)) p q • wordKernel p := by
    simpa only [tensorKernel_star, star_star] using
      conjugate_word_expansion (fun j => star (U j)) q
  rw [hexp]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem tensorTransfer_transpose_unitary (U : Fin n → Mat2)
    (hU : ∀ j, IsOneQubitUnitary (U j)) :
    star (tensorTransfer U).transpose * (tensorTransfer U).transpose = 1 := by
  have ht : star (tensorTransfer U).transpose = (star (tensorTransfer U)).transpose := by
    ext p q
    rfl
  rw [ht, ← Matrix.transpose_mul, (tensorTransfer_unitary U hU).2, Matrix.transpose_one]

/-- Every exact Pauli-weight sum is preserved by arbitrary local unitary conjugation. -/
theorem trace_weight_invariant (U : Fin n → Mat2)
    (hU : ∀ j, IsOneQubitUnitary (U j)) (A : OperatorKernel n) (k : ℕ) :
    (∑ p ∈ Finset.univ.filter (fun p : Word n => wordWeight p = k),
      Complex.normSq (traces (tensorKernel U * A * star (tensorKernel U)) p)) =
      ∑ p ∈ Finset.univ.filter (fun p : Word n => wordWeight p = k), Complex.normSq (traces A p) := by
  rw [traces_conjugate]
  apply BlockUnitaryNorm.sum_normSq_block
  · exact tensorTransfer_transpose_unitary (fun j => star (U j))
      (fun j => LocalUnitaryClosure.unitary_star (hU j))
  · intro p q hpq
    exact tensorTransfer_block (fun j => star (U j))
      (fun j => LocalUnitaryClosure.unitary_star (hU j)) q p hpq.symm

end

end MainTheory.PauliTensorTransfer
