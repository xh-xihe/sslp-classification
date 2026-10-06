import MainTheory.PauliTensorTransfer
import MainTheory.SingletonBitSplit

/-! # Actual partial traces and embedded tensor-Pauli coefficients -/

namespace MainTheory.PauliPartialTrace

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer MainTheory.SingletonBitSplit
open scoped BigOperators Matrix

noncomputable section
variable {a b : ℕ}

def first (M : OperatorKernel (a + b)) : OperatorKernel a :=
  fun x y => ∑ z : SS.BitString b, M (Fin.append x z) (Fin.append y z)

def second (M : OperatorKernel (a + b)) : OperatorKernel b :=
  fun x y => ∑ z : SS.BitString a, M (Fin.append z x) (Fin.append z y)

theorem wordKernel_append (p : Word a) (q : Word b)
    (x y : SS.BitString a) (u v : SS.BitString b) :
    wordKernel (Fin.append p q) (Fin.append x u) (Fin.append y v) =
      wordKernel p x y * wordKernel q u v := by
  have hf : (fun j => pauli (Fin.append p q j)) =
      Fin.append (fun j => pauli (p j)) (fun j => pauli (q j)) := by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp
  unfold wordKernel
  rw [hf]
  exact tensorKernel_append (fun j => pauli (p j)) (fun j => pauli (q j)) x y u v

theorem wordKernel_zero (n : ℕ) : wordKernel (fun _ : Fin n => 0) = 1 := by
  simp only [wordKernel, pauli_zero, tensorKernel_one]

theorem first_coefficient (M : OperatorKernel (a + b)) (p : Word a) :
    Matrix.trace (wordKernel (Fin.append p (fun _ : Fin b => 0)) * M) =
      Matrix.trace (wordKernel p * first M) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [sum_split]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [sum_split, wordKernel_append, wordKernel_zero, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [first, Finset.mul_sum]

theorem second_coefficient (M : OperatorKernel (a + b)) (p : Word b) :
    Matrix.trace (wordKernel (Fin.append (fun _ : Fin a => 0) p) * M) =
      Matrix.trace (wordKernel p * second M) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [sum_split, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [sum_split, wordKernel_append, wordKernel_zero, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul]
  conv_lhs =>
    arg 2
    ext y
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [second, Finset.mul_sum]

end
end MainTheory.PauliPartialTrace
