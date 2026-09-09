import MainTheory.PauliWordBridge

set_option autoImplicit false

namespace MainTheory.PauliAntiunitaryTensor

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer

noncomputable def localFactor (first : Bool) : Mat2 :=
  if first then pauli 1 else pauli 3 * pauli 1

def negative (first : Bool) (p : Fin 4) : Bool :=
  if first then p == 3 else p != 0

def localSign (first : Bool) (p : Fin 4) : ℂ := if negative first p then -1 else 1

theorem local_transform (first : Bool) (p : Fin 4) :
    (star (localFactor first) * pauli p * localFactor first).transpose =
      localSign first p • pauli p := by
  ext i j
  cases first <;> fin_cases p <;> fin_cases i <;> fin_cases j <;>
    simp +decide [localFactor, localSign, pauli, Matrix.transpose_apply,
      Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem tensor_transpose {n : ℕ} (U : Fin n → Mat2) :
    tensorKernel (fun j => (U j).transpose) = (tensorKernel U).transpose := by
  ext x y
  rfl

theorem word_transform {n : ℕ} (first : Fin n → Bool) (p : Word n) :
    (star (tensorKernel (fun j => localFactor (first j))) * wordKernel p *
      tensorKernel (fun j => localFactor (first j))).transpose =
        (∏ j, localSign (first j) (p j)) • wordKernel p := by
  rw [← tensorKernel_star, wordKernel, ← tensorKernel_mul, ← tensorKernel_mul, ← tensor_transpose]
  simp_rw [local_transform]
  ext x y
  simp [tensorKernel, Finset.prod_mul_distrib]

theorem sign_product {n : ℕ} (first : Fin n → Bool) (p : Word n) :
    (∏ j, localSign (first j) (p j)) =
      (-1 : ℂ) ^ (Finset.univ.filter (fun j => negative (first j) (p j))).card := by
  simp [localSign, Finset.prod_ite]

end MainTheory.PauliAntiunitaryTensor
