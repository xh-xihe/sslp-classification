import MainTheory.Orbit3CliffordAverage
import MainTheory.PauliWordBridge

/-! # Actual spectator-Hadamard transformation of Pauli products

This proves the physical conjugation formula for arbitrary six-qubit vectors.
Combined with the genuine 24-element finite average, it gives the Ward rows
without assuming that any individual encoder is Hadamard invariant.
-/

namespace MainTheory.Orbit3HadamardBridge

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer MainTheory.PauliWordBridge
open MainTheory.Orbit3CliffordAverage SixQubit.Generated.SpectatorClifford
open scoped Matrix BigOperators

noncomputable section
set_option maxHeartbeats 8000000

def hLetter : Fin 4 → Fin 4 := ![0, 3, 2, 1]
def hSign : Fin 4 → ℂ := ![1, 1, -1, 1]
def hSignInt : Fin 4 → ℤ := ![1, 1, -1, 1]

theorem hSign_cast (p : Fin 4) : hSign p = (hSignInt p : ℂ) := by
  fin_cases p <;> norm_num [hSign, hSignInt]

theorem local_H (p : Fin 4) :
    star hadamard * pauli p * hadamard = hSign p • pauli (hLetter p) := by
  have hr : (starRingEnd ℂ) root = root := root_star
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauli, hSign, hLetter, Matrix.mul_apply,
      Matrix.star_apply, Fin.sum_univ_two, hr] <;>
    ring_nf <;> norm_num [root_sq] <;> ring

theorem tensor_single_scalar {n : ℕ} (A : Fin n → Mat2) (j : Fin n) (z : ℂ) :
    tensorKernel (Function.update A j (z • A j)) = z • tensorKernel A := by
  ext s t
  have hf : (fun k => Function.update A j (z • A j) k (bitIndex (s k)) (bitIndex (t k))) =
      Function.update (fun k => A k (bitIndex (s k)) (bitIndex (t k))) j
        (z * A j (bitIndex (s j)) (bitIndex (t j))) := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp only [Function.update_of_ne hk]
  change (∏ k, Function.update A j (z • A j) k (bitIndex (s k)) (bitIndex (t k))) =
    z * ∏ k, A k (bitIndex (s k)) (bitIndex (t k))
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ j)]
  have hprod := Finset.prod_update_of_mem (Finset.mem_univ j)
    (fun k => A k (bitIndex (s k)) (bitIndex (t k)))
    (A j (bitIndex (s j)) (bitIndex (t j)))
  rw [Function.update_eq_self] at hprod
  rw [hprod]
  ring

def hWord (p : Word 6) : Word 6 := Function.update p 0 (hLetter (p 0))

theorem word_H (p : Word 6) :
    star (oneQubitKernel 0 hadamard) * wordKernel p * oneQubitKernel 0 hadamard =
      hSign (p 0) • wordKernel (hWord p) := by
  rw [← tensorKernel_single 0 hadamard, wordKernel, ← tensorKernel_star,
    ← tensorKernel_mul, ← tensorKernel_mul]
  have hf : (fun j : Fin 6 => star (Function.update (fun _ => (1 : Mat2)) 0 hadamard j) *
      pauli (p j) * Function.update (fun _ => (1 : Mat2)) 0 hadamard j) =
      Function.update (fun j => pauli (hWord p j)) 0
        (hSign (p 0) • pauli (hWord p 0)) := by
    funext j
    by_cases hj : j = 0
    · subst j
      simpa [hWord] using local_H (p 0)
    · simp [Function.update_of_ne hj, hWord]
  rw [hf, tensor_single_scalar]
  rfl

theorem inner_action (U V : OperatorKernel 6) (w : SS.State 6 ℂ) :
    SS.innerC (kernelAction U w) (kernelAction V w) =
      SS.innerC w (kernelAction (star U * V) w) := by
  change star (U *ᵥ w) ⬝ᵥ (V *ᵥ w) = star w ⬝ᵥ ((star U * V) *ᵥ w)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem expectation_H (P : SS.PauliString 6) (w : SS.State 6 ℂ) :
    SS.innerC (act hadamard w) (SS.pauliAct P (act hadamard w)) =
      hSign (pauliWordEquiv P 0) * SS.innerC w
        (SS.pauliAct (pauliWordEquiv.symm (hWord (pauliWordEquiv P))) w) := by
  rw [← MainTheory.PauliKernelTrace.kernelAction_pauliKernel]
  unfold act
  rw [← MainTheory.CodePreservingUnitary.kernelAction_mul, inner_action]
  rw [← wordKernel_pauliWordEquiv, ← Matrix.mul_assoc, word_H]
  have hkernel : kernelAction (hSign (pauliWordEquiv P 0) • wordKernel (hWord (pauliWordEquiv P))) w =
      fun s => hSign (pauliWordEquiv P 0) *
        kernelAction (wordKernel (hWord (pauliWordEquiv P))) w s := by
    funext s
    simp only [kernelAction, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  rw [hkernel]
  have hword := wordKernel_pauliWordEquiv (pauliWordEquiv.symm (hWord (pauliWordEquiv P)))
  simp only [Equiv.apply_symm_apply] at hword
  rw [hword, MainTheory.PauliKernelTrace.kernelAction_pauliKernel]
  unfold SS.innerC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

def hPauli (P : SS.PauliString 6) : SS.PauliString 6 :=
  pauliWordEquiv.symm (hWord (pauliWordEquiv P))

def productSign (P : Fin 3 → SS.PauliString 6) : ℤ :=
  ∏ k, hSignInt (pauliWordEquiv (P k) 0)

theorem product_H (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ) :
    product P (act hadamard w) = (productSign P : ℝ) * product (fun k => hPauli (P k)) w := by
  unfold product
  simp_rw [expectation_H, hSign_cast]
  rw [Finset.prod_mul_distrib]
  have hs : (∏ k : Fin 3, (hSignInt (pauliWordEquiv (P k) 0) : ℂ)) = (productSign P : ℂ) := by
    simp only [productSign, Int.cast_prod]
  rw [hs]
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
  rfl

theorem actual_H_Ward (P : Fin 3 → SS.PauliString 6) (w : SS.State 6 ℂ) :
    (∑ g : Fin 24, (product P (act (clifford g) w) -
      (productSign P : ℝ) * product (fun k => hPauli (P k)) (act (clifford g) w))) = 0 := by
  have h := actual_H_product_identity P w
  simp_rw [product_H] at h
  rw [Finset.sum_sub_distrib, ← h]
  simp

end
end MainTheory.Orbit3HadamardBridge
