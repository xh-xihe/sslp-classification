import Orbit2.TSupport
import Orbit2.Global

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem flip_distance_site : ∀ (a : Fin 4) (b : Fin 2),
    (if FiveQubit.flipSite a b=b then 0 else 1 : ℕ) = if a=1 ∨ a=2 then 1 else 0 := by decide +kernel

theorem flip_distance (p : Label 4) (x : ActiveBits) :
    hamming (HilbertBridge.flip p x) x=transverseCount p := by
  unfold hamming transverseCount HilbertBridge.flip
  simp_rw [flip_distance_site]

theorem Encoder.physicalT_transverse_trace_zero (V : Encoder) (p : Label 4)
    (hp : transverseCount p≠1) : tau (operator p * V.physicalT)=0 := by
  have hz (x : ActiveBits) : V.physicalT (HilbertBridge.flip p x) x=0 :=
    V.physicalT_support _ _ (by rwa [flip_distance])
  unfold tau Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply,HilbertBridge.operator_row,ite_mul,zero_mul]
  simp [Finset.sum_ite_eq',hz]

def spinSign (p : Label 4) : ℤ := ∏ i, if p i=0 then 1 else -1
theorem spinSign_even : ∀ p : Label 4, pauliWeight p%2=0 → spinSign p=1 := by decide +kernel

theorem activeSpin_operator (p : Label 4) :
    activeSpin * (operator p).transpose * activeSpin = (spinSign p : ℂ) • operator p := by
  unfold activeSpin operator
  rw [tensor_transpose,tensor_mul,tensor_mul]
  simp_rw [local_spin]
  rw [tensor_smul]
  congr 1
  simp [spinSign]

theorem tau_spin_pair (E T : Defects.ActiveMatrix) :
    tau ((activeSpin * E.transpose * activeSpin) * (activeSpin * T.transpose * activeSpin)) =
      tau (E*T) := by
  have he : (activeSpin * E.transpose * activeSpin) * (activeSpin * T.transpose * activeSpin) =
      activeSpin * (E.transpose * T.transpose) * activeSpin := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc activeSpin activeSpin,activeSpin_square,Matrix.one_mul]
  rw [he]
  unfold tau
  rw [Matrix.trace_mul_cycle,activeSpin_square,Matrix.one_mul,
    ← Matrix.trace_transpose (E.transpose * T.transpose),Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.transpose_transpose,Matrix.trace_mul_comm]

theorem Encoder.physicalT_even_trace_zero (V : Encoder) (p : Label 4)
    (hp : pauliWeight p%2=0) : tau (operator p * V.physicalT)=0 := by
  have h := tau_spin_pair (operator p) V.physicalT
  rw [activeSpin_operator,spinSign_even p hp] at h
  simp only [Int.cast_one,one_smul,V.physicalT_spin_skew,Matrix.mul_neg,tau,Matrix.trace_neg,neg_div] at h
  unfold tau
  linear_combination -h/2

theorem pauliBasis_complete : ∀ p : Label 4,
    transverseCount p=1 → pauliWeight p%2≠0 → ∃ i : Fin 32, pauliBasis i=p := by decide +kernel
theorem pauliBasis_injective : Function.Injective pauliBasis := by decide +kernel

theorem Encoder.physicalT_outside_basis_zero (V : Encoder) (p : Label 4)
    (hp : ¬ ∃ i : Fin 32, pauliBasis i=p) : tau (operator p * V.physicalT)=0 := by
  by_cases ht : transverseCount p=1
  · by_cases hw : pauliWeight p%2=0
    · exact V.physicalT_even_trace_zero p hw
    · exact False.elim (hp (pauliBasis_complete p ht hw))
  · exact V.physicalT_transverse_trace_zero p ht

noncomputable def Encoder.physicalT_coordinates (V : Encoder) : Fin 32 → ℂ :=
  fun i => tau (operator (pauliBasis i) * V.physicalT)

/-- Every physical orbit-2 T has exactly the certificate's 32-coordinate
Pauli expansion, with its true normalized trace coefficients. -/
theorem Encoder.physicalT_expansion (V : Encoder) :
    V.physicalT = expansion pauliBasis V.physicalT_coordinates := by
  classical
  rw [matrix_reconstruction V.physicalT]
  unfold expansion Encoder.physicalT_coordinates
  symm
  apply Fintype.sum_of_injective pauliBasis pauliBasis_injective
  · intro p hp
    rw [V.physicalT_outside_basis_zero p hp,zero_smul]
  · intro i
    rfl

end Orbit2
