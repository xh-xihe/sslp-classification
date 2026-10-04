import Orbit2.Purification
import Orbit2.TensorEncoder

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def tensorSplit (n : ℕ) : (Fin (n+1) → Fin 2) ≃ Fin 2 × (Fin n → Fin 2) where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by rcases x with ⟨j,t⟩; rfl

theorem tensor_sum_split {n : ℕ} (f : (Fin (n+1) → Fin 2) → ℂ) :
    (∑ s, f s) = ∑ j : Fin 2, ∑ t : Fin n → Fin 2, f (Fin.cons j t) := by
  simpa only [Fintype.sum_prod_type] using ((tensorSplit n).symm.sum_comp f).symm

def referenceColumn (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 7 → Fin 2) (Fin 1) ℂ := fun s _ => Q (fun i => s i.succ) (s 0)

/-- Splitting the reference Pauli action from the physical action. -/
theorem reference_action (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ)
    (r : Fin 4) (p : Label 6) (s : Fin 7 → Fin 2) :
    (operator (Fin.cons r p) * referenceColumn Q) s 0 =
      localC r (s 0) (FiveQubit.flipSite r (s 0)) *
        (operator p * Q) (fun i => s i.succ) (FiveQubit.flipSite r (s 0)) := by
  simp_rw [Matrix.mul_apply, HilbertBridge.operator_row]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [referenceColumn,HilbertBridge.flip,Fin.cons_zero,Fin.cons_succ,Fin.prod_univ_succ]
  simp only [mul_assoc] <;> rfl

theorem reference_compression (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ)
    (r : Fin 4) (p : Label 6) :
    ((referenceColumn Q).conjTranspose * operator (Fin.cons r p) * referenceColumn Q) 0 0 =
      ∑ j : Fin 2, localC r j (FiveQubit.flipSite r j) *
        (Q.conjTranspose * operator p * Q) j (FiveQubit.flipSite r j) := by
  rw [Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  change (∑ s, star (referenceColumn Q s 0) *
    (operator (Fin.cons r p) * referenceColumn Q) s 0) = _
  simp_rw [reference_action]
  rw [tensor_sum_split]
  rw [Matrix.mul_assoc Q.conjTranspose (operator p) Q]
  simp only [referenceColumn,Fin.cons_zero,Fin.cons_succ,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem reference_KL_zero (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ)
    (r : Fin 4) (hr : r ≠ 0) (p : Label 6) (c : ℂ)
    (hKL : Q.conjTranspose * operator p * Q = c • 1) :
    ((referenceColumn Q).conjTranspose * operator (Fin.cons r p) * referenceColumn Q) 0 0 = 0 := by
  rw [reference_compression,hKL]
  clear hKL
  fin_cases r
  · exact (hr rfl).elim
  · simp [Matrix.smul_apply,Matrix.one_apply,Fin.sum_univ_succ,FiveQubit.flipSite]
  · simp [Matrix.smul_apply,Matrix.one_apply,Fin.sum_univ_succ,FiveQubit.flipSite]
  · have hf : ∀ j : Fin 2, FiveQubit.flipSite (⟨3,by decide⟩ : Fin 4) j = j := by decide +kernel
    simp only [hf,Matrix.smul_apply,Matrix.one_apply,if_true,smul_eq_mul,mul_one]
    rw [← Finset.sum_mul]
    change Matrix.trace (localC ⟨3,by decide⟩) * c = 0
    rw [local_trace]
    norm_num

theorem Encoder.purification_column (V : Encoder) (x : SS.BitString 7) :
    referenceColumn V.tensorMatrix (bitsEquiv 7 x) 0 = V.purification x := by
  change V.psi (bit (x 0)) ((bitsEquiv 6).symm (fun i => bit (x i.succ))) =
    V.psi (if x 0 then 1 else 0) (fun i => x i.succ)
  have ht : (bitsEquiv 6).symm (fun i => bit (x i.succ)) = (fun i => x i.succ) := by
    funext i
    change (bit (x i.succ) == 1) = x i.succ
    cases hx : x i.succ <;> simp [bit,hx]
  rw [ht]
  rfl

/-- A single matrix column and a Hilbert state give the same expectation. -/
theorem column_compression {n : ℕ} (Q : Matrix (Fin n → Fin 2) (Fin 1) ℂ)
    (φ : SS.State n ℂ) (hφ : ∀ x, Q (bitsEquiv n x) 0 = φ x) (p : Label n) :
    SS.innerC φ (SS.pauliAct (decode p) φ) =
      (Q.conjTranspose * operator p * Q) 0 0 := by
  have hh (s : Fin n → Fin 2) : φ ((bitsEquiv n).symm s) = Q s 0 := by
    simpa only [Equiv.apply_symm_apply] using (hφ ((bitsEquiv n).symm s)).symm
  have ha (x : SS.BitString n) : SS.pauliAct (decode p) φ x =
      (operator p * Q) (bitsEquiv n x) 0 := by
    have h := pauli_action (decode p) φ x
    rw [label_decode] at h
    simpa only [hh,Matrix.mul_apply] using h.symm
  rw [Matrix.mul_assoc]
  simp only [SS.innerC,ha,← hφ,Matrix.mul_apply,Matrix.conjTranspose_apply]
  exact (bitsEquiv n).sum_comp (fun s => star (Q s 0) * ∑ t, operator p s t * Q t 0)

noncomputable def Encoder.labelMass (V : Encoder) (p : Label 7) : ℝ :=
  V.purificationMass (decode p)

theorem Encoder.reference_KL_mass_zero (V : Encoder) (p : Label 7)
    (hr : p 0 ≠ 0) (hw : (∑ i : Fin 6, if p i.succ = 0 then 0 else 1 : ℕ) ≤ 2) :
    V.labelMass p = 0 := by
  obtain ⟨c,hc⟩ := V.tensor_KL (fun i => p i.succ) hw
  have he : Fin.cons (p 0) (fun i => p i.succ) = p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hz := reference_KL_zero V.tensorMatrix (p 0) hr (fun i => p i.succ) c hc
  rw [he] at hz
  unfold Encoder.labelMass Encoder.purificationMass
  rw [column_compression (referenceColumn V.tensorMatrix) V.purification
    V.purification_column, hz]
  norm_num

end Orbit2
