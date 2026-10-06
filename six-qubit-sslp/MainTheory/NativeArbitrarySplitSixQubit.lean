import MainTheory.NativeArbitrarySplitPerfectCode

/-! Arbitrary complex split isometries satisfy the actual six-qubit Pauli KL
conditions. The computational basis is explicitly transported to the split
pair and four unsplit sites; all low-weight cases are covered. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.NativeArbitrarySplitSixQubit
open scoped BigOperators Matrix Kronecker
open Orbit2.TensorPauli MainTheory.NativeArbitrarySplitPerfectCode
noncomputable section

def tailLabel (p : Label 6) : Label 4 := ![p 2,p 3,p 4,p 5]
def pairOperator (p : Label 6) : Matrix (Fin 4) (Fin 4) ℂ := fun u v =>
  localC (p 0) ((![0,0,1,1] : Fin 4 → Fin 2) u) ((![0,0,1,1] : Fin 4 → Fin 2) v)*
  localC (p 1) ((![0,1,0,1] : Fin 4 → Fin 2) u) ((![0,1,0,1] : Fin 4 → Fin 2) v)
def weight6 (p : Label 6) : ℕ := ∑ i, if p i=0 then 0 else 1

def sixBits (s : Fin 4 × Tail) : Fin 6 → Fin 2 :=
  ![(![0,0,1,1] : Fin 4 → Fin 2) s.1,(![0,1,0,1] : Fin 4 → Fin 2) s.1,
    s.2 0,s.2 1,s.2 2,s.2 3]
def pairIndex (a b : Fin 2) : Fin 4 := ⟨2*a.val+b.val,by omega⟩
def splitBits (s : Fin 6 → Fin 2) : Fin 4 × Tail :=
  (pairIndex (s 0) (s 1),![s 2,s 3,s 4,s 5])
def basis : (Fin 4 × Tail) ≃ (Fin 6 → Fin 2) where
  toFun := sixBits
  invFun := splitBits
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem operator_factor (p : Label 6) :
    (operator p).submatrix basis basis=pairOperator p ⊗ₖ operator (tailLabel p) := by
  ext s t
  change (∏ i, localC (p i) (sixBits s i) (sixBits t i))=
    pairOperator p s.1 t.1*(∏ i, localC (tailLabel p i) (s.2 i) (t.2 i))
  rw [Fin.prod_univ_six,Fin.prod_univ_four]
  change
    localC (p 0) ((![0,0,1,1] : Fin 4 → Fin 2) s.1) ((![0,0,1,1] : Fin 4 → Fin 2) t.1)*
    localC (p 1) ((![0,1,0,1] : Fin 4 → Fin 2) s.1) ((![0,1,0,1] : Fin 4 → Fin 2) t.1)*
    localC (p 2) (s.2 0) (t.2 0)*localC (p 3) (s.2 1) (t.2 1)*
    localC (p 4) (s.2 2) (t.2 2)*localC (p 5) (s.2 3) (t.2 3)=
    (localC (p 0) ((![0,0,1,1] : Fin 4 → Fin 2) s.1) ((![0,0,1,1] : Fin 4 → Fin 2) t.1)*
    localC (p 1) ((![0,1,0,1] : Fin 4 → Fin 2) s.1) ((![0,1,0,1] : Fin 4 → Fin 2) t.1))*
    (localC (p 2) (s.2 0) (t.2 0)*localC (p 3) (s.2 1) (t.2 1)*
    localC (p 4) (s.2 2) (t.2 2)*localC (p 5) (s.2 3) (t.2 3))
  ring

theorem operator_original (p : Label 6) :
    operator p=(pairOperator p ⊗ₖ operator (tailLabel p)).submatrix basis.symm basis.symm := by
  ext s t
  have he := congrArg (fun M => M (basis.symm s) (basis.symm t)) (operator_factor p)
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using he

theorem weight_tail_le : ∀ p : Label 6, weight (tailLabel p) ≤ weight6 p := by decide +kernel
theorem tail_zero : ∀ p : Label 4, weight p=0 ↔ p=(fun _ => 0) := by decide +kernel
theorem pair_zero_of_tail_two : ∀ p : Label 6,
    weight6 p ≤ 2 → weight (tailLabel p)=2 → p 0=0 ∧ p 1=0 := by decide +kernel

theorem pair_identity (p : Label 6) (h0 : p 0=0) (h1 : p 1=0) :
    pairOperator p=1 := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    norm_num [pairOperator,h0,h1,localC,localG,GaussianInt.toComplex_def]

theorem split_compression (W : Matrix (Fin 4) (Fin 2) ℂ)
    (E : Matrix (Fin 4) (Fin 4) ℂ) (p : Label 4) :
    (split W).conjTranspose*(E ⊗ₖ operator p)*split W=
      C.conjTranspose*((W.conjTranspose*E*W) ⊗ₖ operator p)*C := by
  unfold split V
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker]
  simp only [Matrix.conjTranspose_one]
  have he : (W.conjTranspose ⊗ₖ (1 : Matrix Tail Tail ℂ))*(E ⊗ₖ operator p)*
      (W ⊗ₖ (1 : Matrix Tail Tail ℂ))=(W.conjTranspose*E*W) ⊗ₖ operator p := by
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul,Matrix.mul_one]
  calc
    _=C.conjTranspose*((W.conjTranspose ⊗ₖ (1 : Matrix Tail Tail ℂ))*
        (E ⊗ₖ operator p)*(W ⊗ₖ (1 : Matrix Tail Tail ℂ)))*C := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [he]

def scalar (W : Matrix (Fin 4) (Fin 2) ℂ) (p : Label 6) : ℂ :=
  if tailLabel p=(fun _ => 0) then (1/2 : ℂ)*Matrix.trace (W.conjTranspose*pairOperator p*W)
    else 0

theorem split_KL (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (p : Label 6) (hp : weight6 p ≤ 2) :
    (split W).conjTranspose*(pairOperator p ⊗ₖ operator (tailLabel p))*split W=
      scalar W p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  by_cases hz : tailLabel p=(fun _ => 0)
  · rw [hz,operator_zero,split_pair_compression]
    simp only [scalar,hz,if_true]
  · have ht : weight (tailLabel p) ≤ 2 := le_trans (weight_tail_le p) hp
    rw [split_compression]
    by_cases hsmall : weight (tailLabel p) ≤ 1
    · rw [pure_single_tail _ _ hsmall hz]
      simp only [scalar,hz,if_false,zero_smul]
    · have htwo : weight (tailLabel p)=2 := by omega
      obtain ⟨h0,h1⟩ := pair_zero_of_tail_two p hp htwo
      rw [pair_identity p h0 h1,Matrix.mul_one,hW,pure_double_tail _ ht hz]
      simp only [scalar,hz,if_false,zero_smul]

def code (W : Matrix (Fin 4) (Fin 2) ℂ) : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ :=
  (split W).submatrix basis.symm id

theorem compression_transport (W : Matrix (Fin 4) (Fin 2) ℂ) (p : Label 6) :
    (code W).conjTranspose*operator p*code W=
      (split W).conjTranspose*(pairOperator p ⊗ₖ operator (tailLabel p))*split W := by
  rw [operator_original]
  unfold code
  rw [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  rfl

theorem code_isometry (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) :
    (code W).conjTranspose*code W=1 := by
  unfold code
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,split_isometry W hW]
  rfl

theorem code_KL (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (p : Label 6) (hp : weight6 p ≤ 2) :
    (code W).conjTranspose*operator p*code W=scalar W p • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [compression_transport]
  exact split_KL W hW p hp

def projector (W : Matrix (Fin 4) (Fin 2) ℂ) := code W*(code W).conjTranspose

theorem projector_KL (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (p : Label 6) (hp : weight6 p ≤ 2) :
    projector W*operator p*projector W=scalar W p • projector W := by
  unfold projector
  calc
    _=code W*((code W).conjTranspose*operator p*code W)*(code W).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _=_ := by rw [code_KL W hW p hp]; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]

theorem unsplit_scalar_zero (W : Matrix (Fin 4) (Fin 2) ℂ) (p : Label 6)
    (hp : tailLabel p ≠ (fun _ => 0)) : scalar W p=0 := by simp only [scalar,hp,if_false]

theorem hilbert_orthonormal (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (j k : Fin 2) :
    SS.innerC (Orbit2.HilbertBridge.words (code W) j)
      (Orbit2.HilbertBridge.words (code W) k)=if j=k then 1 else 0 := by
  have he := Orbit2.HilbertBridge.compression (code W) (Orbit2.identityPauli 6) j k
  have hz : Orbit2.HilbertBridge.label (Orbit2.identityPauli 6)=(fun _ => 0) := rfl
  rw [Orbit2.pauliAct_identity,hz,operator_zero,Matrix.mul_one,code_isometry W hW] at he
  simpa only [Matrix.one_apply] using he

theorem hilbert_distance_three (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) :
    SS.HasDistance (Orbit2.HilbertBridge.words (code W)) 3 := by
  intro p hp
  refine ⟨scalar W (Orbit2.HilbertBridge.label p),?_⟩
  intro j k
  rw [Orbit2.HilbertBridge.compression,code_KL W hW (Orbit2.HilbertBridge.label p)
    (by simpa only [weight6,Orbit2.HilbertBridge.label_weight] using hp)]
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]

end
end MainTheory.NativeArbitrarySplitSixQubit
