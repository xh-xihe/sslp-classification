import Orbit2.FiveQubit
import Orbit2.HilbertBridge
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! An arbitrary complex split isometry, rather than just a particular
one-parameter encoder. The finite rotated weight-three-code coefficient contractions are
ordinary kernel proofs and all subsequent matrix algebra is universal.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.NativeArbitrarySplitPerfectCode
open scoped BigOperators Matrix Kronecker
open Orbit2.TensorPauli
noncomputable section
abbrev Tail := Fin 4 → Fin 2
def raw (j a : Fin 2) (t : Tail) : GaussianInt :=
  Orbit2.FiveQubit.seed j ![a,t 0,t 1,t 2,t 3]
def flip (p : Label 4) (t : Tail) : Tail := Orbit2.HilbertBridge.flip p t
def amplitude (p : Label 4) (t : Tail) : GaussianInt :=
  ∏ i, localG (p i) (t i) (flip p t i)
def weight (p : Label 4) : ℕ := ∑ i, if p i=0 then 0 else 1
def coefficient (p : Label 4) (j k a b : Fin 2) : GaussianInt :=
  ∑ t, star (raw j a t)*amplitude p t*raw k b (flip p t)

theorem single_tail : ∀ p : Label 4, weight p≤1 → ∀ j k a b : Fin 2,
    coefficient p j k a b=if p=(fun _ => 0) ∧ j=k ∧ a=b then 32 else 0 := by decide +kernel
theorem double_tail : ∀ p : Label 4, weight p≤2 → ∀ j k : Fin 2,
    (∑ a, coefficient p j k a a)=if p=(fun _ => 0) ∧ j=k then 64 else 0 := by decide +kernel

def C : Matrix (Fin 2 × Tail) (Fin 2) ℂ := fun s j => (raw j s.1 s.2 : ℂ)/8
def V (W : Matrix (Fin 4) (Fin 2) ℂ) : Matrix (Fin 4 × Tail) (Fin 2 × Tail) ℂ :=
  W ⊗ₖ (1 : Matrix Tail Tail ℂ)
def split (W : Matrix (Fin 4) (Fin 2) ℂ) := V W*C

theorem amplitude_cast (p : Label 4) (t : Tail) :
    (amplitude p t : ℂ)=∏ i, localC (p i) (t i) (Orbit2.HilbertBridge.flip p t i) := by
  simp only [amplitude,map_prod,localC,Matrix.map_apply,flip]

theorem compression (F : Matrix (Fin 2) (Fin 2) ℂ) (p : Label 4) (j k : Fin 2) :
    (C.conjTranspose*(F ⊗ₖ operator p)*C) j k=
      (1/64 : ℂ)*(∑ a : Fin 2, ∑ b : Fin 2, F a b*(coefficient p j k a b : ℂ)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,C,Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  simp_rw [Orbit2.HilbertBridge.operator_row]
  simp only [mul_ite,ite_mul,zero_mul,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [star_div₀,star_ofNat]
  simp_rw [← amplitude_cast]
  calc
    _=(∑ a : Fin 2, ∑ t : Tail, ∑ b : Fin 2,
        F a b*(star (raw j a t : ℂ)*(amplitude p t : ℂ)*(raw k b (flip p t) : ℂ)))/64 := by
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro b _
      simp only [flip]
      ring
    _=(∑ a : Fin 2, ∑ b : Fin 2, ∑ t : Tail,
        F a b*(star (raw j a t : ℂ)*(amplitude p t : ℂ)*(raw k b (flip p t) : ℂ)))/64 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _=_ := by
      simp only [coefficient,map_sum,GaussianInt.toComplex_mul,GaussianInt.toComplex_star,
        ← Finset.mul_sum,div_eq_mul_inv,starRingEnd_apply]
      ring

theorem pure_single_tail (F : Matrix (Fin 2) (Fin 2) ℂ) (p : Label 4)
    (hp : weight p≤1) (hn : p≠(fun _ => 0)) :
    C.conjTranspose*(F ⊗ₖ operator p)*C=0 := by
  ext j k
  rw [compression]
  simp [single_tail p hp,hn]

theorem first_matrix_compression (F : Matrix (Fin 2) (Fin 2) ℂ) :
    C.conjTranspose*(F ⊗ₖ (1 : Matrix Tail Tail ℂ))*C=
      ((1/2 : ℂ)*F.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← operator_zero]
  ext j k
  rw [compression]
  have hp : weight (fun _ : Fin 4 => (0 : Fin 4))≤1 := by simp [weight]
  simp only [single_tail _ hp]
  by_cases hj : j=k
  · subst k
    norm_num [Fin.sum_univ_two,Matrix.trace,Matrix.diag,Matrix.smul_apply,
      Matrix.one_apply,GaussianInt.toComplex_def]
    ring
  · simp [hj,Matrix.smul_apply]

theorem pure_double_tail (p : Label 4) (hp : weight p≤2) (hn : p≠(fun _ => 0)) :
    C.conjTranspose*((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator p)*C=0 := by
  ext j k
  rw [compression]
  simp only [Matrix.one_apply,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  have he := congrArg GaussianInt.toComplex (double_tail p hp j k)
  simp only [map_sum,hn,false_and,if_false,map_zero] at he
  rw [he,mul_zero]
  rfl

theorem isometry : C.conjTranspose*C=1 := by
  have he := first_matrix_compression (1 : Matrix (Fin 2) (Fin 2) ℂ)
  norm_num [Matrix.one_kronecker_one] at he
  exact he

theorem split_isometry (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) :
    (split W).conjTranspose*split W=1 := by
  unfold split V
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker]
  simp only [Matrix.conjTranspose_one]
  calc
    _=C.conjTranspose*((W.conjTranspose ⊗ₖ (1 : Matrix Tail Tail ℂ))*(W ⊗ₖ (1 : Matrix Tail Tail ℂ)))*C := by simp only [Matrix.mul_assoc]
    _=C.conjTranspose*((W.conjTranspose*W) ⊗ₖ (1 : Matrix Tail Tail ℂ))*C := by
      rw [← Matrix.mul_kronecker_mul]
      simp only [Matrix.one_mul]
    _=1 := by rw [hW,Matrix.one_kronecker_one,Matrix.mul_one,isometry]

theorem split_pair_compression (W : Matrix (Fin 4) (Fin 2) ℂ)
    (E : Matrix (Fin 4) (Fin 4) ℂ) :
    (split W).conjTranspose*(E ⊗ₖ (1 : Matrix Tail Tail ℂ))*split W=
      ((1/2 : ℂ)*Matrix.trace (W.conjTranspose*E*W)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold split V
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker]
  simp only [Matrix.conjTranspose_one]
  have he : (W.conjTranspose ⊗ₖ (1 : Matrix Tail Tail ℂ))*(E ⊗ₖ (1 : Matrix Tail Tail ℂ))*(W ⊗ₖ (1 : Matrix Tail Tail ℂ))=
      (W.conjTranspose*E*W) ⊗ₖ (1 : Matrix Tail Tail ℂ) := by
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    simp
  calc
    _=C.conjTranspose*((W.conjTranspose ⊗ₖ (1 : Matrix Tail Tail ℂ))*(E ⊗ₖ (1 : Matrix Tail Tail ℂ))*(W ⊗ₖ (1 : Matrix Tail Tail ℂ)))*C := by simp only [Matrix.mul_assoc]
    _=_ := by rw [he,first_matrix_compression]

theorem split_trace (W : Matrix (Fin 4) (Fin 2) ℂ) (E : Matrix (Fin 4) (Fin 4) ℂ) :
    (1/2 : ℂ)*Matrix.trace (W.conjTranspose*E*W)=
      (1/2 : ℂ)*Matrix.trace ((W*W.conjTranspose)*E) := by
  rw [Matrix.trace_mul_cycle]

end
end MainTheory.NativeArbitrarySplitPerfectCode
