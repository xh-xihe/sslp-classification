import MainTheory.PrimitiveOrderTwoCatKL
import Orbit2.FiveQubitPhysical

/-! The actual weight-three and weight-six logical Paulis of the printed
cat construction, with the stabilizing tail flip and its product phase.
-/

namespace MainTheory.PrimitiveOrderTwoCatLogicals
open MainTheory.PrimitiveOrderTwoCatAlgebra
open MainTheory.PrimitiveOrderTwoCatCompression
open MainTheory.PrimitiveOrderTwoCatEncoder
open MainTheory.PrimitiveOrderTwoCatKL
open Orbit2.TensorPauli Orbit2.FiveQubit
open scoped BigOperators Matrix Kronecker
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000

def catActionG (p : Label 5) (j : Fin 5) (s : Bits) : GaussianInt :=
  amplitude p s*((if flip p s=unit j then 1 else 0)+
    (if flip p s=complement (unit j) then 1 else 0))

theorem cat_action (p : Label 5) (s : Bits) (j : Fin 5) :
    (operator p*cats) s j=(h : ℂ)*(catActionG p j s : ℂ) := by
  simp [Matrix.mul_apply,operator_row,cats,catActionG,
    GaussianInt.toComplex_mul,mul_left_comm]

def tailZ : Label 5 := ![0,0,0,3,3]
def tailX : Label 5 := ![1,1,1,1,1]
def signG : Fin 5 → GaussianInt := ![1,1,1,-1,-1]
def sign : Fin 5 → ℂ := fun j => (signG j : ℂ)

theorem tailZ_raw : ∀ s : Bits,∀ j : Fin 5,catActionG tailZ j s=
    signG j*((if s=unit j then 1 else 0)+
      (if s=complement (unit j) then 1 else 0)) := by decide +kernel

theorem tailX_raw : ∀ s : Bits,∀ j : Fin 5,catActionG tailX j s=
    (if s=unit j then 1 else 0)+(if s=complement (unit j) then 1 else 0) := by
  decide +kernel

theorem tailZ_action : operator tailZ*cats=cats*Matrix.diagonal sign := by
  ext s j
  rw [cat_action,tailZ_raw]
  simp [Matrix.mul_apply,Matrix.diagonal,sign,cats,mul_comm,mul_left_comm]

theorem tailX_action : operator tailX*cats=cats := by
  ext s j
  rw [cat_action,tailX_raw]
  simp [cats]

def L3 : Matrix PhysicalBasis PhysicalBasis ℂ :=
  physicalPauli ![3,0,0,0,3,3]
def SX : Matrix PhysicalBasis PhysicalBasis ℂ :=
  physicalPauli ![0,1,1,1,1,1]
def L6 : Matrix PhysicalBasis PhysicalBasis ℂ :=
  -physicalPauli ![3,1,1,1,2,2]
def logicalZ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![-1,1]

theorem localZ_G : ∀ i j : Fin 2,localG 3 i j=
    if i=j then (if i=0 then 1 else -1) else 0 := by decide +kernel

theorem localZ : localC 3=Matrix.diagonal (![1,-1] : Fin 2 → ℂ) := by
  unfold localC
  ext i j
  rw [Matrix.map_apply,localZ_G]
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem spinors_logical (a b : ℝ) :
    (localC 3 ⊗ₖ Matrix.diagonal sign)*spinors a b=spinors a b*logicalZ := by
  rw [localZ]
  ext ij q
  obtain ⟨i,j⟩ := ij
  fin_cases i <;> fin_cases j <;> fin_cases q
  all_goals apply Complex.ext
  all_goals norm_num [Matrix.mul_apply,Matrix.kronecker_apply,
    Matrix.diagonal,Matrix.map_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,
    sign,signG,logicalZ,spinors,x,y,gamma,delta,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.div_re,Complex.div_im,Complex.star_def,map_ofNat,
    -GaussianInt.intCast_re,-GaussianInt.intCast_im]

theorem logical3_action (a b : ℝ) : L3*encoder a b=encoder a b*logicalZ := by
  have he : L3=localC 3 ⊗ₖ operator tailZ := rfl
  rw [he,encoder,liftCat,← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,tailZ_action]
  rw [show localC 3 ⊗ₖ (cats*Matrix.diagonal sign)=
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ cats)*
        (localC 3 ⊗ₖ Matrix.diagonal sign) by
          rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]]
  rw [Matrix.mul_assoc,spinors_logical,← Matrix.mul_assoc]

theorem stabilizer_action (a b : ℝ) : SX*encoder a b=encoder a b := by
  have he : SX=(1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ operator tailX := by
    change localC 0 ⊗ₖ operator tailX= _
    rw [localC_zero]
  rw [he,encoder,liftCat,← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,
    Matrix.mul_one,tailX_action]

theorem product_phase : L3*SX=L6 := by
  have hp : product tailZ tailX=(![1,1,1,2,2] : Label 5) := by decide +kernel
  have hg : phase tailZ tailX=(-1 : GaussianInt) := by decide +kernel
  change (localC 3 ⊗ₖ operator tailZ)*(localC 0 ⊗ₖ operator tailX)=
    -(localC 3 ⊗ₖ operator (![1,1,1,2,2] : Label 5))
  rw [localC_zero,← Matrix.mul_kronecker_mul,Matrix.mul_one,
    operator_mul,hp,hg]
  simp only [map_neg,map_one,neg_one_smul]
  ext ij kl
  simp

theorem logical6_action (a b : ℝ) : L6*encoder a b=encoder a b*logicalZ := by
  rw [← product_phase,Matrix.mul_assoc,stabilizer_action,logical3_action]

theorem logical_weights : totalWeight (![3,0,0,0,3,3] : Label 6)=3 ∧
    totalWeight (![3,1,1,1,2,2] : Label 6)=6 := by decide +kernel

end
end MainTheory.PrimitiveOrderTwoCatLogicals
