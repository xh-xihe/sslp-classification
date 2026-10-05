import MainTheory.PrimitiveOrderTwoCatCompression

/-! The literal six-qubit cat encoder in the first-qubit/tail product basis.
The physical tensor operator is compressed through the actual cat isometry.
-/

namespace MainTheory.PrimitiveOrderTwoCatEncoder
noncomputable section
open MainTheory.PrimitiveOrderTwoCatAlgebra
open MainTheory.PrimitiveOrderTwoCatCompression
open scoped BigOperators Matrix Kronecker

abbrev PhysicalBasis := Fin 2 × Bits

def spinors (a b : ℝ) : Matrix (Fin 2 × Fin 5) (Fin 2) ℂ :=
  fun ij k => if k=0 then x a b ij.2 ij.1 else y a b ij.2 ij.1

def liftCat : Matrix PhysicalBasis (Fin 2 × Fin 5) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ cats

def encoder (a b : ℝ) : Matrix PhysicalBasis (Fin 2) ℂ := liftCat * spinors a b

theorem encoder_apply (a b : ℝ) (i : Fin 2) (s : Bits) (k : Fin 2) :
    encoder a b (i,s) k =
      ∑ j : Fin 5, (if k=0 then x a b j i else y a b j i) * cats s j := by
  simp [encoder,liftCat,spinors,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.one_apply,ite_mul,mul_comm]

theorem spinors_isometry (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    (spinors a b).conjTranspose * spinors a b=1 := by
  ext q r
  fin_cases q <;> fin_cases r
  all_goals apply Complex.ext
  all_goals norm_num [spinors,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,
    x,y,gamma,delta,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.div_re,Complex.div_im,Complex.star_def,map_ofNat]
  all_goals ring_nf
  all_goals try rw [h_square]
  all_goals nlinarith [hab]

theorem lift_isometry : liftCat.conjTranspose * liftCat = 1 := by
  rw [liftCat,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,orthonormal,Matrix.mul_one,Matrix.one_kronecker_one]

theorem encoder_isometry (a b : ℝ) (hab : 2*a^2+b^2=1/4) :
    (encoder a b).conjTranspose * encoder a b=1 := by
  calc
    _ = (spinors a b).conjTranspose *
        (liftCat.conjTranspose * liftCat) * spinors a b := by
      simp only [encoder,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [lift_isometry,Matrix.mul_one,spinors_isometry a b hab]

theorem lift_compression (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix Bits Bits ℂ) :
    liftCat.conjTranspose * (A ⊗ₖ B) * liftCat =
      A ⊗ₖ (cats.conjTranspose * B * cats) := by
  rw [liftCat,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one]

theorem encoder_compression (a b : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix Bits Bits ℂ) :
    (encoder a b).conjTranspose * (A ⊗ₖ B) * encoder a b =
      (spinors a b).conjTranspose *
        (A ⊗ₖ (cats.conjTranspose * B * cats)) * spinors a b := by
  calc
    _ = (spinors a b).conjTranspose *
        (liftCat.conjTranspose * (A ⊗ₖ B) * liftCat) * spinors a b := by
      simp only [encoder,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by rw [lift_compression]

end
end MainTheory.PrimitiveOrderTwoCatEncoder
