import Orbit2.TensorPauli

/-! Permuting three tensor copies commutes with every simultaneous local matrix. -/

namespace MainTheory.ThreeCopyPermutationCommutant
noncomputable section
open Orbit2.TensorPauli
open scoped BigOperators

abbrev Triple := Fin 3 → Fin 2
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def copies (U : Mat) : Matrix Triple Triple ℂ := tensor (fun _ => U)

def permute (σ : Equiv.Perm (Fin 3)) : Equiv.Perm Triple where
  toFun x := fun i => x (σ i)
  invFun x := fun i => x (σ.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

def permutation (σ : Equiv.Perm (Fin 3)) : Matrix Triple Triple ℂ :=
  fun x y => if x=permute σ y then 1 else 0

theorem copy_entries (σ : Equiv.Perm (Fin 3)) (U : Mat) (x y : Triple) :
    copies U (permute σ x) (permute σ y)=copies U x y := by
  unfold copies tensor permute
  exact Equiv.prod_comp σ (fun i => U (x i) (y i))

theorem commute (σ : Equiv.Perm (Fin 3)) (U : Mat) :
    copies U*permutation σ=permutation σ*copies U := by
  ext x y
  simp only [Matrix.mul_apply, permutation, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_rhs => rw [← Equiv.sum_comp (permute σ).symm]
  simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have he := copy_entries σ U ((permute σ).symm x) y
  simpa only [Equiv.apply_symm_apply] using he

theorem copies_mul (U V : Mat) : copies U*copies V=copies (U*V) :=
  tensor_mul _ _

theorem copies_star (U : Mat) : (copies U).conjTranspose=copies U.conjTranspose :=
  tensor_conjTranspose _

theorem copies_one : copies (1 : Mat)=1 := by
  simpa only [operator, localC_zero] using (operator_zero (n:=3))

theorem copies_unitary (U : Mat) (h : U*U.conjTranspose=1) :
    copies U*(copies U).conjTranspose=1 := by
  rw [copies_star, copies_mul, h, copies_one]

theorem fixed (σ : Equiv.Perm (Fin 3)) (U : Mat) (h : U*U.conjTranspose=1) :
    copies U*permutation σ*(copies U).conjTranspose=permutation σ := by
  rw [commute, Matrix.mul_assoc, copies_unitary U h, Matrix.mul_one]

theorem span_fixed {ι : Type*} [Fintype ι] (s : ι → Equiv.Perm (Fin 3)) (c : ι → ℂ)
    (U : Mat) (h : U*U.conjTranspose=1) :
    copies U*(∑ k,c k • permutation (s k))*(copies U).conjTranspose=
      ∑ k,c k • permutation (s k) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    fixed _ U h]

end
end MainTheory.ThreeCopyPermutationCommutant
