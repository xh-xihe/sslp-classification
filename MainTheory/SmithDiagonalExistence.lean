import MainTheory.SharpClearing

/-! # Integral diagonal reduction of a nonsingular square matrix

This module extracts actual invertible integral change-of-basis matrices
from the PID submodule theorem. The divisibility-chain refinement is a
separate obligation; an arbitrary diagonal reduction is not called a
normalized Smith witness.
-/

namespace MainTheory.SmithExistence

open Module

noncomputable section

variable {s : Type*} [Fintype s] [DecidableEq s]

theorem mulVec_injective_of_det_ne_zero (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    Function.Injective C.mulVec := by
  intro v w hvw
  have h := congrArg C.adjugate.mulVec hvw
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h
  funext i
  exact mul_left_cancel₀ hC (congrFun h i)

/-- A genuine integral diagonal reduction, with both inverses of both
change-of-basis matrices and nonzero diagonal entries. -/
structure DiagonalReduction (C : Matrix s s ℤ) where
  entry : s → ℤ
  entry_ne_zero : ∀ i, entry i ≠ 0
  U : Matrix s s ℤ
  Uinv : Matrix s s ℤ
  V : Matrix s s ℤ
  Vinv : Matrix s s ℤ
  U_mul_Uinv : U * Uinv = 1
  Uinv_mul_U : Uinv * U = 1
  V_mul_Vinv : V * Vinv = 1
  Vinv_mul_V : Vinv * V = 1
  reduction : U * C * V = Matrix.diagonal entry

theorem exists_diagonalReduction (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    Nonempty (DiagonalReduction C) := by
  let f := Matrix.toLin' C
  have hf : Function.Injective f := mulVec_injective_of_det_ne_zero C hC
  let e := LinearEquiv.ofInjective f hf
  let b := Pi.basisFun ℤ s
  have hr : Module.finrank ℤ f.range = Module.finrank ℤ (s → ℤ) := e.symm.finrank_eq
  obtain ⟨bM, a, bN, hab⟩ := f.range.exists_smith_normal_form_of_rank_eq b hr
  let bD := bN.map e.symm
  have hfd (j : s) : f (bD j) = a j • bM j := by
    have he : e (bD j) = bN j := e.apply_symm_apply (bN j)
    have hev := congrArg Subtype.val he
    simpa only [LinearEquiv.ofInjective_apply] using hev.trans (hab j)
  have ha (j : s) : a j ≠ 0 := by
    intro haj
    have hb := hab j
    rw [haj, zero_smul] at hb
    exact bN.ne_zero j (Subtype.ext hb)
  refine ⟨⟨a, ha, bM.toMatrix b, b.toMatrix bM, b.toMatrix bD, bD.toMatrix b,
    bM.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip bM,
    b.toMatrix_mul_toMatrix_flip bD, bD.toMatrix_mul_toMatrix_flip b, ?_⟩⟩
  have hmat : LinearMap.toMatrix b b f = C := by
    simp [f, b]
  rw [← hmat]
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  simp only [LinearMap.toMatrix_apply, hfd, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

end

end MainTheory.SmithExistence
