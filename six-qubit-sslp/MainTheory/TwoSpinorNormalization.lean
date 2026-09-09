import SixQubit.Spinor

set_option autoImplicit false

namespace MainTheory.TwoSpinorNormalization

abbrev Vec := Fin 2 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def basisMatrix (u : Vec) : Mat :=
  !![star (u 0), star (u 1); -u 1, u 0]

theorem basis_unitary (u : Vec) (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 1) :
    basisMatrix u * (basisMatrix u).conjTranspose = 1 := by
  have hC : star (u 0)*u 0 + star (u 1)*u 1 = 1 := by
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add,hu]
    rfl
  simp only [Complex.star_def] at hC
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
  all_goals try { exact hC }
  all_goals try { solve | ring }
  all_goals linear_combination hC

theorem basis_sends_first (u : Vec)
    (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 1) :
    (basisMatrix u).mulVec u = ![1,0] := by
  have hC : star (u 0)*u 0 + star (u 1)*u 1 = 1 := by
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add,hu]
    rfl
  funext i
  fin_cases i <;> simp [basisMatrix,Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · exact hC
  · ring

theorem basis_preserves_norm (u v : Vec)
    (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 1)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    Complex.normSq ((basisMatrix u).mulVec v 0) +
      Complex.normSq ((basisMatrix u).mulVec v 1) = 1 := by
  have h := SixQubit.Spinor.lagrange (u 0) (u 1) (v 0) (v 1)
  rw [hu,hv,one_mul] at h
  simpa [basisMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_add_neg,
    mul_comm,add_comm] using h

theorem exists_phase_correction (z : ℂ) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ a*z = (‖z‖ : ℂ) := by
  refine ⟨Complex.exp (-((Complex.arg z : ℂ)*Complex.I)), ?_, ?_⟩
  · simp [Complex.normSq_eq_norm_sq,Complex.norm_exp]
  · conv_lhs => arg 2; rw [← Complex.norm_mul_exp_arg_mul_I z]
    simp [Complex.exp_neg,mul_comm]

theorem diagonal_unitary (a b : ℂ) (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) :
    (Matrix.diagonal ![a,b]) * (Matrix.diagonal ![a,b]).conjTranspose = 1 := by
  have h : ∀ i : Fin 2, (![a,b] i)*star (![a,b] i) = 1 := by
    intro i
    fin_cases i
    · change a*star a = 1
      rw [mul_comm,SixQubit.star_mul_self,ha]
      rfl
    · change b*star b = 1
      rw [mul_comm,SixQubit.star_mul_self,hb]
      rfl
  rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    exact h i
  · simp [hij]

end MainTheory.TwoSpinorNormalization
