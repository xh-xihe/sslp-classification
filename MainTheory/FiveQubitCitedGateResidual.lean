import MainTheory.FiveQubitCitedGateData

set_option autoImplicit false

namespace MainTheory.FiveQubitCitedGateResidual

open SixQubit.Realize MainTheory.ExactZQFinite MainTheory.FiveQubitCitedGateData

noncomputable def word (i : Fin 2) : Fin 32 → ℂ := fun x => toC (rawWord i x)
noncomputable def image (i : Fin 2) : Fin 32 → ℂ := fun x => toC (imageWord i x)
noncomputable def gate : Matrix (Fin 32) (Fin 32) ℂ := fun x y => toC (kernel x y)
noncomputable def normConstant : ℂ := 192-64*(Real.sqrt 3 : ℂ)

theorem normConstant_value : toC (z8 192 0 (-64) 0 0 0 0 0)=normConstant := by
  apply Complex.ext <;> norm_num [toC,toCre,toCim,rz,SS.rp,z8,normConstant]
  ring

theorem image_normConstant : toC (z8 12288 0 (-4096) 0 0 0 0 0)=64*normConstant := by
  apply Complex.ext <;> norm_num [toC,toCre,toCim,rz,SS.rp,z8,normConstant]
  ring

theorem normConstant_ne_zero : normConstant ≠ 0 := by
  have hr : Real.sqrt (3 : ℝ)<3 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  intro h
  have h' := congrArg Complex.re h
  norm_num [normConstant] at h'
  linarith

theorem actual_image (i : Fin 2) : gate.mulVec (word i)=image i := by
  ext x
  simpa only [gate,word,image,Matrix.mulVec,dotProduct,toC_sum,toC_mul] using
    (congrArg toC (imageWord_checked i x)).symm

theorem orthogonal (i j : Fin 2) : (∑ x,star (word i x)*image j x)=0 := by
  simpa only [word,image,toC_sum,toC_mul,toC_conj,toC_zero] using
    congrArg toC (orthogonal_checked i j)

theorem gram (i j : Fin 2) : (∑ x,star (word i x)*word j x)=if i=j then normConstant else 0 := by
  have h := congrArg toC (gram_checked i j)
  simpa only [word,toC_sum,toC_mul,toC_conj,apply_ite,toC_zero,normConstant_value] using h

theorem image_gram (i j : Fin 2) :
    (∑ x,star (image i x)*image j x)=if i=j then 64*normConstant else 0 := by
  have h := congrArg toC (image_gram_checked i j)
  simpa only [image,toC_sum,toC_mul,toC_conj,apply_ite,toC_zero,image_normConstant] using h

theorem image_not_in_span : ¬ ∃ a : Fin 2 → ℂ,
    gate.mulVec (word 0)=fun x => ∑ j,a j*word j x := by
  rintro ⟨a,ha⟩
  rw [actual_image] at ha
  have hzero (i : Fin 2) : a i=0 := by
    have h := orthogonal i 0
    rw [ha] at h
    simp only [Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    have hh : (∑ j,∑ x,star (word i x)*(a j*word j x))=
        ∑ j,a j*(if i=j then normConstant else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← gram]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hh] at h
    simp only [mul_ite,mul_zero] at h
    have h : a i*normConstant=0 := by simpa using h
    exact (mul_eq_zero.mp h).resolve_right normConstant_ne_zero
  have him : image 0=0 := by ext x; simp [ha,hzero]
  have h := image_gram 0 0
  simp [him] at h
  exact normConstant_ne_zero (by simpa using h)

end MainTheory.FiveQubitCitedGateResidual
