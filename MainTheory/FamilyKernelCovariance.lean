import MainTheory.MixedFamilyTrace

set_option autoImplicit false

namespace MainTheory.FamilyKernelCovariance

open MainTheory.PairPartialTrace MainTheory.MixedFamilyTrace MainTheory.ClassificationLevels

theorem covariance (M : OperatorKernel 6) (psi : Fin 2 → SS.State 6 ℂ) :
    familyKernel (fun i => M.mulVec (psi i))=M*familyKernel psi*M.conjTranspose := by
  have hc : columns (fun i => M.mulVec (psi i))=M*columns psi := by ext x i; rfl
  rw [family_factor,hc,family_factor,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem eigen_preservation (M : OperatorKernel 6) (psi : Fin 2 → SS.State 6 ℂ)
    (lam : Fin 2 → ℂ) (hu : ∀ i,star (lam i)*lam i=1)
    (hM : ∀ i,M.mulVec (psi i)=lam i • psi i) :
    M*familyKernel psi*M.conjTranspose=familyKernel psi := by
  rw [← covariance]
  simp_rw [hM]
  ext x y
  unfold familyKernel
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply,smul_eq_mul,star_mul']
  linear_combination psi i x*star (psi i y)*hu i

theorem fixed_left (M : OperatorKernel 6) (psi : Fin 2 → SS.State 6 ℂ)
    (hM : ∀ i,M.mulVec (psi i)=psi i) : M*familyKernel psi=familyKernel psi := by
  have hc : M*columns psi=columns psi := by
    ext x i
    exact congrFun (hM i) x
  rw [family_factor,← Matrix.mul_assoc,hc]

end MainTheory.FamilyKernelCovariance
