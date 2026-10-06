import MainTheory.Orbit8SpinSemantics
import MainTheory.Orbit8EnumeratorDisplays

set_option autoImplicit false

namespace MainTheory.Orbit8SpinProjector

open SixQubit.Orbit8Universal MainTheory.PairPartialTrace

def complementEquiv : SS.BitString 6 ≃ SS.BitString 6 where
  toFun := SS.complement
  invFun := SS.complement
  left_inv := SS.complement_complement
  right_inv := SS.complement_complement

noncomputable def spinConjugate (A : Matrix (SS.BitString 6) (SS.BitString 6) ℂ) :
    Matrix (SS.BitString 6) (SS.BitString 6) ℂ := fun x y =>
  (spinSign x : ℂ)*(spinSign y : ℂ)*star (A (SS.complement x) (SS.complement y))

theorem star_sign (x : SS.BitString 6) : star (spinSign x : ℂ)=(spinSign x : ℂ) := by
  unfold spinSign
  split_ifs <;> norm_num

theorem spin_conjugate_action (A : Matrix (SS.BitString 6) (SS.BitString 6) ℂ)
    (f : SS.State 6 ℂ) : spinJ (A.mulVec (spinJ f))=(spinConjugate A).mulVec f := by
  funext x
  simp only [spinJ,Matrix.mulVec,dotProduct]
  rw [star_sum,Finset.mul_sum,← complementEquiv.sum_comp]
  simp only [complementEquiv,Equiv.coe_fn_mk,SS.complement_complement,
    spinSign_complement,star_mul,star_star,star_sign]
  apply Finset.sum_congr rfl
  intro y _
  unfold spinConjugate
  ring

theorem family_star (psi : Fin 2 → SS.State 6 ℂ) (x y : SS.BitString 6) :
    star (familyKernel psi x y)=familyKernel psi y x := by
  unfold familyKernel
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul,star_star]

theorem spin_family (psi : Fin 2 → SS.State 6 ℂ) :
    spinConjugate (familyKernel psi)=familyKernel (fun i => spinJ (psi i)) := by
  ext x y
  simp only [spinConjugate,familyKernel,spinJ,star_sum,star_mul,star_star,star_sign,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spinSign_psign (x : SS.BitString 6) :
    (spinSign x : ℂ)= -((SS.Shadow.psign x : ℝ) : ℂ) := by
  have hp : SS.Shadow.psign x=(-1 : ℝ)^SS.hammingWt x := by
    simp [SS.Shadow.psign,SS.MacWilliams.chi_eq_pow,SS.ones,SS.hammingWt]
  rw [MainTheory.Orbit8SpinSemantics.spinSign_power,hp]
  push_cast
  rw [pow_succ]
  ring

theorem trace_core (psi : Fin 2 → SS.State 6 ℂ) :
    Matrix.trace (familyKernel psi*spinConjugate (familyKernel psi))=SS.Shadow.core psi := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,spinConjugate,
    family_star,spinSign_psign]
  unfold SS.Shadow.core SS.MacWilliams.RR familyKernel
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem spinflip_enumerator (psi : Fin 2 → SS.State 6 ℂ) :
    Matrix.trace (familyKernel psi*spinConjugate (familyKernel psi))=
      (1/16 : ℂ)*((∑ j : Fin 7,(-1 : ℝ)^j.val*
        MainTheory.Orbit8EnumeratorDisplays.normalizedA psi j.val : ℝ) : ℂ) := by
  have h := SS.Shadow.alt_sum_eq_core psi
  rw [← Complex.ofReal_sum,SS.Shadow.alt_sum_as_Aco,← trace_core] at h
  norm_num [Finset.sum_range_succ] at h
  norm_num [Fin.sum_univ_succ,MainTheory.Orbit8EnumeratorDisplays.normalizedA]
  linear_combination -h/64

theorem trace_nonnegative (psi : Fin 2 → SS.State 6 ℂ) :
    0 ≤ (Matrix.trace (familyKernel psi*spinConjugate (familyKernel psi))).re := by
  rw [trace_core,(SS.Shadow.core_eq_nonneg_real psi).1,Complex.ofReal_re]
  exact (SS.Shadow.core_eq_nonneg_real psi).2

end MainTheory.Orbit8SpinProjector
