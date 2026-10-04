import MainTheory.QuaternionAxisFrames

/-! One common unitary frame for an ordered pair of perpendicular axes. -/

namespace MainTheory.QuaternionOrthogonalFrame

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionAxisConjugation

def Anti (s t : unitary ℍ[ℝ]) : Prop := s*t = -(t*s)

theorem conjugate_mul (u s t : unitary ℍ[ℝ]) :
    conjugate u (s*t)=conjugate u s*conjugate u t := by
  simp only [conjugate]
  group

theorem conjugate_neg (u s : unitary ℍ[ℝ]) :
    conjugate u (-s) = -(conjugate u s) := by
  apply Subtype.ext
  simp [conjugate,Unitary.coe_neg]

theorem conjugate_anti (u s t : unitary ℍ[ℝ]) (h : Anti s t) :
    Anti (conjugate u s) (conjugate u t) := by
  unfold Anti at *
  rw [← conjugate_mul, h, conjugate_neg,conjugate_mul]

theorem anti_I_coordinate (p : unitary ℍ[ℝ]) (hp : Anti axisI p) :
    p.val.imI=0 := by
  have he := congrArg (fun q : unitary ℍ[ℝ] => q.val.re) hp
  simp [axisI,Unitary.coe_neg] at he
  linarith

theorem fixing_I (p : unitary ℍ[ℝ]) (hp : p.val.re=0) (ha : Anti axisI p) :
    ∃ u : unitary ℍ[ℝ],conjugate u axisI=axisI ∧ conjugate u p=axisJ := by
  by_cases h : p.val = -axisJ.val
  · refine ⟨axisI,?_,?_⟩
    · simp [conjugate]
    · apply Subtype.ext
      rw [conjugate_value,h]
      apply Quaternion.ext <;> norm_num [axisI,axisJ]
  · let r : ℍ[ℝ] := 1-axisJ.val*p.val
    have hr : r≠0 := raw_intertwiner_ne_zero p axisJ hp h
    let u := normalize r hr
    have hi := anti_I_coordinate p ha
    have hc : r*axisI.val=axisI.val*r := by
      apply Quaternion.ext <;> simp [r,axisI,axisJ,hp,hi]
    have huI : u.val*axisI.val=axisI.val*u.val := by
      change ((Real.sqrt (Quaternion.normSq r))⁻¹ • r)*axisI.val =
        axisI.val*((Real.sqrt (Quaternion.normSq r))⁻¹ • r)
      rw [smul_mul_assoc,mul_smul_comm,hc]
    have hup : u.val*p.val=axisJ.val*u.val := by
      change ((Real.sqrt (Quaternion.normSq r))⁻¹ • r)*p.val =
        axisJ.val*((Real.sqrt (Quaternion.normSq r))⁻¹ • r)
      rw [smul_mul_assoc,mul_smul_comm]
      exact congrArg (fun q : ℍ[ℝ] => (Real.sqrt (Quaternion.normSq r))⁻¹ • q)
        (raw_intertwiner p axisJ hp axisJ_pure)
    refine ⟨u,?_,?_⟩ <;> apply Subtype.ext <;> rw [conjugate_value]
    · rw [huI,mul_assoc,u.property.2,mul_one]
    · rw [hup,mul_assoc,u.property.2,mul_one]

theorem ordered_frame (s t : unitary ℍ[ℝ])
    (hs : s.val.re=0) (ht : t.val.re=0) (ha : Anti s t) :
    ∃ u : unitary ℍ[ℝ],conjugate u s=axisI ∧ conjugate u t=axisJ := by
  obtain ⟨v,hv⟩ := any_axis s axisI hs axisI_pure
  have hp := conjugate_pure v t ht
  have hanti := conjugate_anti v s t ha
  rw [hv] at hanti
  obtain ⟨w,hwI,hwt⟩ := fixing_I (conjugate v t) hp hanti
  refine ⟨w*v,?_,?_⟩
  · rw [conjugate_comp,hv,hwI]
  · rw [conjugate_comp,hwt]

end

end MainTheory.QuaternionOrthogonalFrame
