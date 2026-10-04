import MainTheory.QuaternionThirdGroup

/-! Explicit common frames for a third-turn and a perpendicular half-turn. -/

namespace MainTheory.QuaternionThirdTraceFrame

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionOrthogonalFrame MainTheory.QuaternionCliffordAxes

def scale : ℝ := 2/Real.sqrt 3

theorem scale_square : scale^2=4/3 := by
  unfold scale
  rw [div_pow,Real.sq_sqrt (by norm_num)]
  norm_num

theorem scale_ne : scale≠0 := by
  intro h
  have hs := scale_square
  rw [h] at hs
  norm_num at hs

def imaginary (q : ℍ[ℝ]) : ℍ[ℝ] := ⟨0,q.imI,q.imJ,q.imK⟩

theorem imaginary_norm (q : unitary ℍ[ℝ]) (hq : q.val.re=1/2) :
    Quaternion.normSq (imaginary q.val)=3/4 := by
  have hn := normSq_unitary q
  simp only [Quaternion.normSq_def',imaginary,hq] at *
  nlinarith

def axis (q : unitary ℍ[ℝ]) (hq : q.val.re=1/2) : unitary ℍ[ℝ] :=
  ⟨scale • imaginary q.val,by
    have hn : Quaternion.normSq (scale • imaginary q.val)=1 := by
      rw [Quaternion.normSq_smul,scale_square,imaginary_norm q hq]
      norm_num
    constructor
    · rw [Quaternion.star_mul_self,hn]; rfl
    · rw [Quaternion.self_mul_star,hn]; rfl⟩

theorem axis_pure (q : unitary ℍ[ℝ]) (hq : q.val.re=1/2) : (axis q hq).val.re=0 := by
  simp [axis,imaginary]

theorem conjugate_real (u : unitary ℍ[ℝ]) (a : ℝ) :
    u.val*(a : ℍ[ℝ])*star u.val=(a : ℍ[ℝ]) := by
  rw [Quaternion.mul_coe_eq_smul,smul_mul_assoc,u.property.2]
  apply Quaternion.ext <;> simp

theorem actual_of_axis (u q t : unitary ℍ[ℝ]) (hq : q.val.re=1/2) (ht : t.val.re=1/2)
    (h : conjugate u (axis q hq)=axis t ht) : conjugate u q=t := by
  have hv := congrArg Subtype.val h
  change u.val*(scale • imaginary q.val)*star u.val=scale • imaginary t.val at hv
  rw [mul_smul_comm,smul_mul_assoc] at hv
  have he := congrArg (fun p : ℍ[ℝ] => scale⁻¹ • p) hv
  simp only [smul_smul,inv_mul_cancel₀ scale_ne,one_smul] at he
  have hqdec : q.val=(1/2 : ℝ)+imaginary q.val := by
    apply Quaternion.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,
      Quaternion.imJ_add,Quaternion.imK_add,Quaternion.re_coe,Quaternion.imI_coe,
      Quaternion.imJ_coe,Quaternion.imK_coe,imaginary,hq,zero_add,add_zero]
  have htdec : t.val=(1/2 : ℝ)+imaginary t.val := by
    apply Quaternion.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,
      Quaternion.imJ_add,Quaternion.imK_add,Quaternion.re_coe,Quaternion.imI_coe,
      Quaternion.imJ_coe,Quaternion.imK_coe,imaginary,ht,zero_add,add_zero]
  apply Subtype.ext
  rw [conjugate_value,hqdec,htdec,mul_add,add_mul,conjugate_real,he]

theorem same_trace_frame (q t : unitary ℍ[ℝ]) (hq : q.val.re=1/2) (ht : t.val.re=1/2) :
    ∃ u : unitary ℍ[ℝ],conjugate u q=t := by
  obtain ⟨u,hu⟩ := any_axis (axis q hq) (axis t ht) (axis_pure q hq) (axis_pure t ht)
  exact ⟨u,actual_of_axis u q t hq ht hu⟩

theorem axis_anti (q p : unitary ℍ[ℝ]) (hq : q.val.re=1/2) (hp : p.val.re=0)
    (hd : imaginaryDot q.val p.val=0) : Anti (axis q hq) p := by
  apply pure_anti_of_dot _ _ (axis_pure q hq) hp
  change imaginaryDot (scale • imaginary q.val) p.val=0
  unfold imaginaryDot at hd ⊢
  simp only [Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul,
    imaginary,smul_eq_mul]
  linear_combination scale*hd

theorem cancel_conjugate (u p : unitary ℍ[ℝ]) : conjugate u⁻¹ (conjugate u p)=p := by
  simp only [conjugate,inv_inv]
  group

theorem ordered_axes_to (s p t r : unitary ℍ[ℝ])
    (hs : s.val.re=0) (hp : p.val.re=0) (ht : t.val.re=0) (hr : r.val.re=0)
    (hsp : Anti s p) (htr : Anti t r) :
    ∃ u : unitary ℍ[ℝ],conjugate u s=t ∧ conjugate u p=r := by
  obtain ⟨u,huI,huJ⟩ := ordered_frame s p hs hp hsp
  obtain ⟨v,hvI,hvJ⟩ := ordered_frame t r ht hr htr
  refine ⟨v⁻¹*u,?_,?_⟩
  · rw [conjugate_comp,huI,← hvI,cancel_conjugate]
  · rw [conjugate_comp,huJ,← hvJ,cancel_conjugate]

theorem third_half_frame (q p t r : unitary ℍ[ℝ])
    (hq : q.val.re=1/2) (hp : p.val.re=0) (ht : t.val.re=1/2) (hr : r.val.re=0)
    (hqp : imaginaryDot q.val p.val=0) (htr : imaginaryDot t.val r.val=0) :
    ∃ u : unitary ℍ[ℝ],conjugate u q=t ∧ conjugate u p=r := by
  obtain ⟨u,huq,hup⟩ := ordered_axes_to (axis q hq) p (axis t ht) r
    (axis_pure q hq) hp (axis_pure t ht) hr (axis_anti q p hq hp hqp) (axis_anti t r ht hr htr)
  exact ⟨u,actual_of_axis u q t hq ht huq,hup⟩

end

end MainTheory.QuaternionThirdTraceFrame
