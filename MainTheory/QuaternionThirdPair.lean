import MainTheory.QuaternionAxisGeometry

/-! Two nonparallel third-turns generate a perpendicular pair of half-turns. -/

namespace MainTheory.QuaternionThirdPair

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionOrthogonalFrame

theorem rotation_dot (q s : ℍ[ℝ]) (hs : s.re=0) :
    imaginaryDot s (q*s*star q) =
      (q.re^2-imaginaryDot q q)*imaginaryDot s s+2*(imaginaryDot q s)^2 := by
  simp only [imaginaryDot,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,
    Quaternion.imK_star,hs]
  ring

theorem unit_rotation_dot (q s : unitary ℍ[ℝ]) (hs : s.val.re=0) :
    imaginaryDot s.val (conjugate q s).val =
      2*q.val.re^2-1+2*(imaginaryDot q.val s.val)^2 := by
  have hn := normSq_unitary q
  have hm := normSq_unitary s
  rw [Quaternion.normSq_def'] at hn hm
  have hq : imaginaryDot q.val q.val=1-q.val.re^2 := by
    unfold imaginaryDot; nlinarith [hn]
  have hh : imaginaryDot s.val s.val=1 := by
    unfold imaginaryDot; nlinarith [hm]
  rw [conjugate_value,rotation_dot q.val s.val hs,hq,hh]
  ring

theorem product_projection (q p : ℍ[ℝ]) (he : p.re=q.re) :
    imaginaryDot q (q*star p)=q.re*(imaginaryDot q q-imaginaryDot q p) := by
  simp only [imaginaryDot,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star,he]
  ring

theorem perpendicular_pair (q p : unitary ℍ[ℝ])
    (hq : q.val.re=1/2) (hp : p.val.re=1/2)
    (hd : imaginaryDot q.val p.val= -1/4) :
    (q*p⁻¹).val.re=0 ∧ (conjugate q (q*p⁻¹)).val.re=0 ∧
      Anti (q*p⁻¹) (conjugate q (q*p⁻¹)) := by
  have hz : (q*p⁻¹).val.re=0 := by
    change (q.val*star p.val).re=0
    simp only [Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,
      Quaternion.imJ_star,Quaternion.imK_star,hq,hp]
    unfold imaginaryDot at hd
    linarith
  have hn := normSq_unitary q
  rw [Quaternion.normSq_def',hq] at hn
  have hself : imaginaryDot q.val q.val=3/4 := by
    unfold imaginaryDot; nlinarith [hn]
  have hproj : imaginaryDot q.val (q*p⁻¹).val=1/2 := by
    change imaginaryDot q.val (q.val*star p.val)=_
    rw [product_projection q.val p.val (hp.trans hq.symm),hself,hd,hq]
    norm_num
  refine ⟨hz,conjugate_pure q _ hz,?_⟩
  apply pure_anti_of_dot _ _ hz (conjugate_pure q _ hz)
  rw [unit_rotation_dot q _ hz,hproj,hq]
  norm_num

end

end MainTheory.QuaternionThirdPair
