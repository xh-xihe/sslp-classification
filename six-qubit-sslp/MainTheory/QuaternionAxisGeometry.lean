import MainTheory.QuaternionOrthogonalFrame
import MainTheory.QuaternionAxisAngles

/-! Exact Euclidean relations between unit quaternion axes. -/

namespace MainTheory.QuaternionAxisGeometry

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisAngles
  MainTheory.QuaternionProjectiveOrders

theorem scalar_comm (p q : ℍ[ℝ]) : (p*q).re=(q*p).re := by
  simp only [Quaternion.re_mul]
  ring

theorem conjugate_re (u q : unitary ℍ[ℝ]) :
    (conjugate u q).val.re=q.val.re := by
  rw [conjugate_value,scalar_comm,← mul_assoc,u.property.1,one_mul]

theorem pure_equal_of_dot (s t : unitary ℍ[ℝ])
    (hs : s.val.re=0) (ht : t.val.re=0) (h : imaginaryDot s.val t.val=1) : s=t := by
  have hn := normSq_unitary s
  have hm := normSq_unitary t
  rw [Quaternion.normSq_def',hs] at hn
  rw [Quaternion.normSq_def',ht] at hm
  unfold imaginaryDot at h
  have hI : s.val.imI=t.val.imI := by
    nlinarith [sq_nonneg (s.val.imJ-t.val.imJ),sq_nonneg (s.val.imK-t.val.imK)]
  have hJ : s.val.imJ=t.val.imJ := by
    nlinarith [sq_nonneg (s.val.imI-t.val.imI),sq_nonneg (s.val.imK-t.val.imK)]
  have hK : s.val.imK=t.val.imK := by
    nlinarith [sq_nonneg (s.val.imI-t.val.imI),sq_nonneg (s.val.imJ-t.val.imJ)]
  apply Subtype.ext
  apply Quaternion.ext <;> simp_all

theorem pure_negative_of_dot (s t : unitary ℍ[ℝ])
    (hs : s.val.re=0) (ht : t.val.re=0) (h : imaginaryDot s.val t.val= -1) : s= -t := by
  apply pure_equal_of_dot s (-t) hs
  · simpa [Unitary.coe_neg] using ht
  · simp only [imaginaryDot,Unitary.coe_neg,Quaternion.imI_neg,Quaternion.imJ_neg,
      Quaternion.imK_neg]
    unfold imaginaryDot at h
    linarith

theorem pure_anti_of_dot (s t : unitary ℍ[ℝ])
    (hs : s.val.re=0) (ht : t.val.re=0) (h : imaginaryDot s.val t.val=0) : Anti s t := by
  apply Subtype.ext
  change s.val*t.val= -(t.val*s.val)
  apply Quaternion.ext
  · simp only [Quaternion.re_neg,Quaternion.re_mul,hs,ht]
    unfold imaginaryDot at h
    linarith
  all_goals simp [hs,ht]; ring

def Related (s t : unitary ℍ[ℝ]) : Prop := s=t ∨ s= -t ∨ Anti s t

theorem related_of_dot (s t : unitary ℍ[ℝ]) (hs : s.val.re=0) (ht : t.val.re=0)
    (h : imaginaryDot s.val t.val=1 ∨ imaginaryDot s.val t.val=0 ∨
      imaginaryDot s.val t.val= -1) : Related s t := by
  rcases h with h | h | h
  · exact Or.inl (pure_equal_of_dot s t hs ht h)
  · exact Or.inr (Or.inr (pure_anti_of_dot s t hs ht h))
  · exact Or.inr (Or.inl (pure_negative_of_dot s t hs ht h))

theorem quarter_square_pure (q : unitary ℍ[ℝ]) (hq : 2*q.val.re^2=1) :
    (q^2).val.re=0 := by
  have hn := normSq_unitary q
  rw [Quaternion.normSq_def'] at hn
  rw [pow_two]
  change (q.val*q.val).re=0
  simp only [Quaternion.re_mul]
  nlinarith [hn,hq]

theorem quarter_square_dot (p q : unitary ℍ[ℝ]) (he : p.val.re=q.val.re)
    (hq : 2*q.val.re^2=1) :
    imaginaryDot (p^2).val (q^2).val=2*imaginaryDot p.val q.val := by
  change imaginaryDot (p.val^2) (q.val^2)=_
  obtain ⟨hI,hJ,hK⟩ := square_im p.val
  obtain ⟨kI,kJ,kK⟩ := square_im q.val
  simp only [imaginaryDot,hI,hJ,hK,kI,kJ,kK,he]
  nlinarith [congrArg (fun x : ℝ => x*(p.val.imI*q.val.imI+p.val.imJ*q.val.imJ+
    p.val.imK*q.val.imK)) hq]

theorem quarter_related (p q : unitary ℍ[ℝ]) (he : p.val.re=q.val.re)
    (hq : 2*q.val.re^2=1) (hpq : AllowedScalar (p*q).val.re)
    (hpqs : AllowedScalar (p*q⁻¹).val.re) : Related (p^2) (q^2) := by
  have hp : 2*p.val.re^2=1 := by rw [he]; exact hq
  apply related_of_dot _ _ (quarter_square_pure p hp) (quarter_square_pure q hq)
  rw [quarter_square_dot p q he hq]
  have hd := quarter_relative_dot p.val q.val he hq hpq hpqs
  rcases hd with hd | hd | hd
  · left; linarith
  · right; left; linarith
  · right; right; linarith

def CoordinateAxis (s : unitary ℍ[ℝ]) : Prop :=
  s=axisI ∨ s= -axisI ∨ s=axisJ ∨ s= -axisJ ∨ s=axisK ∨ s= -axisK

theorem coordinate_axis (s : unitary ℍ[ℝ]) (hs : s.val.re=0)
    (hi : Related s axisI) (hj : Related s axisJ) : CoordinateAxis s := by
  rcases hi with hi | hi | hi
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  rcases hj with hj | hj | hj
  · exact Or.inr (Or.inr (Or.inl hj))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hj)))
  have hI := anti_I_coordinate s (by
    apply Subtype.ext
    have hv := congrArg Subtype.val hi
    simpa [Anti,Unitary.coe_neg] using (congrArg Neg.neg hv).symm)
  have hJ : s.val.imJ=0 := by
    have he := congrArg (fun q : unitary ℍ[ℝ] => q.val.re) hj
    simp [axisJ,Unitary.coe_neg] at he
    linarith
  have hn := normSq_unitary s
  rw [Quaternion.normSq_def',hs,hI,hJ] at hn
  have hk : s.val.imK=1 ∨ s.val.imK= -1 := by
    have hz : (s.val.imK-1)*(s.val.imK+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · left; linarith
    · right; linarith
  rcases hk with hk | hk
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      apply Subtype.ext; apply Quaternion.ext <;> simp [axisK,hs,hI,hJ,hk])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      apply Subtype.ext; apply Quaternion.ext <;> simp [axisK,hs,hI,hJ,hk,Unitary.coe_neg])))))

end

end MainTheory.QuaternionAxisGeometry
