import MainTheory.QuaternionQuarterPair

/-! Bounded quarter-turns restrict every rotation in their common axis plane. -/

namespace MainTheory.QuaternionQuarterPlane

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionOrthogonalFrame MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionProjectiveOrders

theorem square_sum (r s : ℝ) (hr : AllowedScalar r) (hs : AllowedScalar s)
    (hn : r^2+s^2=1) : r^2=0 ∨ r^2=1/2 ∨ r^2=1 := by
  rcases hr with hr | hr | hr | hr
  · exact Or.inr (Or.inr hr)
  · exact Or.inl (by rw [hr]; norm_num)
  · rcases hs with hs | hs | hs | hs
    all_goals exfalso; nlinarith
  · exact Or.inr (Or.inl (by linarith))

theorem plane_double_cos (a b c : ℝ) (hn : a^2+b^2=1) (hc : c^2=1/2)
    (hminus : AllowedScalar (c*(a-b))) (hplus : AllowedScalar (c*(a+b))) :
    a^2-b^2=0 ∨ a^2-b^2=1 ∨ a^2-b^2= -1 := by
  have hsq : (c*(a-b))^2+(c*(a+b))^2=1 := by
    simp only [mul_pow,hc]
    nlinarith [hn]
  have hrel : (c*(a-b))^2=(1-2*a*b)/2 := by
    rw [mul_pow,hc]
    nlinarith [hn]
  have hd := square_sum _ _ hminus hplus hsq
  rcases hd with hd | hd | hd
  · have he : a=b := by nlinarith [hrel,sq_nonneg (a-b)]
    exact Or.inl (by rw [he]; ring)
  · have he : a*b=0 := by linarith [hrel]
    rcases mul_eq_zero.mp he with he | he
    · exact Or.inr (Or.inr (by nlinarith [hn]))
    · exact Or.inr (Or.inl (by nlinarith [hn]))
  · have he : a= -b := by nlinarith [hrel,sq_nonneg (a+b)]
    exact Or.inl (by rw [he]; ring)

theorem plane_normalizes (g : unitary ℍ[ℝ]) (c : ℝ)
    (hj : g.val.imJ=0) (hk : g.val.imK=0) (hc : c^2=1/2)
    (hminus : AllowedScalar (c*(g.val.re-g.val.imI)))
    (hplus : AllowedScalar (c*(g.val.re+g.val.imI))) : Normalizes g := by
  have hn := normSq_unitary g
  rw [Quaternion.normSq_def',hj,hk] at hn
  have hunit : g.val.re^2+g.val.imI^2=1 := by nlinarith [hn]
  have hi : conjugate g axisI=axisI := by
    apply Subtype.ext
    rw [conjugate_value]
    apply Quaternion.ext <;> simp [axisI,hj,hk] <;> nlinarith [hunit]
  have hp := conjugate_pure g axisJ axisJ_pure
  have hdi : imaginaryDot (conjugate g axisJ).val axisI.val=0 := by
    rw [conjugate_value]
    simp [imaginaryDot,axisI,axisJ,hj,hk]
  have hdj : imaginaryDot (conjugate g axisJ).val axisJ.val =
      g.val.re^2-g.val.imI^2 := by
    rw [conjugate_value]
    simp [imaginaryDot,axisJ,hj,hk,pow_two]
    ring
  have hir : Related (conjugate g axisJ) axisI :=
    Or.inr (Or.inr (pure_anti_of_dot _ _ hp axisI_pure hdi))
  have hjr : Related (conjugate g axisJ) axisJ := by
    rcases plane_double_cos _ _ c hunit hc hminus hplus with h | h | h
    · exact Or.inr (Or.inr (pure_anti_of_dot _ _ hp axisJ_pure (hdj.trans h)))
    · exact Or.inl (pure_equal_of_dot _ _ hp axisJ_pure (hdj.trans h))
    · exact Or.inr (Or.inl (pure_negative_of_dot _ _ hp axisJ_pure (hdj.trans h)))
  exact normalizes_of_two g (Or.inl hi) (coordinate_axis _ hp hir hjr)

end

end MainTheory.QuaternionQuarterPlane
