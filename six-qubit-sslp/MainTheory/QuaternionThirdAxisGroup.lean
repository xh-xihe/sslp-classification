import MainTheory.QuaternionThirdCanonicalTargets
import MainTheory.QuaternionCommutingThird
import MainTheory.QuaternionAxisNormalizerShape

/-! One common Clifford basis for the normalizer of a third-turn axis. -/

namespace MainTheory.QuaternionThirdAxisGroup

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionSpinMatrices
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionCommutingThird MainTheory.QuaternionThirdGroup
  MainTheory.QuaternionThirdTraceFrame MainTheory.QuaternionThirdCanonicalTargets
  MainTheory.QuaternionConjugatedSubgroup MainTheory.QuaternionAxisNormalizerShape
  MainTheory.QuaternionOrthogonalFrame

theorem inverting_shape (g q : unitary ℍ[ℝ]) (hq : q.val.re=1/2)
    (h : conjugate g q=q⁻¹) : g.val.re=0 ∧ imaginaryDot q.val g.val=0 := by
  have he := intertwiner g q q⁻¹ h
  have hr := congrArg (fun q : unitary ℍ[ℝ] => q.val.re) he
  have hi := congrArg (fun q : unitary ℍ[ℝ] => q.val.imI) he
  have hj := congrArg (fun q : unitary ℍ[ℝ] => q.val.imJ) he
  have hk := congrArg (fun q : unitary ℍ[ℝ] => q.val.imK) he
  change (g.val*q.val).re=(star q.val*g.val).re at hr
  change (g.val*q.val).imI=(star q.val*g.val).imI at hi
  change (g.val*q.val).imJ=(star q.val*g.val).imJ at hj
  change (g.val*q.val).imK=(star q.val*g.val).imK at hk
  simp only [Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star] at hr
  simp only [Quaternion.imI_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star] at hi
  simp only [Quaternion.imJ_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star] at hj
  simp only [Quaternion.imK_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star] at hk
  have hI : g.val.re*q.val.imI=0 := by linarith [hi]
  have hJ : g.val.re*q.val.imJ=0 := by linarith [hj]
  have hK : g.val.re*q.val.imK=0 := by linarith [hk]
  have hn := normSq_unitary q
  rw [Quaternion.normSq_def',hq] at hn
  have hg : g.val.re=0 := by
    by_cases hqi : q.val.imI=0
    · by_cases hqj : q.val.imJ=0
      · have hqk : q.val.imK≠0 := by intro h; rw [hqi,hqj,h] at hn; norm_num at hn
        exact (mul_eq_zero.mp hK).resolve_right hqk
      · exact (mul_eq_zero.mp hJ).resolve_right hqj
    · exact (mul_eq_zero.mp hI).resolve_right hqi
  refine ⟨hg,?_⟩
  unfold imaginaryDot
  linarith [hr]

theorem bodyHalf_inverts : conjugate bodyHalf bodyThird=bodyThird⁻¹ := by
  apply Subtype.ext
  change bodyHalf.val*bodyThird.val*star bodyHalf.val=star bodyThird.val
  apply Quaternion.ext
  all_goals simp [bodyHalf,bodyThird]
  all_goals nlinarith [halfScale_square]

theorem fixed_body (G : Subgroup (unitary ℍ[ℝ])) (hG : NoQuarter G)
    (hq : bodyThird∈G) (g : unitary ℍ[ℝ]) (hg : g∈G)
    (h : conjugate g bodyThird=bodyThird) : Normalizes g := by
  exact cyclic_normalizes g (cyclic_part bodyThird g bodyThird_re
    (hG g hg) (hG _ (G.mul_mem hq hg)) (intertwiner g _ _ h).symm)

theorem with_bodyHalf (G : Subgroup (unitary ℍ[ℝ])) (hG : NoQuarter G)
    (hq : bodyThird∈G) (hp : bodyHalf∈G)
    (haxis : ∀ g∈G,conjugate g bodyThird=bodyThird ∨ conjugate g bodyThird=bodyThird⁻¹) :
    ∀ g∈G,Normalizes g := by
  intro g hg
  rcases haxis g hg with h | h
  · exact fixed_body G hG hq g hg h
  · have hfix : conjugate (bodyHalf*g) bodyThird=bodyThird := by
      rw [conjugate_comp,h,conjugate_inv,bodyHalf_inverts,inv_inv]
    have hn := fixed_body G hG hq (bodyHalf*g) (G.mul_mem hp hg) hfix
    have he := normalizes_mul bodyHalf⁻¹ (bodyHalf*g) bodyHalf_inverse_normalizes hn
    simpa only [inv_mul_cancel_left] using he

theorem shared_axis (G : Subgroup (unitary ℍ[ℝ])) (hG : NoQuarter G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hqre : q.val.re=1/2)
    (haxis : ∀ g∈G,conjugate g q=q ∨ conjugate g q=q⁻¹) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hneg : ∃ g∈G,conjugate g q=q⁻¹
  · obtain ⟨p,hp,hinv⟩ := hneg
    obtain ⟨hpre,horth⟩ := inverting_shape p q hqre hinv
    obtain ⟨u,huq,hup⟩ := third_half_frame q p bodyThird bodyHalf hqre hpre
      bodyThird_re bodyHalf_re horth target_orthogonal
    have hqrot : bodyThird∈rotated G u := huq ▸ rotated_mem G u q hq
    have hprot : bodyHalf∈rotated G u := hup ▸ rotated_mem G u p hp
    have hrot : ∀ g∈rotated G u,
        conjugate g bodyThird=bodyThird ∨ conjugate g bodyThird=bodyThird⁻¹ := by
      rintro g ⟨v,hv,rfl⟩
      change conjugate (conjugate u v) bodyThird=bodyThird ∨
        conjugate (conjugate u v) bodyThird=bodyThird⁻¹
      rcases haxis v hv with h | h
      · left; rw [← huq,← conjugate_intertwine,h]
      · right; rw [← huq,← conjugate_intertwine,h,conjugate_inv]
    refine ⟨u,?_⟩
    intro g hg
    exact with_bodyHalf (rotated G u) (noQuarter_rotated G u hG) hqrot hprot hrot
      _ (rotated_mem G u g hg)
  · obtain ⟨u,hu⟩ := same_trace_frame q bodyThird hqre bodyThird_re
    refine ⟨u,?_⟩
    intro g hg
    have hfix : conjugate g q=q := by
      rcases haxis g hg with h | h
      · exact h
      · exact False.elim (hneg ⟨g,hg,h⟩)
    have hbody : conjugate (conjugate u g) bodyThird=bodyThird := by
      rw [← hu,← conjugate_intertwine,hfix]
    exact fixed_body (rotated G u) (noQuarter_rotated G u hG)
      (hu ▸ rotated_mem G u q hq) _ (rotated_mem G u g hg) hbody

end

end MainTheory.QuaternionThirdAxisGroup
