import MainTheory.QuaternionQuarterPlane
import MainTheory.QuaternionAxisNormalizerShape
import MainTheory.QuaternionConjugatedSubgroup

/-! A bounded subgroup sharing a quarter-turn axis has a common Pauli frame. -/

namespace MainTheory.QuaternionQuarterAxisGroup

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionOrthogonalFrame MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionProjectiveOrders MainTheory.QuaternionQuarterPair
  MainTheory.QuaternionQuarterPlane MainTheory.QuaternionAxisNormalizerShape
  MainTheory.QuaternionConjugatedSubgroup

theorem plane_member (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hquarter : 2*q.val.re^2=1) (hsq : q^2=axisI)
    (g : unitary ℍ[ℝ]) (hg : g∈G) (haxis : conjugate g axisI=axisI) : Normalizes g := by
  obtain ⟨hi,hj,hk⟩ := quarter_root_I q hquarter hsq
  obtain ⟨hgj,hgk⟩ := axis_positive_shape g haxis
  have hm := hG (q*g) (G.mul_mem hq hg)
  have hp := hG (q⁻¹*g) (G.mul_mem (G.inv_mem hq) hg)
  change AllowedScalar (q.val*g.val).re at hm
  change AllowedScalar (star q.val*g.val).re at hp
  have hem : (q.val*g.val).re=q.val.re*(g.val.re-g.val.imI) := by
    simp only [Quaternion.re_mul,hi,hj,hk]; ring
  have hep : (star q.val*g.val).re=q.val.re*(g.val.re+g.val.imI) := by
    simp only [Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,
      Quaternion.imJ_star,Quaternion.imK_star,hi,hj,hk]; ring
  rw [hem] at hm
  rw [hep] at hp
  exact plane_normalizes g q.val.re hgj hgk (by linarith) hm hp

theorem axisJ_negative : conjugate axisJ axisI= -axisI := by
  apply Subtype.ext
  rw [conjugate_value]
  apply Quaternion.ext <;> norm_num [axisI,axisJ,Unitary.coe_neg]

theorem with_J (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hquarter : 2*q.val.re^2=1) (hsq : q^2=axisI)
    (hJ : axisJ∈G) (haxis : ∀ g∈G,conjugate g axisI=axisI ∨ conjugate g axisI= -axisI) :
    ∀ g∈G,Normalizes g := by
  intro g hg
  rcases haxis g hg with h | h
  · exact plane_member G hG q hq hquarter hsq g hg h
  · have hpositive : conjugate (axisJ*g) axisI=axisI := by
      rw [conjugate_comp,h,conjugate_neg,axisJ_negative]
      apply Subtype.ext; simp
    have hp := plane_member G hG q hq hquarter hsq (axisJ*g)
      (G.mul_mem hJ hg) hpositive
    have hn := normalizes_mul axisJ⁻¹ (axisJ*g) normalizes_axisJ_inv hp
    simpa only [inv_mul_cancel_left] using hn

theorem shared_axis (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hquarter : 2*q.val.re^2=1) (hsq : q^2=axisI)
    (haxis : ∀ g∈G,conjugate g axisI=axisI ∨ conjugate g axisI= -axisI) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hneg : ∃ g∈G,conjugate g axisI= -axisI
  · obtain ⟨g,hg,hgneg⟩ := hneg
    obtain ⟨hgre,hgI⟩ := axis_negative_shape g hgneg
    have hganti : Anti axisI g := by
      apply MainTheory.QuaternionAxisGeometry.pure_anti_of_dot _ _ axisI_pure hgre
      simp [imaginaryDot,axisI,hgI]
    obtain ⟨u,huI,hug⟩ := fixing_I g hgre hganti
    have hqr : conjugate u q∈rotated G u := rotated_mem G u q hq
    have hqquarter : 2*(conjugate u q).val.re^2=1 := by rw [conjugate_re]; exact hquarter
    have hqsq : (conjugate u q)^2=axisI := by rw [← conjugate_pow,hsq,huI]
    have huJ : axisJ∈rotated G u := hug ▸ rotated_mem G u g hg
    have hrot : ∀ v∈rotated G u,conjugate v axisI=axisI ∨ conjugate v axisI= -axisI := by
      rintro v ⟨w,hw,rfl⟩
      change conjugate (conjugate u w) axisI=axisI ∨
        conjugate (conjugate u w) axisI= -axisI
      rcases haxis w hw with h | h
      · left; rw [← huI,← conjugate_intertwine,h]
      · right; rw [← huI,← conjugate_intertwine,h,conjugate_neg]
    refine ⟨u,?_⟩
    intro v hv
    exact with_J (rotated G u) (rotated_bounded G u hG) (conjugate u q) hqr
      hqquarter hqsq huJ hrot _ (rotated_mem G u v hv)
  · refine ⟨1,?_⟩
    intro g hg
    have hp : conjugate g axisI=axisI := by
      rcases haxis g hg with h | h
      · exact h
      · exact False.elim (hneg ⟨g,hg,h⟩)
    simpa [conjugate] using plane_member G hG q hq hquarter hsq g hg hp

end

end MainTheory.QuaternionQuarterAxisGroup
