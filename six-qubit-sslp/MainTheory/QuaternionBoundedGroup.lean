import MainTheory.QuaternionQuarterGroup
import MainTheory.QuaternionThirdAxisGroup
import MainTheory.QuaternionThirdOrbit
import MainTheory.QuaternionHalfTurnGroup

/-! A single common Pauli frame for every unit quaternion subgroup with orders at most four. -/

namespace MainTheory.QuaternionBoundedGroup

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionProjectiveOrders MainTheory.QuaternionQuarterPair
  MainTheory.QuaternionQuarterGroup MainTheory.QuaternionThirdGroup
  MainTheory.QuaternionThirdOrbit MainTheory.QuaternionHalfTurnGroup

theorem third_positive_group (G : Subgroup (unitary ℍ[ℝ])) (hG : NoQuarter G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hqre : q.val.re=1/2) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hn : ∃ g∈G,conjugate g q≠q ∧ conjugate g q≠q⁻¹
  · obtain ⟨g,hg,hne,hinv⟩ := hn
    exact third_pair_nonparallel G hG q (conjugate g q) hq
      (conjugate_mem G g q hg hq) hqre (by rw [conjugate_re]; exact hqre) hne hinv
  · have haxis : ∀ g∈G,conjugate g q=q ∨ conjugate g q=q⁻¹ := by
      intro g hg
      by_cases hp : conjugate g q=q
      · exact Or.inl hp
      · right; by_contra hm; exact hn ⟨g,hg,hp,hm⟩
    exact MainTheory.QuaternionThirdAxisGroup.shared_axis G hG q hq hqre haxis

theorem neg_mem (G : Subgroup (unitary ℍ[ℝ])) (hneg : (-1 : unitary ℍ[ℝ])∈G)
    (g : unitary ℍ[ℝ]) (hg : g∈G) : -g∈G := by
  have he : (-1 : unitary ℍ[ℝ])*g= -g := by
    apply Subtype.ext; simp [Unitary.coe_neg]
  exact he ▸ G.mul_mem hneg hg

theorem bounded_group (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (hneg : (-1 : unitary ℍ[ℝ])∈G) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hquarter : ∃ q∈G,2*q.val.re^2=1
  · obtain ⟨q,hq,hqre⟩ := hquarter
    exact quarter_group G hG q hq hqre
  · have hnq : NoQuarter G := by
      intro g hg
      rcases hG g hg with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (hquarter ⟨g,hg,h⟩)
    by_cases hthird : ∃ q∈G,4*q.val.re^2=1
    · obtain ⟨q,hq,hqre⟩ := hthird
      have hz : (q.val.re-1/2)*(q.val.re+1/2)=0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · exact third_positive_group G hnq q hq (by linarith)
      · have hqneg : (-q).val.re=1/2 := by
          simp only [Unitary.coe_neg,Quaternion.re_neg]; linarith
        exact third_positive_group G hnq (-q) (neg_mem G hneg q hq) hqneg
    · apply half_turn_group G
      intro g hg
      rcases hnq g hg with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hthird ⟨g,hg,h⟩)

end

end MainTheory.QuaternionBoundedGroup
