import MainTheory.QuaternionQuarterAxisGroup

/-! Common Pauli basis for every bounded-order subgroup containing a quarter-turn. -/

namespace MainTheory.QuaternionQuarterGroup

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionQuarterPair MainTheory.QuaternionConjugatedSubgroup
  MainTheory.QuaternionQuarterAxisGroup

theorem quarter_group (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hquarter : 2*q.val.re^2=1) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hn : ∃ v∈G,(conjugate v q)^2≠q^2 ∧ (conjugate v q)^2≠ -(q^2)
  · obtain ⟨v,hv,hp,hm⟩ := hn
    exact nonparallel_orbit G hG q hq hquarter v hv hp hm
  · have haxis : ∀ g∈G,conjugate g (q^2)=q^2 ∨ conjugate g (q^2)= -(q^2) := by
      intro g hg
      rw [conjugate_pow]
      by_cases hp : (conjugate g q)^2=q^2
      · exact Or.inl hp
      · right
        by_contra hm
        exact hn ⟨g,hg,hp,hm⟩
    obtain ⟨v,hv⟩ := any_axis (q^2) axisI (quarter_square_pure q hquarter) axisI_pure
    have hqsq : (conjugate v q)^2=axisI := by rw [← conjugate_pow,hv]
    have hqquarter : 2*(conjugate v q).val.re^2=1 := by rw [conjugate_re]; exact hquarter
    have hrot : ∀ g∈rotated G v,conjugate g axisI=axisI ∨ conjugate g axisI= -axisI := by
      rintro g ⟨w,hw,rfl⟩
      change conjugate (conjugate v w) axisI=axisI ∨
        conjugate (conjugate v w) axisI= -axisI
      rcases haxis w hw with h | h
      · left; rw [← hv,← conjugate_intertwine,h]
      · right; rw [← hv,← conjugate_intertwine,h,conjugate_neg]
    obtain ⟨u,hu⟩ := shared_axis (rotated G v) (rotated_bounded G v hG)
      (conjugate v q) (rotated_mem G v q hq) hqquarter hqsq hrot
    refine ⟨u*v,?_⟩
    intro g hg
    rw [conjugate_comp]
    exact hu _ (rotated_mem G v g hg)

end

end MainTheory.QuaternionQuarterGroup
