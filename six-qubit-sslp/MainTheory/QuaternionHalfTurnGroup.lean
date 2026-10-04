import MainTheory.QuaternionThirdGroup

/-! One common Pauli frame for subgroups with projective orders at most two. -/

namespace MainTheory.QuaternionHalfTurnGroup

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionAxisAngles
  MainTheory.QuaternionOrthogonalFrame MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionRationalNormalizer MainTheory.QuaternionThirdGroup
  MainTheory.QuaternionConjugatedSubgroup

def HalfTurns (G : Subgroup (unitary ℍ[ℝ])) : Prop := ∀ g∈G,g.val.re^2=1 ∨ g.val.re=0

theorem halfTurns_noQuarter (G : Subgroup (unitary ℍ[ℝ])) (hG : HalfTurns G) : NoQuarter G := by
  intro g hg
  rcases hG g hg with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem scalar_normalizes (g : unitary ℍ[ℝ]) (hr : g.val.re^2=1) : Normalizes g := by
  have hn := normSq_unitary g
  rw [Quaternion.normSq_def',hr] at hn
  have hi : g.val.imI=0 := by nlinarith [sq_nonneg g.val.imJ,sq_nonneg g.val.imK]
  have hj : g.val.imJ=0 := by nlinarith [sq_nonneg g.val.imI,sq_nonneg g.val.imK]
  have hk : g.val.imK=0 := by nlinarith [sq_nonneg g.val.imI,sq_nonneg g.val.imJ]
  apply rational_normalizes g (Or.inl hr)
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inl hk)

theorem axis_normalizes (g : unitary ℍ[ℝ]) (h : CoordinateAxis g) : Normalizes g := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply rational_normalizes
  all_goals norm_num [AllowedWithoutQuarter,axisI,axisJ,axisK,Unitary.coe_neg]

theorem pure_related (G : Subgroup (unitary ℍ[ℝ])) (hG : HalfTurns G)
    (p q : unitary ℍ[ℝ]) (hp : p∈G) (hq : q∈G) (hpre : p.val.re=0) (hqre : q.val.re=0) :
    Related p q := by
  have h := hG (p*q) (G.mul_mem hp hq)
  have he : (p*q).val.re= -imaginaryDot p.val q.val := by
    change (p.val*q.val).re= -imaginaryDot p.val q.val
    simp only [Quaternion.re_mul,imaginaryDot,hpre,hqre]; ring
  rw [he] at h
  apply related_of_dot p q hpre hqre
  rcases h with h | h
  · have hz : (imaginaryDot p.val q.val-1)*(imaginaryDot p.val q.val+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inr (Or.inl (by linarith))

theorem half_turn_group (G : Subgroup (unitary ℍ[ℝ])) (hG : HalfTurns G) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  by_cases hpair : ∃ p∈G,∃ q∈G,p.val.re=0 ∧ q.val.re=0 ∧ p≠q ∧ p≠ -q
  · obtain ⟨p,hp,q,hq,hpre,hqre,hne,hnneg⟩ := hpair
    have ha := ((pure_related G hG p q hp hq hpre hqre).resolve_left hne).resolve_left hnneg
    obtain ⟨u,huI,huJ⟩ := ordered_frame p q hpre hqre ha
    have hi : axisI∈rotated G u := huI ▸ rotated_mem G u p hp
    have hj : axisJ∈rotated G u := huJ ▸ rotated_mem G u q hq
    refine ⟨u,?_⟩
    intro g hg
    exact pauli_frame _ (noQuarter_rotated G u (halfTurns_noQuarter G hG)) hi hj
      _ (rotated_mem G u g hg)
  · by_cases hpure : ∃ p∈G,p.val.re=0
    · obtain ⟨p,hp,hpre⟩ := hpure
      obtain ⟨u,hu⟩ := any_axis p axisI hpre axisI_pure
      refine ⟨u,?_⟩
      intro g hg
      rcases hG g hg with h | h
      · exact scalar_normalizes _ (by rw [conjugate_re]; exact h)
      · have he : g=p ∨ g= -p := by
          by_cases he : g=p
          · exact Or.inl he
          · right; by_contra hn
            exact hpair ⟨g,hg,p,hp,h,hpre,he,hn⟩
        apply axis_normalizes
        rcases he with rfl | he
        · exact Or.inl hu
        · rw [he,conjugate_neg,hu]; exact Or.inr (Or.inl rfl)
    · refine ⟨1,?_⟩
      intro g hg
      have hr : g.val.re^2=1 := (hG g hg).resolve_right (fun h => hpure ⟨g,hg,h⟩)
      simpa [conjugate] using scalar_normalizes g hr

end

end MainTheory.QuaternionHalfTurnGroup
