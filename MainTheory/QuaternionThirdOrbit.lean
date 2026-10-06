import MainTheory.QuaternionThirdGroup

/-! Exact separation of parallel and tetrahedral third-turn conjugacy orbits. -/

namespace MainTheory.QuaternionThirdOrbit

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionCliffordAxes MainTheory.QuaternionThirdGroup

theorem dot_symm (p q : ℍ[ℝ]) : imaginaryDot p q=imaginaryDot q p := by
  unfold imaginaryDot; ring

theorem same_trace_equal (p q : unitary ℍ[ℝ]) (he : p.val.re=q.val.re)
    (hd : imaginaryDot p.val q.val=1-q.val.re^2) : p=q := by
  have hn := normSq_unitary p
  have hm := normSq_unitary q
  rw [Quaternion.normSq_def',he] at hn
  rw [Quaternion.normSq_def'] at hm
  unfold imaginaryDot at hd
  have hI : p.val.imI=q.val.imI := by
    nlinarith [sq_nonneg (p.val.imJ-q.val.imJ),sq_nonneg (p.val.imK-q.val.imK)]
  have hJ : p.val.imJ=q.val.imJ := by
    nlinarith [sq_nonneg (p.val.imI-q.val.imI),sq_nonneg (p.val.imK-q.val.imK)]
  have hK : p.val.imK=q.val.imK := by
    nlinarith [sq_nonneg (p.val.imI-q.val.imI),sq_nonneg (p.val.imJ-q.val.imJ)]
  apply Subtype.ext; apply Quaternion.ext <;> assumption

theorem third_pair_nonparallel (G : Subgroup (unitary ℍ[ℝ])) (hG : NoQuarter G)
    (q p : unitary ℍ[ℝ]) (hq : q∈G) (hp : p∈G)
    (hqre : q.val.re=1/2) (hpre : p.val.re=1/2)
    (hne : p≠q) (hinv : p≠q⁻¹) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  have hquarter : 4*q.val.re^2=1 := by rw [hqre]; norm_num
  have hd := third_relative_dot p.val q.val (hpre.trans hqre.symm) hquarter
    (hG _ (G.mul_mem hp hq)) (hG _ (G.mul_mem hp (G.inv_mem hq)))
  rcases hd with hd | hd | hd | hd
  · exfalso; apply hinv
    apply same_trace_equal p q⁻¹
    · change p.val.re=(star q.val).re; simp only [Quaternion.re_star,hpre,hqre]
    · change imaginaryDot p.val (star q.val)=1-(star q.val).re^2
      simp only [imaginaryDot,Quaternion.re_star,Quaternion.imI_star,
        Quaternion.imJ_star,Quaternion.imK_star,hqre]
      unfold imaginaryDot at hd
      linarith
  · exfalso; apply hne
    apply same_trace_equal p q (hpre.trans hqre.symm)
    rw [hqre]; linarith
  · exact third_pair_frame G hG q p hq hp hqre hpre ((dot_symm _ _).trans hd)
  · apply third_pair_frame G hG q p⁻¹ hq (G.inv_mem hp) hqre
    · change (star p.val).re=1/2; simpa using hpre
    · change imaginaryDot q.val (star p.val)= -1/4
      have he := (dot_symm q.val p.val).trans hd
      simp only [imaginaryDot,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star]
      unfold imaginaryDot at he
      linarith

end

end MainTheory.QuaternionThirdOrbit
