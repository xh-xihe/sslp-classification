import MainTheory.Orbit9TwoSupportDisplays

set_option autoImplicit false

namespace MainTheory.Orbit9TwoSupportEdges

open SixQubit.Orbit9Universal SixQubit.CodeEquiv

theorem fullKL_permAct (c d : SS.State 6 ℂ) (H : FullKL c d) (sigma : Equiv.Perm (Fin 6)) :
    FullKL (permAct sigma c) (permAct sigma d) := by
  refine ⟨support_S0_permAct sigma c H.support0,support_S1_permAct sigma d H.support1,
    ?_,?_,hasDistance_permAct sigma c d H.distance⟩
  · rw [innerC_permAct,H.norm0]
  · rw [innerC_permAct,H.norm1]

theorem r_permAct (sigma : Equiv.Perm (Fin 6)) (c : SS.State 6 ℂ) (i j : Fin 6) :
    r (permAct sigma c) i j=r c (sigma.symm i) (sigma.symm j) := by
  have hc (x : SS.BitString 6) : permStr sigma (SS.complement x)=
      SS.complement (permStr sigma x) := rfl
  simp only [r,sigma.symm.injective.eq_iff,permAct,hc,pair,permStr_bxor,permStr_one]

theorem canonical_edges (c d : SS.State 6 ℂ) (H : FullKL c d) (hs : TwoSupport01 c)
    (t : Fin 6) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : r c t 0=1/12 ∧ r c t 1=1/12 := by
  have he := twoSupport01_edges c d H.support0 H.support1 H.norm0 H.norm1 H.distance hs
  fin_cases t
  · exact (ht0 rfl).elim
  · exact (ht1 rfl).elim
  · exact ⟨(r_symm c 2 0).trans he.r02,(r_symm c 2 1).trans he.r12⟩
  · exact ⟨(r_symm c 3 0).trans he.r03,(r_symm c 3 1).trans he.r13⟩
  · exact ⟨(r_symm c 4 0).trans he.r04,(r_symm c 4 1).trans he.r14⟩
  · exact ⟨(r_symm c 5 0).trans he.r05,(r_symm c 5 1).trans he.r15⟩

theorem edges (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) (t : Fin 6) (hta : t ≠ a) (htb : t ≠ b) :
    r c t a=1/12 ∧ r c t b=1/12 := by
  let sigma := pairTo01 a b
  have ha : sigma a=0 := pairTo01_apply_left a b hs.distinct
  have hb : sigma b=1 := pairTo01_apply_right a b
  have ht0 : sigma t ≠ 0 := fun h => hta (sigma.injective (h.trans ha.symm))
  have ht1 : sigma t ≠ 1 := fun h => htb (sigma.injective (h.trans hb.symm))
  have h := canonical_edges (permAct sigma c) (permAct sigma d) (fullKL_permAct c d H sigma)
    (twoSupport01_permAct_of_twoSupportAt c a b hs) (sigma t) ht0 ht1
  rw [← ha,← hb,r_permAct,r_permAct] at h
  simpa only [Equiv.symm_apply_apply] using h

end MainTheory.Orbit9TwoSupportEdges
