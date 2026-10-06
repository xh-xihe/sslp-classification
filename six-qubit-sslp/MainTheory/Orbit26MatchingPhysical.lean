import MainTheory.Orbit26MatchingRows
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26MatchingPhysical
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26NormalizedRows
open MainTheory.Orbit26MatchingRows MainTheory.Orbit26NonmatchingPhysical
open MainTheory.Orbit26PhysicalDependentAnchors MainTheory.Orbit26PhysicalNorms
open MainTheory.Orbit26PhysicalMatrices MainTheory.Orbit26PrintedProbabilities
open MainTheory.Orbit26 (M2 cj)
open SixQubit.Orbit26 (S0 S1)
noncomputable section

theorem physical_firstrowD (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) (g : Fin 3) :
    row (unitAnchor (C c 3)) (D d g.castSucc)=
      -star (row (unitAnchor (D d 3)) (C c g.castSucc)) := by
  exact normalized_row_relation _ _ _ _ (Real.sqrt (1/8))
    (physical_rows c d hc hd hkl lam mu hC hD g).1

theorem physical_Jrows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu])
    (g h : Fin 3) (hgh : g<h) :
    SixQubit.Block26.Jform
      (row (unitAnchor (D d 3)) (C c g.castSucc) 0)
      (row (unitAnchor (D d 3)) (C c g.castSucc) 1)
      (row (unitAnchor (D d 3)) (C c h.castSucc) 0)
      (row (unitAnchor (D d 3)) (C c h.castSucc) 1)=0 := by
  exact J_rows _ _ _ _ _ _ (physical_outer c d hc hd hkl g h hgh)
    (physical_firstrowD c d hc hd hkl lam mu hC hD g)
    (physical_firstrowD c d hc hd hkl lam mu hC hD h)

theorem physical_row_sum (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ g : Fin 3,nsq (row (unitAnchor (D d 3)) (C c g.castSucc)))=
      1/2+Complex.normSq (star (unitAnchor (C c 3)) ⬝ᵥ unitAnchor (D d 3))/4 := by
  obtain ⟨_,hv,hC,hD,_,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  exact row_sum (fun g : Fin 3 => C c g.castSucc) _ _ _ _ hv hC hD
    (physical_nonanchor_moment_C c d hc hd hkl)

theorem physical_row_bounds (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ g : Fin 3,nsq (row (unitAnchor (D d 3)) (C c g.castSucc))≤1/4) ∧
    (∀ j : Fin 2,(∑ g : Fin 3,
      Complex.normSq (row (unitAnchor (D d 3)) (C c g.castSucc) j))≤3/8) := by
  obtain ⟨_,hv,_,_,_,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  obtain ⟨hm,_⟩ := physical_column_masses c d hc hd hnc hnd hkl
  refine ⟨?_,?_⟩
  · intro g
    rw [row_nsq]
    exact group_row_bound _ _ _ _ hm rfl _ hv g.castSucc
  · intro j
    have he := axis_bound _ _ _ _ hm rfl (unitAnchor (D d 3)) hv j
    simpa [Fin.sum_univ_three,← conjugate_row] using he

theorem physical_anchor_orthogonal (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) :
    star (unitAnchor (C c 3)) ⬝ᵥ unitAnchor (D d 3)=0 := by
  have hs := physical_row_sum c d hc hd hnc hnd hkl
  obtain ⟨hb,ha⟩ := physical_row_bounds c d hc hd hnc hnd hkl
  have e01 := physical_Jrows c d hc hd hkl lam mu hC hD 0 1 (by decide)
  have e02 := physical_Jrows c d hc hd hkl lam mu hC hD 0 2 (by decide)
  have e12 := physical_Jrows c d hc hd hkl lam mu hC hD 1 2 (by decide)
  have hz : Complex.normSq (star (unitAnchor (C c 3)) ⬝ᵥ unitAnchor (D d 3))=0 := by
    by_contra h
    have hp := lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm h)
    apply MainTheory.Orbit26.core_rank_one e01 e02 e12
    · simpa [nsq,Fin.sum_univ_two] using hb 0
    · simpa [nsq,Fin.sum_univ_two] using hb 1
    · simpa [nsq,Fin.sum_univ_two] using hb 2
    · simp only [Fin.sum_univ_three,nsq,Fin.sum_univ_two] at hs
      linarith
    · simpa [Fin.sum_univ_three] using ha 0
    · simpa [Fin.sum_univ_three] using ha 1
  exact Complex.normSq_eq_zero.mp hz

theorem row_boundary (r : Fin 3 → Vec)
    (hs : (∑ g,nsq (r g))=1/2) (hb : ∀ g,nsq (r g)≤1/4)
    (ha : ∀ j : Fin 2,(∑ g,Complex.normSq (r g j))≤3/8)
    (he : ∀ g h : Fin 3,g<h →
      SixQubit.Block26.Jform (r g 0) (r g 1) (r h 0) (r h 1)=0) :
    ∃ k : Fin 3,r k=0 ∧ ∀ g : Fin 3,g≠k → nsq (r g)=1/4 := by
  classical
  have hz : ∃ k,r k=0 := by
    by_contra hn
    push_neg at hn
    have hne (g : Fin 3) : ¬(r g 0=0 ∧ r g 1=0) := by
      rintro ⟨h0,h1⟩
      apply hn g
      funext j
      fin_cases j
      · exact h0
      · exact h1
    rcases SixQubit.Block26.axis_lemma _ _ _ _ _ _ (hne 0) (hne 1) (hne 2)
      (he 0 1 (by decide)) (he 0 2 (by decide)) (he 1 2 (by decide)) with h|h
    · have hx := ha 0
      simp only [Fin.sum_univ_three,nsq,Fin.sum_univ_two,h.1,h.2.1,h.2.2,
        map_zero,add_zero] at hs
      simp only [Fin.sum_univ_three] at hx
      linarith
    · have hx := ha 1
      simp only [Fin.sum_univ_three,nsq,Fin.sum_univ_two,h.1,h.2.1,h.2.2,
        map_zero,zero_add] at hs
      simp only [Fin.sum_univ_three] at hx
      linarith
  obtain ⟨k,hk⟩ := hz
  refine ⟨k,hk,?_⟩
  intro g hg
  have hzN : nsq (r k)=0 := by rw [hk]; simp [nsq]
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  simp only [Fin.sum_univ_three] at hs
  fin_cases k
  · change nsq (r 0)=0 at hzN
    fin_cases g
    · exact (hg rfl).elim
    · change nsq (r 1)=1/4; linarith
    · change nsq (r 2)=1/4; linarith
  · change nsq (r 1)=0 at hzN
    fin_cases g
    · change nsq (r 0)=1/4; linarith
    · exact (hg rfl).elim
    · change nsq (r 2)=1/4; linarith
  · change nsq (r 2)=0 at hzN
    fin_cases g
    · change nsq (r 0)=1/4; linarith
    · change nsq (r 1)=1/4; linarith
    · exact (hg rfl).elim

theorem physical_two_full_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) :
    ∃ k : Fin 3,row (unitAnchor (D d 3)) (C c k.castSucc)=0 ∧
      ∀ g : Fin 3,g≠k → nsq (row (unitAnchor (D d 3)) (C c g.castSucc))=1/4 := by
  have hs := physical_row_sum c d hc hd hnc hnd hkl
  have ho := physical_anchor_orthogonal c d hc hd hnc hnd hkl lam mu hC hD
  rw [ho] at hs
  norm_num at hs
  obtain ⟨hb,ha⟩ := physical_row_bounds c d hc hd hnc hnd hkl
  exact row_boundary _ hs hb ha (physical_Jrows c d hc hd hkl lam mu hC hD)
end
end MainTheory.Orbit26MatchingPhysical
