import SixQubit.Orbit8UniversalHafnianExplicit

namespace SixQubit.Orbit8Universal

open SixQubit
noncomputable section

def cEdge (d : SS.BitString 6 → ℂ) (i j : Fin 6) : ℂ :=
  if i < j then v d i j else v d j i

lemma cEdge_ne (d : SS.BitString 6 → ℂ)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (i j : Fin 6) (hij : i ≠ j) : cEdge d i j ≠ 0 := by
  unfold cEdge
  split
  · exact hall i j hij
  · exact hall j i (Ne.symm hij)

theorem support012_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (h0 : u d 0 ≠ 0) (h1 : u d 1 ≠ 0) (h2 : u d 2 ≠ 0) : False := by
  apply raw_support3_impossible
    (s1 := cEdge d 0 1) (s2 := cEdge d 0 2) (s3 := cEdge d 0 3)
    (s4 := cEdge d 0 4) (s5 := cEdge d 0 5)
    (e12 := cEdge d 1 2) (e13 := cEdge d 1 3)
    (e14 := cEdge d 1 4) (e15 := cEdge d 1 5)
    (e23 := cEdge d 2 3) (e24 := cEdge d 2 4)
    (e25 := cEdge d 2 5) (e34 := cEdge d 3 4)
    (e35 := cEdge d 3 5) (e45 := cEdge d 4 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl h2)
    simp only [compHaf_25] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl h2)
    simp only [compHaf_24] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl h2)
    simp only [compHaf_23] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl h1)
    simp only [compHaf_15] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl h1)
    simp only [compHaf_14] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl h1)
    simp only [compHaf_13] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl h1)
    simp only [compHaf_12] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl h0)
    simp only [compHaf_02] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl h0)
    simp only [compHaf_04] at h
    simpa [cEdge] using h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl h0)
    simp only [compHaf_03] at h
    simpa [cEdge] using h

end
end SixQubit.Orbit8Universal
