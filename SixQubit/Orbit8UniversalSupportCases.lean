import SixQubit.Orbit8UniversalSupportCase012

/-! The remaining nineteen sorted active triples. -/

namespace SixQubit.Orbit8Universal

open SixQubit
noncomputable section

theorem support013_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 1 ≠ 0) (hc' : u d 3 ≠ 0) : False := by
  have hcAct : u d 3 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 1) (s2 := cEdge d 0 3) (s3 := cEdge d 0 2)
    (s4 := cEdge d 0 4) (s5 := cEdge d 0 5) (e12 := cEdge d 1 3)
    (e13 := cEdge d 1 2) (e14 := cEdge d 1 4) (e15 := cEdge d 1 5)
    (e23 := cEdge d 3 2) (e24 := cEdge d 3 4) (e25 := cEdge d 3 5)
    (e34 := cEdge d 2 4) (e35 := cEdge d 2 5) (e45 := cEdge d 4 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hcAct)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 3 2] at h
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl hb)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl hb)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl hb)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl hb)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl ha)
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support014_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 1 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 1) (s2 := cEdge d 0 4) (s3 := cEdge d 0 2)
    (s4 := cEdge d 0 3) (s5 := cEdge d 0 5) (e12 := cEdge d 1 4)
    (e13 := cEdge d 1 2) (e14 := cEdge d 1 3) (e15 := cEdge d 1 5)
    (e23 := cEdge d 4 2) (e24 := cEdge d 4 3) (e25 := cEdge d 4 5)
    (e34 := cEdge d 2 3) (e35 := cEdge d 2 5) (e45 := cEdge d 3 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl hb)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl hb)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl hb)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl hb)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl ha)
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support015_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 1 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 1) (s2 := cEdge d 0 5) (s3 := cEdge d 0 2)
    (s4 := cEdge d 0 3) (s5 := cEdge d 0 4) (e12 := cEdge d 1 5)
    (e13 := cEdge d 1 2) (e14 := cEdge d 1 3) (e15 := cEdge d 1 4)
    (e23 := cEdge d 5 2) (e24 := cEdge d 5 3) (e25 := cEdge d 5 4)
    (e34 := cEdge d 2 3) (e35 := cEdge d 2 4) (e45 := cEdge d 3 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl hb)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl hb)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl hb)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl hb)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 5
      (by decide) (Or.inl ha)
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support023_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 3 ≠ 0) : False := by
  have hcAct : u d 3 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 2) (s2 := cEdge d 0 3) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 4) (s5 := cEdge d 0 5) (e12 := cEdge d 2 3)
    (e13 := cEdge d 2 1) (e14 := cEdge d 2 4) (e15 := cEdge d 2 5)
    (e23 := cEdge d 3 1) (e24 := cEdge d 3 4) (e25 := cEdge d 3 5)
    (e34 := cEdge d 1 4) (e35 := cEdge d 1 5) (e45 := cEdge d 4 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hcAct)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl ha)
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support024_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 2) (s2 := cEdge d 0 4) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 3) (s5 := cEdge d 0 5) (e12 := cEdge d 2 4)
    (e13 := cEdge d 2 1) (e14 := cEdge d 2 3) (e15 := cEdge d 2 5)
    (e23 := cEdge d 4 1) (e24 := cEdge d 4 3) (e25 := cEdge d 4 5)
    (e34 := cEdge d 1 3) (e35 := cEdge d 1 5) (e45 := cEdge d 3 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl ha)
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support025_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 2) (s2 := cEdge d 0 5) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 3) (s5 := cEdge d 0 4) (e12 := cEdge d 2 5)
    (e13 := cEdge d 2 1) (e14 := cEdge d 2 3) (e15 := cEdge d 2 4)
    (e23 := cEdge d 5 1) (e24 := cEdge d 5 3) (e25 := cEdge d 5 4)
    (e34 := cEdge d 1 3) (e35 := cEdge d 1 4) (e45 := cEdge d 3 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 5
      (by decide) (Or.inl ha)
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 3
      (by decide) (Or.inl ha)
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support034_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 3) (s2 := cEdge d 0 4) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 2) (s5 := cEdge d 0 5) (e12 := cEdge d 3 4)
    (e13 := cEdge d 3 1) (e14 := cEdge d 3 2) (e15 := cEdge d 3 5)
    (e23 := cEdge d 4 1) (e24 := cEdge d 4 2) (e25 := cEdge d 4 5)
    (e34 := cEdge d 1 2) (e35 := cEdge d 1 5) (e45 := cEdge d 2 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 2] at h
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 4
      (by decide) (Or.inl ha)
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support035_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 3) (s2 := cEdge d 0 5) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 2) (s5 := cEdge d 0 4) (e12 := cEdge d 3 5)
    (e13 := cEdge d 3 1) (e14 := cEdge d 3 2) (e15 := cEdge d 3 4)
    (e23 := cEdge d 5 1) (e24 := cEdge d 5 2) (e25 := cEdge d 5 4)
    (e34 := cEdge d 1 2) (e35 := cEdge d 1 4) (e45 := cEdge d 2 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 2] at h
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 5
      (by decide) (Or.inl ha)
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support045_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 0 ≠ 0) (hb : u d 4 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 0 4) (s2 := cEdge d 0 5) (s3 := cEdge d 0 1)
    (s4 := cEdge d 0 2) (s5 := cEdge d 0 3) (e12 := cEdge d 4 5)
    (e13 := cEdge d 4 1) (e14 := cEdge d 4 2) (e15 := cEdge d 4 3)
    (e23 := cEdge d 5 1) (e24 := cEdge d 5 2) (e25 := cEdge d 5 3)
    (e34 := cEdge d 1 2) (e35 := cEdge d 1 3) (e45 := cEdge d 2 3)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hb)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 5
      (by decide) (Or.inl ha)
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 2
      (by decide) (Or.inl ha)
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 0 1
      (by decide) (Or.inl ha)
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support123_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 3 ≠ 0) : False := by
  have hcAct : u d 3 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 2) (s2 := cEdge d 1 3) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 4) (s5 := cEdge d 1 5) (e12 := cEdge d 2 3)
    (e13 := cEdge d 2 0) (e14 := cEdge d 2 4) (e15 := cEdge d 2 5)
    (e23 := cEdge d 3 0) (e24 := cEdge d 3 4) (e25 := cEdge d 3 5)
    (e34 := cEdge d 0 4) (e35 := cEdge d 0 5) (e45 := cEdge d 4 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hcAct)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl ha)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl ha)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support124_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 2) (s2 := cEdge d 1 4) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 3) (s5 := cEdge d 1 5) (e12 := cEdge d 2 4)
    (e13 := cEdge d 2 0) (e14 := cEdge d 2 3) (e15 := cEdge d 2 5)
    (e23 := cEdge d 4 0) (e24 := cEdge d 4 3) (e25 := cEdge d 4 5)
    (e34 := cEdge d 0 3) (e35 := cEdge d 0 5) (e45 := cEdge d 3 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl ha)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl ha)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support125_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 2 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 2) (s2 := cEdge d 1 5) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 3) (s5 := cEdge d 1 4) (e12 := cEdge d 2 5)
    (e13 := cEdge d 2 0) (e14 := cEdge d 2 3) (e15 := cEdge d 2 4)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 3) (e25 := cEdge d 5 4)
    (e34 := cEdge d 0 3) (e35 := cEdge d 0 4) (e45 := cEdge d 3 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl hb)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 3
      (by decide) (Or.inl hb)
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl hb)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl ha)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 3
      (by decide) (Or.inl ha)
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support134_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 3) (s2 := cEdge d 1 4) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 2) (s5 := cEdge d 1 5) (e12 := cEdge d 3 4)
    (e13 := cEdge d 3 0) (e14 := cEdge d 3 2) (e15 := cEdge d 3 5)
    (e23 := cEdge d 4 0) (e24 := cEdge d 4 2) (e25 := cEdge d 4 5)
    (e34 := cEdge d 0 2) (e35 := cEdge d 0 5) (e45 := cEdge d 2 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 2] at h
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 4
      (by decide) (Or.inl ha)
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl ha)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support135_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 3) (s2 := cEdge d 1 5) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 2) (s5 := cEdge d 1 4) (e12 := cEdge d 3 5)
    (e13 := cEdge d 3 0) (e14 := cEdge d 3 2) (e15 := cEdge d 3 4)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 2) (e25 := cEdge d 5 4)
    (e34 := cEdge d 0 2) (e35 := cEdge d 0 4) (e45 := cEdge d 2 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 2] at h
    simp only [compHaf_23] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl ha)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl ha)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support145_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 1 ≠ 0) (hb : u d 4 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 1 4) (s2 := cEdge d 1 5) (s3 := cEdge d 1 0)
    (s4 := cEdge d 1 2) (s5 := cEdge d 1 3) (e12 := cEdge d 4 5)
    (e13 := cEdge d 4 0) (e14 := cEdge d 4 2) (e15 := cEdge d 4 3)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 2) (e25 := cEdge d 5 3)
    (e34 := cEdge d 0 2) (e35 := cEdge d 0 3) (e45 := cEdge d 2 3)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hb)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 5
      (by decide) (Or.inl ha)
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 2
      (by decide) (Or.inl ha)
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 1 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 1 0] at h
    simp only [compHaf_01] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support234_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 2 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 4 ≠ 0) : False := by
  have hcAct : u d 4 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 2 3) (s2 := cEdge d 2 4) (s3 := cEdge d 2 0)
    (s4 := cEdge d 2 1) (s5 := cEdge d 2 5) (e12 := cEdge d 3 4)
    (e13 := cEdge d 3 0) (e14 := cEdge d 3 1) (e15 := cEdge d 3 5)
    (e23 := cEdge d 4 0) (e24 := cEdge d 4 1) (e25 := cEdge d 4 5)
    (e34 := cEdge d 0 1) (e35 := cEdge d 0 5) (e45 := cEdge d 1 5)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hcAct)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 4
      (by decide) (Or.inl ha)
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support235_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 2 ≠ 0) (hb : u d 3 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 2 3) (s2 := cEdge d 2 5) (s3 := cEdge d 2 0)
    (s4 := cEdge d 2 1) (s5 := cEdge d 2 4) (e12 := cEdge d 3 5)
    (e13 := cEdge d 3 0) (e14 := cEdge d 3 1) (e15 := cEdge d 3 4)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 1) (e25 := cEdge d 5 4)
    (e34 := cEdge d 0 1) (e35 := cEdge d 0 4) (e45 := cEdge d 1 4)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 4
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 4] at h
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 4
      (by decide) (Or.inl hb)
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl hb)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl ha)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support245_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 2 ≠ 0) (hb : u d 4 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 2 4) (s2 := cEdge d 2 5) (s3 := cEdge d 2 0)
    (s4 := cEdge d 2 1) (s5 := cEdge d 2 3) (e12 := cEdge d 4 5)
    (e13 := cEdge d 4 0) (e14 := cEdge d 4 1) (e15 := cEdge d 4 3)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 1) (e25 := cEdge d 5 3)
    (e34 := cEdge d 0 1) (e35 := cEdge d 0 3) (e45 := cEdge d 1 3)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 3
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 3] at h
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 3
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 3] at h
    simp only [compHaf_34] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hb)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 5
      (by decide) (Or.inl ha)
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 1
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 1] at h
    simp only [compHaf_12] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 2 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 2 0] at h
    simp only [compHaf_02] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem support345_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (ha : u d 3 ≠ 0) (hb : u d 4 ≠ 0) (hc' : u d 5 ≠ 0) : False := by
  have hcAct : u d 5 ≠ 0 := hc'
  apply raw_support3_impossible
    (s1 := cEdge d 3 4) (s2 := cEdge d 3 5) (s3 := cEdge d 3 0)
    (s4 := cEdge d 3 1) (s5 := cEdge d 3 2) (e12 := cEdge d 4 5)
    (e13 := cEdge d 4 0) (e14 := cEdge d 4 1) (e15 := cEdge d 4 2)
    (e23 := cEdge d 5 0) (e24 := cEdge d 5 1) (e25 := cEdge d 5 2)
    (e34 := cEdge d 0 1) (e35 := cEdge d 0 2) (e45 := cEdge d 1 2)
  all_goals try exact cEdge_ne d hall _ _ (by decide)
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 2
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 2] at h
    simp only [compHaf_25] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 1
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 1] at h
    simp only [compHaf_15] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 5 0
      (by decide) (Or.inl hcAct)
    rw [compHaf_swap d 5 0] at h
    simp only [compHaf_05] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 2
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 2] at h
    simp only [compHaf_24] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 1
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 1] at h
    simp only [compHaf_14] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 0
      (by decide) (Or.inl hb)
    rw [compHaf_swap d 4 0] at h
    simp only [compHaf_04] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 4 5
      (by decide) (Or.inl hb)
    simp only [compHaf_45] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 5
      (by decide) (Or.inl ha)
    simp only [compHaf_35] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 1
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 3 1] at h
    simp only [compHaf_13] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h
  · have h := compHaf_eq_zero_of_endpoint c d hc hd hnc hnd hcode 3 0
      (by decide) (Or.inl ha)
    rw [compHaf_swap d 3 0] at h
    simp only [compHaf_03] at h
    simp [cEdge] at h ⊢
    ring_nf at h ⊢
    exact h

theorem sorted_three_active_impossible (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hall : ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0)
    (a b cidx : Fin 6) (hab : a < b) (hbc : b < cidx)
    (ha : u d a ≠ 0) (hb : u d b ≠ 0) (hcidx : u d cidx ≠ 0) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases cidx <;> simp at hab hbc
  all_goals first
    | exact support012_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support013_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support014_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support015_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support023_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support024_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support025_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support034_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support035_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support045_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support123_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support124_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support125_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support134_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support135_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support145_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support234_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support235_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support245_impossible c d hc hd hnc hnd hcode hall ha hb hcidx
    | exact support345_impossible c d hc hd hnc hnd hcode hall ha hb hcidx

end
end SixQubit.Orbit8Universal
