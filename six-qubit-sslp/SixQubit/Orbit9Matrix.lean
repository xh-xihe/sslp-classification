import SixQubit.Orbit9Mask

/-!
# Orbit 9: abstract component matrix

The active-component argument uses only a symmetric zero-diagonal complex
matrix, its row kernel, and its four-vertex hafnians.  This file packages that
layer without choosing labels or dividing by an edge amplitude.
-/

namespace SixQubit.Orbit9Matrix

open scoped BigOperators

noncomputable section

structure MatrixSys (m : Fin 6 → Fin 6 → ℂ) : Prop where
  symm : ∀ i j, m i j = m j i
  diag : ∀ i, m i i = 0
  row : ∀ i, (∑ j, m i j) = 0
  haf : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l →
    j ≠ k → j ≠ l → k ≠ l →
      m i j * m k l + m i k * m j l + m i l * m j k = 0

def outside3 (i j k : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun l => l ≠ i ∧ l ≠ j ∧ l ≠ k)

lemma univ_eq_insert3 (i j k : Fin 6) :
    (Finset.univ : Finset (Fin 6)) =
      insert i (insert j (insert k (outside3 i j k))) := by
  ext l
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_filter,
    outside3]
  by_cases hli : l = i
  · exact Or.inl hli
  by_cases hlj : l = j
  · exact Or.inr (Or.inl hlj)
  by_cases hlk : l = k
  · exact Or.inr (Or.inr (Or.inl hlk))
  exact Or.inr (Or.inr (Or.inr ⟨True.intro, hli, hlj, hlk⟩))

lemma outside3_perm (i j k : Fin 6) :
    outside3 i j k = outside3 j k i := by
  ext l
  simp [outside3, and_left_comm, and_comm]

lemma row_outside3 {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ l ∈ outside3 i j k, m i l) = -(m i j + m i k) := by
  have hr := h.row i
  change (∑ l ∈ (Finset.univ : Finset (Fin 6)), m i l) = 0 at hr
  rw [univ_eq_insert3 i j k] at hr
  have hi : i ∉ insert j (insert k (outside3 i j k)) := by
    simp [outside3, hij, hik]
  have hj : j ∉ insert k (outside3 i j k) := by
    simp [outside3, hjk]
  have hk : k ∉ outside3 i j k := by simp [outside3]
  rw [Finset.sum_insert hi, Finset.sum_insert hj, Finset.sum_insert hk] at hr
  rw [h.diag] at hr
  linear_combination hr

/-- Summing the hafnians through a triangle and substituting the three row
identities gives the division-free triangle relation. -/
theorem triangle_relation {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    m i j * m i k + m i j * m j k + m i k * m j k = 0 := by
  have hs :
      (∑ l ∈ outside3 i j k,
        (m i j * m k l + m i k * m j l + m i l * m j k)) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hm := (Finset.mem_filter.mp hl).2
    exact h.haf i j k l hij hik (Ne.symm hm.1)
      hjk (Ne.symm hm.2.1) (Ne.symm hm.2.2)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  have hi := row_outside3 h i j k hij hik hjk
  have hj := row_outside3 h j k i hjk (Ne.symm hij) (Ne.symm hik)
  have hk := row_outside3 h k i j (Ne.symm hik) (Ne.symm hjk) hij
  rw [outside3_perm j k i, outside3_perm k i j] at hj
  rw [outside3_perm k i j] at hk
  have sji := h.symm j i
  have ski := h.symm k i
  have skj := h.symm k j
  rw [hi, hj, hk, sji, ski, skj] at hs
  linear_combination (-1 / 2 : ℂ) * hs

/-- Two adjacent nonzero edges force the third edge of their triangle. -/
theorem triangle_closes {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hij0 : m i j ≠ 0) (hik0 : m i k ≠ 0) : m j k ≠ 0 := by
  intro hjk0
  have ht := triangle_relation h i j k hij hik hjk
  rw [hjk0] at ht
  simp only [mul_zero, add_zero] at ht
  exact (mul_ne_zero hij0 hik0) ht

def outside2 (i j : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)

lemma univ_eq_insert2 (i j : Fin 6) :
    (Finset.univ : Finset (Fin 6)) = insert i (insert j (outside2 i j)) := by
  ext k
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_filter,
    outside2]
  by_cases hki : k = i
  · exact Or.inl hki
  by_cases hkj : k = j
  · exact Or.inr (Or.inl hkj)
  exact Or.inr (Or.inr ⟨True.intro, hki, hkj⟩)

lemma row_outside2 {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j : Fin 6) (hij : i ≠ j) :
    (∑ k ∈ outside2 i j, m i k) = -m i j := by
  have hr := h.row i
  change (∑ k ∈ (Finset.univ : Finset (Fin 6)), m i k) = 0 at hr
  rw [univ_eq_insert2 i j] at hr
  have hi : i ∉ insert j (outside2 i j) := by simp [outside2, hij]
  have hj : j ∉ outside2 i j := by simp [outside2]
  rw [Finset.sum_insert hi, Finset.sum_insert hj, h.diag] at hr
  linear_combination hr

/-- A row-kernel matrix cannot have a two-vertex nontrivial component. -/
theorem edge_has_third {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j : Fin 6) (hij : i ≠ j) (hij0 : m i j ≠ 0) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ m i k ≠ 0 := by
  classical
  by_contra hex
  have hz : ∀ k, k ≠ i → k ≠ j → m i k = 0 := by
    intro k hki hkj
    by_contra hk0
    exact hex ⟨k, hki, hkj, hk0⟩
  have hsum : (∑ k ∈ outside2 i j, m i k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hm := (Finset.mem_filter.mp hk).2
    exact hz k hm.1 hm.2
  have hr := row_outside2 h i j hij
  rw [hsum] at hr
  exact hij0 (by linear_combination hr)

/-- An active triangle cannot be an isolated connected component. -/
theorem triangle_has_outgoing {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hij0 : m i j ≠ 0) :
    ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧
      (m i l ≠ 0 ∨ m j l ≠ 0 ∨ m k l ≠ 0) := by
  classical
  by_contra hex
  have hzero : ∀ a l, (a = i ∨ a = j ∨ a = k) →
      l ≠ i → l ≠ j → l ≠ k → m a l = 0 := by
    intro a l ha hli hlj hlk
    by_contra hal
    apply hex
    refine ⟨l, hli, hlj, hlk, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact Or.inl hal
    · exact Or.inr (Or.inl hal)
    · exact Or.inr (Or.inr hal)
  have hsi : (∑ l ∈ outside3 i j k, m i l) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hm := (Finset.mem_filter.mp hl).2
    exact hzero i l (Or.inl rfl) hm.1 hm.2.1 hm.2.2
  have hsj : (∑ l ∈ outside3 i j k, m j l) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hm := (Finset.mem_filter.mp hl).2
    exact hzero j l (Or.inr (Or.inl rfl)) hm.1 hm.2.1 hm.2.2
  have hsk : (∑ l ∈ outside3 i j k, m k l) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hm := (Finset.mem_filter.mp hl).2
    exact hzero k l (Or.inr (Or.inr rfl)) hm.1 hm.2.1 hm.2.2
  have hi := row_outside3 h i j k hij hik hjk
  have hj := row_outside3 h j k i hjk (Ne.symm hij) (Ne.symm hik)
  have hk := row_outside3 h k i j (Ne.symm hik) (Ne.symm hjk) hij
  rw [hsi] at hi
  rw [outside3_perm j k i, outside3_perm k i j, hsj] at hj
  rw [outside3_perm k i j, hsk] at hk
  have hji := h.symm j i
  have hki := h.symm k i
  have hkj := h.symm k j
  rw [hji] at hj
  rw [hki, hkj] at hk
  have hz : m i j = 0 := by
    linear_combination (1 / 2 : ℂ) * hi + (1 / 2 : ℂ) * hj - (1 / 2 : ℂ) * hk
  exact hij0 hz

def relabel (σ : Equiv.Perm (Fin 6)) (m : Fin 6 → Fin 6 → ℂ) :
    Fin 6 → Fin 6 → ℂ := fun i j => m (σ i) (σ j)

theorem relabel_sys {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (σ : Equiv.Perm (Fin 6)) : MatrixSys (relabel σ m) := by
  constructor
  · intro i j
    exact h.symm (σ i) (σ j)
  · intro i
    exact h.diag (σ i)
  · intro i
    change (∑ j, m (σ i) (σ j)) = 0
    rw [σ.sum_comp]
    · exact h.row (σ i)
    · simp
  · intro i j k l hij hik hil hjk hjl hkl
    exact h.haf (σ i) (σ j) (σ k) (σ l)
      (σ.injective.ne hij) (σ.injective.ne hik) (σ.injective.ne hil)
      (σ.injective.ne hjk) (σ.injective.ne hjl) (σ.injective.ne hkl)

theorem toGraphSys {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m) :
    SixQubit.Orbit9Graph.Sys
      (m 0 1) (m 0 2) (m 0 3) (m 0 4) (m 0 5)
      (m 1 2) (m 1 3) (m 1 4) (m 1 5)
      (m 2 3) (m 2 4) (m 2 5) (m 3 4) (m 3 5) (m 4 5) := by
  constructor
  · have hr := h.row 0
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr
  · have hr := h.row 1
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr - h.symm 1 0
  · have hr := h.row 2
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr - h.symm 2 0 - h.symm 2 1
  · have hr := h.row 3
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr - h.symm 3 0 - h.symm 3 1 - h.symm 3 2
  · have hr := h.row 4
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr - h.symm 4 0 - h.symm 4 1 - h.symm 4 2 - h.symm 4 3
  · have hr := h.row 5
    simp [Fin.sum_univ_succ, h.diag] at hr
    linear_combination hr - h.symm 5 0 - h.symm 5 1 - h.symm 5 2 - h.symm 5 3 - h.symm 5 4
  · exact h.haf 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 1 2 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 1 2 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 1 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 1 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 1 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 2 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 2 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 0 3 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 1 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 1 2 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 1 2 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 1 3 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact h.haf 2 3 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

theorem noK5_canonical {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (z05 : m 0 5 = 0) (z15 : m 1 5 = 0) (z25 : m 2 5 = 0)
    (z35 : m 3 5 = 0) (z45 : m 4 5 = 0)
    (n01 : m 0 1 ≠ 0) (n23 : m 2 3 ≠ 0)
    (n24 : m 2 4 ≠ 0) (n34 : m 3 4 ≠ 0) : False :=
  SixQubit.Orbit9Graph.no_K5_component (toGraphSys h)
    z05 z15 z25 z35 z45 n01 n23 n24 n34

/-- A five-clique cannot be a connected component, in arbitrary labels. -/
theorem k5_has_crossing {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (t : Fin 6)
    (hclique : ∀ i j, i ≠ t → j ≠ t → i ≠ j → m i j ≠ 0) :
    ∃ i, i ≠ t ∧ m t i ≠ 0 := by
  classical
  by_contra hex
  have hzero : ∀ i, i ≠ t → m t i = 0 := by
    intro i hit
    by_contra hti
    exact hex ⟨i, hit, hti⟩
  let σ : Equiv.Perm (Fin 6) := Equiv.swap 5 t
  let m' : Fin 6 → Fin 6 → ℂ := relabel σ m
  have hs : MatrixSys m' := relabel_sys h σ
  have hσ5 : σ 5 = t := by simp [σ]
  have hnot : ∀ a : Fin 6, a ≠ 5 → σ a ≠ t := by
    intro a ha hat
    apply ha
    apply σ.injective
    rw [hσ5]
    exact hat
  have z (a : Fin 6) (ha : a ≠ 5) : m' a 5 = 0 := by
    unfold m' relabel
    rw [hσ5, h.symm]
    exact hzero (σ a) (hnot a ha)
  have n (a b : Fin 6) (ha : a ≠ 5) (hb : b ≠ 5) (hab : a ≠ b) :
      m' a b ≠ 0 := by
    unfold m' relabel
    exact hclique (σ a) (σ b) (hnot a ha) (hnot b hb)
      (σ.injective.ne hab)
  exact noK5_canonical hs
    (z 0 (by decide)) (z 1 (by decide)) (z 2 (by decide))
    (z 3 (by decide)) (z 4 (by decide))
    (n 0 1 (by decide) (by decide) (by decide))
    (n 2 3 (by decide) (by decide) (by decide))
    (n 2 4 (by decide) (by decide) (by decide))
    (n 3 4 (by decide) (by decide) (by decide))

/-- The complete six-vertex support is excluded by the exact K6 certificate. -/
theorem noK6 {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m) :
    ¬ ∀ i j, i ≠ j → m i j ≠ 0 := by
  intro hcomplete
  exact SixQubit.Orbit9Graph.no_K6 (toGraphSys h)
    (hcomplete 0 3 (by decide)) (hcomplete 0 4 (by decide))
    (hcomplete 0 5 (by decide)) (hcomplete 1 2 (by decide))

def maskOf (m : Fin 6 → Fin 6 → ℂ) : SixQubit.Orbit9Mask.Mask :=
  ⟨decide (m 0 1 ≠ 0), decide (m 0 2 ≠ 0), decide (m 0 3 ≠ 0),
    decide (m 0 4 ≠ 0), decide (m 0 5 ≠ 0), decide (m 1 2 ≠ 0),
    decide (m 1 3 ≠ 0), decide (m 1 4 ≠ 0), decide (m 1 5 ≠ 0),
    decide (m 2 3 ≠ 0), decide (m 2 4 ≠ 0), decide (m 2 5 ≠ 0),
    decide (m 3 4 ≠ 0), decide (m 3 5 ≠ 0), decide (m 4 5 ≠ 0)⟩

lemma edge_maskOf_iff {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m)
    (i j : Fin 6) :
    SixQubit.Orbit9Mask.edge (maskOf m) i j = true ↔ m i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [maskOf, SixQubit.Orbit9Mask.edge, h.diag]
  all_goals rw [h.symm]

theorem triangleClosed_maskOf {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m) :
    SixQubit.Orbit9Mask.triangleClosedB (maskOf m) = true := by
  rw [SixQubit.Orbit9Mask.triangleClosedB_iff]
  intro i j k hij hik hjk hij0 hik0
  change SixQubit.Orbit9Mask.edge (maskOf m) i j = true at hij0
  change SixQubit.Orbit9Mask.edge (maskOf m) i k = true at hik0
  change SixQubit.Orbit9Mask.edge (maskOf m) j k = true
  rw [edge_maskOf_iff h] at hij0 hik0 ⊢
  exact triangle_closes h i j k hij hik hjk hij0 hik0

theorem valid_mask_prop {m : Fin 6 → Fin 6 → ℂ} (h : MatrixSys m) :
    SixQubit.Orbit9Mask.Valid (maskOf m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (SixQubit.Orbit9Mask.triangleClosedB_iff _).mp
      (triangleClosed_maskOf h)
  · intro i j hij0
    change SixQubit.Orbit9Mask.edge (maskOf m) i j = true at hij0
    have hmij := (edge_maskOf_iff h i j).mp hij0
    have hij : i ≠ j := by
      intro heq
      subst j
      exact hmij (h.diag i)
    rcases edge_has_third h i j hij hmij with ⟨k, hki, hkj, hik⟩
    refine ⟨k, hki, hkj, ?_⟩
    change SixQubit.Orbit9Mask.edge (maskOf m) i k = true
    exact (edge_maskOf_iff h i k).mpr hik
  · intro i j k hij hik hjk hij0 hik0 hjk0
    change SixQubit.Orbit9Mask.edge (maskOf m) i j = true at hij0
    have hmij := (edge_maskOf_iff h i j).mp hij0
    rcases triangle_has_outgoing h i j k hij hik hjk hmij with
      ⟨l, hli, hlj, hlk, hout⟩
    refine ⟨l, hli, hlj, hlk, ?_⟩
    rcases hout with hil | hjl | hkl
    · exact Or.inl ((edge_maskOf_iff h i l).mpr hil)
    · exact Or.inr (Or.inl ((edge_maskOf_iff h j l).mpr hjl))
    · exact Or.inr (Or.inr ((edge_maskOf_iff h k l).mpr hkl))
  · intro t hclique
    have hc : ∀ i j, i ≠ t → j ≠ t → i ≠ j → m i j ≠ 0 := by
      intro i j hit hjt hij
      have ha := hclique i j hit hjt hij
      change SixQubit.Orbit9Mask.edge (maskOf m) i j = true at ha
      exact (edge_maskOf_iff h i j).mp ha
    rcases k5_has_crossing h t hc with ⟨i, hit, hti⟩
    refine ⟨i, hit, ?_⟩
    change SixQubit.Orbit9Mask.edge (maskOf m) t i = true
    exact (edge_maskOf_iff h t i).mpr hti
  · intro hcomplete
    apply noK6 h
    intro i j hij
    have ha := hcomplete i j hij
    change SixQubit.Orbit9Mask.edge (maskOf m) i j = true at ha
    exact (edge_maskOf_iff h i j).mp ha

end

end SixQubit.Orbit9Matrix
