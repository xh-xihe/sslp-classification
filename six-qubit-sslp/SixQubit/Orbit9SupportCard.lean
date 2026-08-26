import SixQubit.Orbit9ComponentPhase

/-!
# Orbit 9: support cardinality from the genuine KL budgets

This file deliberately leaves the two-point support branch open.  Its job is
to show, from `FullKL` alone, that every other possible active support has
exactly four singleton coordinates.  No graph or degree condition is added:
the only degree identities used below are `pq_degree` and `global_masses`.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Singleton coordinates having strictly positive probability. -/
noncomputable def ActiveSet (c : SS.State 6 ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (Active c)

@[simp] lemma mem_ActiveSet (c : SS.State 6 ℂ) (i : Fin 6) :
    i ∈ ActiveSet c ↔ Active c i := by
  classical
  simp [ActiveSet]

lemma p_eq_zero_of_not_active (c : SS.State 6 ℂ) (i : Fin 6)
    (hi : ¬ Active c i) : p c i = 0 :=
  le_antisymm (le_of_not_gt hi) (p_nonneg c i)

private lemma yamp_ne_zero_of_active (c d : SS.State 6 ℂ)
    (H : FullKL c d) (i : Fin 6) (hi : Active c i) : yamp d i ≠ 0 := by
  rw [← rho_mul_star_xamp c d i hi]
  exact mul_ne_zero (rho_ne_zero_of_active c d H i hi)
    (star_ne_zero.mpr (xamp_ne_zero_of_active c i hi))

private lemma r_eq_zero_of_damp (c : SS.State 6 ℂ) (i j : Fin 6)
    (hij : i ≠ j) (h : damp c i j = 0) : r c i j = 0 := by
  have hn := congrArg Complex.normSq h
  simpa [r, damp, hij] using hn

/-- Five distinct vertices of `Fin 6` have one remaining vertex, and these
six vertices exhaust `Fin 6`.  `decide` is kernel reduction over a fixed
finite type, not an external enumeration assumption. -/
private theorem sixth_vertex_cover :
    ∀ i j k l t : Fin 6,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      t ≠ i → t ≠ j → t ≠ k → t ≠ l →
      ∃ u : Fin 6,
        u ≠ i ∧ u ≠ j ∧ u ≠ k ∧ u ≠ l ∧ u ≠ t ∧
        ∀ z : Fin 6, z = i ∨ z = j ∨ z = k ∨ z = l ∨ z = t ∨ z = u := by
  intro i j k l t hij hik hil hjk hjl hkl hti htj htk htl
  classical
  let S : Finset (Fin 6) := {i, j, k, l, t}
  have hcardS : S.card = 5 := by
    simp [S, hij, hik, hil, hjk, hjl, hkl,
      Ne.symm hti, Ne.symm htj, Ne.symm htk, Ne.symm htl]
  have hcardC : ((Finset.univ : Finset (Fin 6)) \ S).card = 1 := by
    calc
      ((Finset.univ : Finset (Fin 6)) \ S).card =
          Finset.univ.card - (S ∩ Finset.univ).card := Finset.card_sdiff
      _ = 6 - 5 := by simp [hcardS]
      _ = 1 := by norm_num
  rcases Finset.card_eq_one.mp hcardC with ⟨u, hu⟩
  have huC : u ∈ (Finset.univ : Finset (Fin 6)) \ S := by
    rw [hu]
    simp
  have huS : u ∉ S := (Finset.mem_sdiff.mp huC).2
  have hune : u ≠ i ∧ u ≠ j ∧ u ≠ k ∧ u ≠ l ∧ u ≠ t := by
    simpa [S, and_assoc] using huS
  refine ⟨u, hune.1, hune.2.1, hune.2.2.1, hune.2.2.2.1,
    hune.2.2.2.2, ?_⟩
  intro z
  by_cases hzS : z ∈ S
  · have hz : z = i ∨ z = j ∨ z = k ∨ z = l ∨ z = t := by
      simpa [S] using hzS
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp
  · have hzC : z ∈ (Finset.univ : Finset (Fin 6)) \ S := by
      simp [hzS]
    rw [hu] at hzC
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hzC)))))

private lemma Rdeg_eq_remaining (c : SS.State 6 ℂ)
    (i j k l t u : Fin 6)
    (hcover : ∀ z : Fin 6,
      z = i ∨ z = j ∨ z = k ∨ z = l ∨ z = t ∨ z = u)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l)
    (hdi : damp c t i = 0) (hdj : damp c t j = 0)
    (hdk : damp c t k = 0) (hdl : damp c t l = 0) :
    Rdeg c t = r c t u := by
  classical
  have hri := r_eq_zero_of_damp c t i hti hdi
  have hrj := r_eq_zero_of_damp c t j htj hdj
  have hrk := r_eq_zero_of_damp c t k htk hdk
  have hrl := r_eq_zero_of_damp c t l htl hdl
  unfold Rdeg
  rw [Finset.sum_eq_single u]
  · intro z _ hzu
    rcases hcover z with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hri
    · exact hrj
    · exact hrk
    · exact hrl
    · simp [r]
    · exact (hzu rfl).elim
  · intro hu
    exact (hu (Finset.mem_univ u)).elim

private lemma companion_single_remaining (c d : SS.State 6 ℂ)
    (H : FullKL c d) (i j k l t u : Fin 6)
    (hcover : ∀ z : Fin 6,
      z = i ∨ z = j ∨ z = k ∨ z = l ∨ z = t ∨ z = u)
    (hdi : damp c t i = 0) (hdj : damp c t j = 0)
    (hdk : damp c t k = 0) (hdl : damp c t l = 0) :
    damp c t u * star (yamp d u) = 0 := by
  classical
  have hrow := companion_row_univ c d H t
  have hsum : (∑ z, damp c t z * star (yamp d z)) =
      damp c t u * star (yamp d u) := by
    rw [Finset.sum_eq_single u]
    · intro z _ hzu
      rcases hcover z with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hdi]
      · simp [hdj]
      · simp [hdk]
      · simp [hdl]
      · simp [damp]
      · exact (hzu rfl).elim
    · intro hu
      exact (hu (Finset.mem_univ u)).elim
  rw [hsum] at hrow
  exact hrow

/-- An amplitude-level `K₄` supplied by the phase-component classification
already contains every active singleton coordinate.  This is where the real
degree budget rules out fifth and sixth active vertices. -/
theorem activeK4_covers (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l : Fin 6) (K : ActiveK4 c d i j k l) :
    ∀ t, Active c t → t = i ∨ t = j ∨ t = k ∨ t = l := by
  intro t ht
  by_contra hout
  push_neg at hout
  rcases hout with ⟨hti, htj, htk, htl⟩
  rcases sixth_vertex_cover i j k l t
      K.hij K.hik K.hil K.hjk K.hjl K.hkl hti htj htk htl with
    ⟨u, hui, huj, huk, hul, hut, hcover⟩
  have hiso := K.isolated t hti htj htk htl ht
  have hdi : damp c t i = 0 := by rw [damp_symm]; exact hiso.1
  have hdj : damp c t j = 0 := by rw [damp_symm]; exact hiso.2.1
  have hdk : damp c t k = 0 := by rw [damp_symm]; exact hiso.2.2.1
  have hdl : damp c t l = 0 := by rw [damp_symm]; exact hiso.2.2.2
  have hRt : Rdeg c t = r c t u :=
    Rdeg_eq_remaining c i j k l t u hcover hti htj htk htl hdi hdj hdk hdl
  by_cases hu : Active c u
  · have hcomp := companion_single_remaining c d H i j k l t u hcover
      hdi hdj hdk hdl
    have hdu : damp c t u = 0 :=
      (mul_eq_zero.mp hcomp).resolve_right
        (star_ne_zero.mpr (yamp_ne_zero_of_active c d H u hu))
    have hru : r c t u = 0 := r_eq_zero_of_damp c t u hut.symm hdu
    have hdeg := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1
      H.distance t).2.1
    rw [hRt, hru] at hdeg
    change 0 < p c t at ht
    have hsix : (0 : ℝ) < 1 / 6 := by norm_num
    linarith
  · have hpu : p c u = 0 := p_eq_zero_of_not_active c u hu
    have hdegt := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1
      H.distance t).2.1
    have hdegu := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1
      H.distance u).2.1
    have hle : r c t u ≤ Rdeg c u := by
      rw [r_symm c t u]
      unfold Rdeg
      exact Finset.single_le_sum
        (fun z _ => r_nonneg c u z) (Finset.mem_univ t)
    rw [hRt] at hdegt
    rw [hpu] at hdegu
    change 0 < p c t at ht
    linarith

lemma active_p_sum (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (∑ i ∈ ActiveSet c, p c i) = 1 / 3 := by
  classical
  have hrestrict : (∑ i ∈ ActiveSet c, p c i) = ∑ i, p c i := by
    apply Finset.sum_subset (Finset.subset_univ (ActiveSet c))
    intro i _ hi
    exact p_eq_zero_of_not_active c i (by simpa using hi)
  have hm := (global_masses c d H.support0 H.support1 H.norm0 H.norm1
    H.distance).1
  rw [hrestrict]
  exact hm

lemma active_degree_sum (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (∑ i ∈ ActiveSet c, Rdeg c i) =
      ((ActiveSet c).card : ℝ) / 6 + 1 / 3 := by
  classical
  calc
    (∑ i ∈ ActiveSet c, Rdeg c i) =
        ∑ i ∈ ActiveSet c, (1 / 6 + p c i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (pq_degree c d H.support0 H.support1 H.norm0 H.norm1
        H.distance i).2.1
    _ = ((ActiveSet c).card : ℝ) / 6 +
        ∑ i ∈ ActiveSet c, p c i := by
      rw [Finset.sum_add_distrib]
      simp
      ring
    _ = ((ActiveSet c).card : ℝ) / 6 + 1 / 3 := by
      rw [active_p_sum c d H]

private lemma active_degree_le_inactive_of_no_edge
    (c : SS.State 6 ℂ)
    (hno : ∀ i, i ∈ ActiveSet c → ∀ j, j ∈ ActiveSet c →
      i ≠ j → damp c i j = 0) :
    (∑ i ∈ ActiveSet c, Rdeg c i) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin 6)) \ ActiveSet c, Rdeg c j := by
  classical
  let A := ActiveSet c
  let I := (Finset.univ : Finset (Fin 6)) \ A
  have hrow (i : Fin 6) (hi : i ∈ A) :
      Rdeg c i = ∑ j ∈ I, r c i j := by
    unfold Rdeg
    symm
    apply Finset.sum_subset (Finset.sdiff_subset)
    intro j _ hjI
    have hjA : j ∈ A := by
      by_contra hj
      apply hjI
      simp [hj]
    by_cases hij : i = j
    · subst j
      simp [r]
    · exact r_eq_zero_of_damp c i j hij (hno i hi j hjA hij)
  calc
    (∑ i ∈ ActiveSet c, Rdeg c i) =
        ∑ i ∈ A, ∑ j ∈ I, r c i j := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        exact hrow i hi
    _ = ∑ j ∈ I, ∑ i ∈ A, r c j i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact r_symm c i j
    _ ≤ ∑ j ∈ I, Rdeg c j := by
      apply Finset.sum_le_sum
      intro j _
      unfold Rdeg
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ A) (fun i _ _ => r_nonneg c j i)
    _ = ∑ j ∈ (Finset.univ : Finset (Fin 6)) \ ActiveSet c,
        Rdeg c j := rfl

lemma active_degree_le_two_thirds_of_no_edge
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hno : ∀ i, i ∈ ActiveSet c → ∀ j, j ∈ ActiveSet c →
      i ≠ j → damp c i j = 0) :
    (∑ i ∈ ActiveSet c, Rdeg c i) ≤ 2 / 3 := by
  classical
  have hle := active_degree_le_inactive_of_no_edge c hno
  have hsplit := Finset.sum_sdiff
    (f := Rdeg c) (Finset.subset_univ (ActiveSet c))
  have hR := (global_masses c d H.support0 H.support1 H.norm0 H.norm1
    H.distance).2.1
  have hall : (∑ i, Rdeg c i) = 4 / 3 := by
    unfold Rmass at hR
    norm_num at hR ⊢
    linarith
  linarith

/-- Three or more active singleton probabilities force a genuine nonzero
edge.  This is a consequence of the exact `Rdeg` and total `Rmass` budgets,
not a graph hypothesis. -/
theorem active_edge_of_three_le_card (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hcard : 3 ≤ (ActiveSet c).card) :
    ∃ i ∈ ActiveSet c, ∃ j ∈ ActiveSet c, i ≠ j ∧ damp c i j ≠ 0 := by
  classical
  by_contra hnone
  have hno : ∀ i, i ∈ ActiveSet c → ∀ j, j ∈ ActiveSet c →
      i ≠ j → damp c i j = 0 := by
    intro i hi j hj hij
    by_contra hedge
    exact hnone ⟨i, hi, j, hj, hij, hedge⟩
  have hle := active_degree_le_two_thirds_of_no_edge c d H hno
  rw [active_degree_sum c d H] at hle
  have hcardR : (3 : ℝ) ≤ ((ActiveSet c).card : ℝ) := by
    exact_mod_cast hcard
  norm_num at hle
  linarith

theorem active_card_ne_zero (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 0 := by
  intro hzero
  have hempty := Finset.card_eq_zero.mp hzero
  have hm := active_p_sum c d H
  rw [hempty] at hm
  norm_num at hm

theorem active_card_ne_one (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 1 := by
  classical
  intro hone
  rcases Finset.card_eq_one.mp hone with ⟨a, hA⟩
  have haA : a ∈ ActiveSet c := by rw [hA]; simp
  have ha : Active c a := (mem_ActiveSet c a).mp haA
  have hya : yamp d a ≠ 0 := yamp_ne_zero_of_active c d H a ha
  have hda : ∀ z, damp c a z = 0 := by
    intro z
    by_cases hza : z = a
    · subst z
      simp [damp]
    · have hrow := companion_row_univ c d H z
      have hsum : (∑ j, damp c z j * star (yamp d j)) =
          damp c z a * star (yamp d a) := by
        rw [Finset.sum_eq_single a]
        · intro j _ hja
          have hjnot : ¬ Active c j := by
            intro hj
            have hjA : j ∈ ActiveSet c := (mem_ActiveSet c j).mpr hj
            rw [hA] at hjA
            exact hja (by simpa using hjA)
          rw [yamp_zero_of_not_active c d H j hjnot]
          simp
        · intro haU
          exact (haU (Finset.mem_univ a)).elim
      rw [hsum] at hrow
      have hza0 : damp c z a = 0 :=
        (mul_eq_zero.mp hrow).resolve_right (star_ne_zero.mpr hya)
      rw [damp_symm]
      exact hza0
  have hRzero : Rdeg c a = 0 := by
    unfold Rdeg
    apply Finset.sum_eq_zero
    intro z _
    by_cases haz : a = z
    · subst z
      simp [r]
    · exact r_eq_zero_of_damp c a z haz (hda z)
  have hdeg := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1
    H.distance a).2.1
  rw [hRzero] at hdeg
  change 0 < p c a at ha
  have hsix : (0 : ℝ) < 1 / 6 := by norm_num
  linarith

/-- Once the support has at least three points, a real active edge produces
an amplitude-level `K₄`, and the KL budgets prove that its four vertices are
exactly the entire active support. -/
theorem active_k4_exact_of_three_le_card
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hcard : 3 ≤ (ActiveSet c).card) :
    ∃ i j k l, ActiveK4 c d i j k l ∧
      ∀ t, Active c t ↔ t = i ∨ t = j ∨ t = k ∨ t = l := by
  rcases active_edge_of_three_le_card c d H hcard with
    ⟨i, hiA, j, hjA, hij, hedge⟩
  have hi : Active c i := (mem_ActiveSet c i).mp hiA
  have hj : Active c j := (mem_ActiveSet c j).mp hjA
  rcases active_edge_has_actual_k4 c d H i j hij hi hj hedge with ⟨k, l, K⟩
  refine ⟨i, j, k, l, K, ?_⟩
  intro t
  constructor
  · exact activeK4_covers c d H i j k l K t
  · intro ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact K.active_i
    · exact K.active_j
    · exact K.active_k
    · exact K.active_l

theorem active_card_eq_four_of_three_le
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hcard : 3 ≤ (ActiveSet c).card) :
    (ActiveSet c).card = 4 := by
  classical
  rcases active_k4_exact_of_three_le_card c d H hcard with
    ⟨i, j, k, l, K, hcover⟩
  have hset : ActiveSet c = {i, j, k, l} := by
    ext t
    rw [mem_ActiveSet]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcover t
  rw [hset]
  simp [K.hij, K.hik, K.hil, K.hjk, K.hjl, K.hkl]

/-- The support-cardinality reduction, with the two-point case intentionally
left as the explicit remaining branch. -/
theorem active_card_two_or_four (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card = 2 ∨ (ActiveSet c).card = 4 := by
  by_cases htwo : (ActiveSet c).card = 2
  · exact Or.inl htwo
  · right
    apply active_card_eq_four_of_three_le c d H
    have hzero := active_card_ne_zero c d H
    have hone := active_card_ne_one c d H
    omega

theorem active_card_eq_four_of_ne_two
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (htwo : (ActiveSet c).card ≠ 2) : (ActiveSet c).card = 4 := by
  rcases active_card_two_or_four c d H with h | h
  · exact (htwo h).elim
  · exact h

theorem active_card_ne_three (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 3 := by
  rcases active_card_two_or_four c d H with h | h <;> omega

theorem active_card_ne_five (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 5 := by
  rcases active_card_two_or_four c d H with h | h <;> omega

theorem active_card_ne_six (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (ActiveSet c).card ≠ 6 := by
  rcases active_card_two_or_four c d H with h | h <;> omega

/-- In the four-point branch the actual nonzero damp-edge returned by the KL
budget sits in an `ActiveK4` whose four vertices exactly cover the support. -/
theorem active_k4_exact_of_card_four
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hfour : (ActiveSet c).card = 4) :
    ∃ i j k l, ActiveK4 c d i j k l ∧
      ∀ t, Active c t ↔ t = i ∨ t = j ∨ t = k ∨ t = l := by
  apply active_k4_exact_of_three_le_card c d H
  omega

end

end SixQubit.Orbit9Universal
