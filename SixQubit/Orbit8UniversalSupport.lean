import SixQubit.Orbit8UniversalSupportCases
import SixQubit.Orbit8UniversalMomentBound

/-!
# Orbit 8 universal converse: the singleton support has size at most two

This is the final genuine-KL bridge.  Three nonzero singleton amplitudes make
every complementary edge nonzero by the exact `ZZ` magnitude formula; the
kernel-expanded hafnians then contradict `raw_support3_impossible`.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators
open SixQubit

noncomputable section

lemma p_nonneg (d : SS.BitString 6 → ℂ) (i : Fin 6) : 0 ≤ p d i :=
  Complex.normSq_nonneg _

theorem sorted_triple_in_support : ∀ s : Finset (Fin 6),
    ¬ s.card ≤ 2 → ∃ a b c : Fin 6,
      a < b ∧ b < c ∧ a ∈ s ∧ b ∈ s ∧ c ∈ s := by
  decide

theorem triple_has_vertex_outside_pair : ∀ a b c i j : Fin 6,
    a < b → b < c → i ≠ j →
      ∃ k : Fin 6, (k = a ∨ k = b ∨ k = c) ∧ k ≠ i ∧ k ≠ j := by
  decide

lemma sum_p_away_pair (d : SS.BitString 6 → ℂ)
    (hr : r d = 1/6) (i j : Fin 6) (hij : i ≠ j) :
    (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), p d k) =
      1/6 - p d i - p d j := by
  have hset : Finset.univ.filter (fun k : Fin 6 => k ≠ i ∧ k ≠ j) =
      (Finset.univ.erase i).erase j := by
    ext k
    simp [and_comm]
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin 6)) := by
    simp [Ne.symm hij]
  have hi : i ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ i
  have h1 := Finset.sum_erase_add (Finset.univ.erase i) (p d) hj
  have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) (p d) hi
  unfold r at hr
  rw [hset]
  linarith

lemma u_ne_of_p_mem (d : SS.BitString 6 → ℂ) (i : Fin 6)
    (hi : p d i ≠ 0) : u d i ≠ 0 := by
  intro hui
  apply hi
  unfold p
  rw [hui, Complex.normSq_zero]

/-- Once three singleton coordinates are active, all fifteen weight-four
edge coordinates are nonzero. -/
theorem all_edges_nonzero_of_three_active (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (a b cidx : Fin 6) (hab : a < b) (hbc : b < cidx)
    (ha : u d a ≠ 0) (hb : u d b ≠ 0) (hcidx : u d cidx ≠ 0) :
    ∀ i j : Fin 6, i ≠ j → v d i j ≠ 0 := by
  intro i j hij
  obtain ⟨k, hkabc, hki, hkj⟩ :=
    triple_has_vertex_outside_pair a b cidx i j hab hbc hij
  have huk : u d k ≠ 0 := by
    rcases hkabc with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hcidx
  have hkpos : 0 < p d k := Complex.normSq_pos.mpr huk
  have hsumpos : 0 <
      ∑ x ∈ Finset.univ.filter (fun x => x ≠ i ∧ x ≠ j), p d x := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun x hx => p_nonneg d x)).2
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hkj⟩, hkpos⟩
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have haway := sum_p_away_pair d hr i j hij
  have hw := w_formula c d hc hd hnc hnd hcode i j hij
  have hwpos : 0 < w d i j := by
    rw [hw]
    linarith [haway, hsumpos]
  exact Complex.normSq_pos.mp hwpos

/-- The actual nonzero singleton probability support has cardinality at most
two.  No support ansatz is assumed. -/
theorem singleton_support_le_two (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (probabilitySupport (p d)).card ≤ 2 := by
  by_contra hcard
  obtain ⟨a,b,cidx,hab,hbc,haMem,hbMem,hcMem⟩ :=
    sorted_triple_in_support (probabilitySupport (p d)) hcard
  have hpa : p d a ≠ 0 := by simpa [probabilitySupport] using haMem
  have hpb : p d b ≠ 0 := by simpa [probabilitySupport] using hbMem
  have hpc : p d cidx ≠ 0 := by simpa [probabilitySupport] using hcMem
  have ha := u_ne_of_p_mem d a hpa
  have hb := u_ne_of_p_mem d b hpb
  have hcidx := u_ne_of_p_mem d cidx hpc
  have hall := all_edges_nonzero_of_three_active c d hc hd hnc hnd hcode
    a b cidx hab hbc ha hb hcidx
  exact sorted_three_active_impossible c d hc hd hnc hnd hcode hall
    a b cidx hab hbc ha hb hcidx

end

end SixQubit.Orbit8Universal
