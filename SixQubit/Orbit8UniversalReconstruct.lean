import SixQubit.Orbit8UniversalMagnitudes

/-!
# Orbit 8 universal converse, XI: reconstructing the triple shell

The pair-cross equations identify `R† c` on every two-excitation state.
Evaluating the already-proved eigen-equation `R R† c = (1/6)c` then gives
the triple-amplitude reconstruction, without choosing a phase for the
all-one amplitude.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

theorem false_indices_pair : ∀ i j : Fin 6, i ≠ j →
    Finset.univ.filter (fun k => pairMask i j k = false) =
      Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j) := by decide

theorem pair_add_third : ∀ i j k : Fin 6,
    i ≠ j → k ≠ i → k ≠ j →
    SS.bxor (pairMask i j) (SS.stdBasis k) = tripleMask i j k := by decide

lemma lower_pair (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j) :
    lower (u d) c (pairMask i j) = -ball c * star (v d i j) := by
  have hcross := congrArg star (pair_cross c d hc hd hcode i j hij)
  simp only [star_add, star_sum, star_mul', star_star, star_zero] at hcross
  unfold lower
  rw [← Finset.sum_filter, false_indices_pair i j hij]
  rw [Finset.sum_congr rfl (fun k hk => by
    have hk' := (Finset.mem_filter.mp hk).2
    rw [pair_add_third i j k hij hk'.1 hk'.2])]
  change (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
    star (u d k) * a c i j k) = _
  have hsum : (∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
      star (u d k) * a c i j k) =
      ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
        a c i j k * star (u d k) := by
    exact Finset.sum_congr rfl (fun k hk => by ring)
  rw [hsum]
  linear_combination hcross

theorem true_indices_triple : ∀ i j k : Fin 6,
    i ≠ j → i ≠ k → j ≠ k →
    Finset.univ.filter (fun l => tripleMask i j k l = true) = {i,j,k} := by decide

theorem triple_remove_first : ∀ i j k : Fin 6,
    i ≠ j → i ≠ k → j ≠ k →
    SS.bxor (tripleMask i j k) (SS.stdBasis i) = pairMask j k := by decide

theorem triple_remove_second : ∀ i j k : Fin 6,
    i ≠ j → i ≠ k → j ≠ k →
    SS.bxor (tripleMask i j k) (SS.stdBasis j) = pairMask i k := by decide

theorem triple_remove_third : ∀ i j k : Fin 6,
    i ≠ j → i ≠ k → j ≠ k →
    SS.bxor (tripleMask i j k) (SS.stdBasis k) = pairMask i j := by decide

lemma raise_triple (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    raise ud f (tripleMask i j k) =
      ud i * f (pairMask j k) + ud j * f (pairMask i k) +
        ud k * f (pairMask i j) := by
  unfold raise
  rw [← Finset.sum_filter, true_indices_triple i j k hij hik hjk]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_singleton,
        triple_remove_first i j k hij hik hjk,
        triple_remove_second i j k hij hik hjk,
        triple_remove_third i j k hij hik hjk]
      ring
    · simp [hjk]
  · simp [hij, hik]

/-- Phase-covariant form of the manuscript's triple reconstruction. -/
theorem triple_reconstruct (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    star (ball c) * a c i j k +
      u d i * star (v d j k) + u d j * star (v d i k) +
        u d k * star (v d i j) = 0 := by
  have hQ := (Q_eigen c d hc hd hnc hnd hcode).1
  have hx := congrFun hQ (tripleMask i j k)
  change raise (u d) (lower (u d) c) (tripleMask i j k) =
    (1/6 : ℂ) * a c i j k at hx
  rw [raise_triple (u d) (lower (u d) c) i j k hij hik hjk,
    lower_pair c d hc hd hcode j k hjk,
    lower_pair c d hc hd hcode i k hik,
    lower_pair c d hc hd hcode i j hij] at hx
  obtain ⟨hb, hr, hb0⟩ := rigid_coordinate_norms c d hc hd hnc hnd hcode
  have hbC : star (ball c) * ball c = (1/6 : ℂ) := by
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) hb
    push_cast at hcast
    rw [← SixQubit.star_mul_self] at hcast
    exact hcast
  have hprod : ball c *
      (star (ball c) * a c i j k +
        u d i * star (v d j k) + u d j * star (v d i k) +
          u d k * star (v d i j)) = 0 := by
    calc
      _ = (star (ball c) * ball c) * a c i j k +
          ball c * (u d i * star (v d j k) +
            u d j * star (v d i k) + u d k * star (v d i j)) := by ring
      _ = (1/6 : ℂ) * a c i j k +
          ball c * (u d i * star (v d j k) +
            u d j * star (v d i k) + u d k * star (v d i j)) := by rw [hbC]
      _ = 0 := by linear_combination -hx
  rcases mul_eq_zero.mp hprod with h | h
  · exact (hb0 h).elim
  · exact h

def edgeMask (d : SS.BitString 6 → ℂ) (q : SS.BitString 6) : ℂ :=
  d (SS.complement q)

def recSum (d : SS.BitString 6 → ℂ) (x : SS.BitString 6) : ℂ :=
  ∑ i, if x i = true then
    u d i * star (edgeMask d (SS.bxor x (SS.stdBasis i))) else 0

theorem weight_two_is_pairMask : ∀ q : SS.BitString 6,
    SS.hammingWt q = 2 → ∃ i j : Fin 6, i ≠ j ∧ q = pairMask i j := by decide

theorem remove_true_from_three : ∀ (x : SS.BitString 6) (i : Fin 6),
    SS.hammingWt x = 3 → x i = true →
      SS.hammingWt (SS.bxor x (SS.stdBasis i)) = 2 := by decide

lemma lower_weight_two (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (q : SS.BitString 6) (hq : SS.hammingWt q = 2) :
    lower (u d) c q = -ball c * star (edgeMask d q) := by
  obtain ⟨i,j,hij,rfl⟩ := weight_two_is_pairMask q hq
  rw [lower_pair c d hc hd hcode i j hij]
  rfl

/-- Coordinate-free triple reconstruction, used by the finite Walsh-to-
hafnian collection below. -/
theorem reconstruct_mask (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (x : SS.BitString 6) (hx : SS.hammingWt x = 3) :
    star (ball c) * c x + recSum d x = 0 := by
  have hQ := (Q_eigen c d hc hd hnc hnd hcode).1
  have hxe := congrFun hQ x
  unfold Qact raise at hxe
  have hxe' : (∑ i, if x i = true then
      u d i * (-ball c * star (edgeMask d (SS.bxor x (SS.stdBasis i)))) else 0) =
      (1/6 : ℂ) * c x := by
    calc
      _ = ∑ i, if x i = true then
          u d i * lower (u d) c (SS.bxor x (SS.stdBasis i)) else 0 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        by_cases hxi : x i = true
        · simp [hxi, lower_weight_two c d hc hd hcode _
            (remove_true_from_three x i hx hxi)]
        · simp [hxi]
      _ = _ := hxe
  obtain ⟨hb, hr, hb0⟩ := rigid_coordinate_norms c d hc hd hnc hnd hcode
  have hbC : star (ball c) * ball c = (1/6 : ℂ) := by
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) hb
    push_cast at hcast
    rw [← SixQubit.star_mul_self] at hcast
    exact hcast
  have hxeS : -(ball c) * recSum d x = (1/6 : ℂ) * c x := by
    unfold recSum
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, if x i = true then
          u d i * (-ball c * star (edgeMask d (SS.bxor x (SS.stdBasis i)))) else 0 := by
        exact Finset.sum_congr rfl (fun i hi => by
          by_cases hxi : x i = true
          · simp [hxi]
            ring
          · simp [hxi])
      _ = _ := hxe'
  have hprod : ball c * (star (ball c) * c x + recSum d x) = 0 := by
    calc
      _ = (star (ball c) * ball c) * c x +
          ball c * recSum d x := by ring
      _ = (1/6 : ℂ) * c x +
          ball c * recSum d x := by rw [hbC]
      _ = 0 := by linear_combination -hxeS
  rcases mul_eq_zero.mp hprod with h | h
  · exact (hb0 h).elim
  · exact h

end

end SixQubit.Orbit8Universal
