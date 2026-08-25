import SixQubit.Orbit8UniversalStar

/-!
# Orbit 8 universal converse, XIII: genuine KL to complementary hafnians

The weight-one Walsh equations are combined with the coordinate-free triple
reconstruction.  The resulting double sum is collected inside Lean into the
complementary four-vertex hafnian coefficients.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

set_option maxRecDepth 20000

noncomputable section

def hafVia (d : SS.BitString 6 → ℂ) (i j m : Fin 6) : ℂ :=
  ∑ ij ∈ awayPairs i,
    if touches ij j = true ∧ topRecip i ij m = true then
      v d ij.1 ij.2 * edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis m))
    else 0

theorem topRecip_weight : ∀ (i : Fin 6) (ij : Fin 6 × Fin 6),
    ij ∈ awayPairs i → SS.hammingWt (topRecip i ij) = 3 := by decide

theorem topRecip_left_false : ∀ (i : Fin 6) (ij : Fin 6 × Fin 6),
    ij ∈ awayPairs i → topRecip i ij i = false := by decide

theorem topRecip_touched_false : ∀ (i j : Fin 6) (ij : Fin 6 × Fin 6),
    ij ∈ awayPairs i → touches ij j = true →
      topRecip i ij j = false := by decide

/-- Before isolating the coefficients, every weight-one star supplies the
sum of the four complementary hafnians not containing its dressed vertex. -/
theorem hafnian_sum (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j) :
    (∑ m, if m ≠ i ∧ m ≠ j then
      u d m * star (hafVia d i j m) else 0) = 0 := by
  have hs := star_equation c d hc hd hcode i j hij
  let L : ℂ := ∑ ij ∈ awayPairs i,
    if touches ij j = true then
      star (v d ij.1 ij.2) * recSum d (topRecip i ij) else 0
  have hw : (∑ ij ∈ awayPairs i,
      if touches ij j = true then
        star (v d ij.1 ij.2) *
          (star (ball c) * c (topRecip i ij) + recSum d (topRecip i ij))
      else 0) = 0 := by
    exact Finset.sum_eq_zero (fun ij hmem => by
      by_cases ht : touches ij j = true
      · rw [if_pos ht, reconstruct_mask c d hc hd hnc hnd hcode _
          (topRecip_weight i ij hmem), mul_zero]
      · rw [if_neg ht])
  have hsplit :
      (∑ ij ∈ awayPairs i,
        if touches ij j = true then
          star (v d ij.1 ij.2) *
            (star (ball c) * c (topRecip i ij) + recSum d (topRecip i ij))
        else 0) = star (ball c) *
          (∑ ij ∈ awayPairs i,
            if touches ij j = true then
              star (v d ij.1 ij.2) * c (topRecip i ij) else 0) + L := by
    unfold L
    calc
      _ = ∑ ij ∈ awayPairs i,
          ((if touches ij j = true then
              star (ball c) * (star (v d ij.1 ij.2) * c (topRecip i ij))
            else 0) +
           (if touches ij j = true then
              star (v d ij.1 ij.2) * recSum d (topRecip i ij)
            else 0)) := by
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        by_cases ht : touches ij j = true
        · simp [ht]
          ring
        · simp [ht]
      _ = (∑ ij ∈ awayPairs i,
            if touches ij j = true then
              star (ball c) * (star (v d ij.1 ij.2) * c (topRecip i ij))
            else 0) +
          (∑ ij ∈ awayPairs i,
            if touches ij j = true then
              star (v d ij.1 ij.2) * recSum d (topRecip i ij)
            else 0) := Finset.sum_add_distrib
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        by_cases ht : touches ij j = true <;> simp [ht]
  have hL : L = 0 := by
    rw [hsplit, hs, mul_zero, zero_add] at hw
    exact hw
  have hcollect : L = ∑ m, if m ≠ i ∧ m ≠ j then
      u d m * star (hafVia d i j m) else 0 := by
    unfold L recSum hafVia
    calc
      _ = ∑ ij ∈ awayPairs i, ∑ m,
          if touches ij j = true ∧ topRecip i ij m = true then
            u d m * (star (v d ij.1 ij.2) *
              star (edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis m))))
          else 0 := by
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        by_cases ht : touches ij j = true
        · rw [if_pos ht, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m hm => ?_)
          by_cases hxm : topRecip i ij m = true
          · simp [ht, hxm]
            ring
          · simp [ht, hxm]
        · rw [if_neg ht]
          exact (Finset.sum_eq_zero (fun m hm => by simp [ht])).symm
      _ = ∑ m, ∑ ij ∈ awayPairs i,
          if touches ij j = true ∧ topRecip i ij m = true then
            u d m * (star (v d ij.1 ij.2) *
              star (edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis m))))
          else 0 := by rw [Finset.sum_comm]
      _ = ∑ m, u d m * star
          (∑ ij ∈ awayPairs i,
            if touches ij j = true ∧ topRecip i ij m = true then
              v d ij.1 ij.2 *
                edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis m))
            else 0) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [star_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        by_cases hb : touches ij j = true ∧ topRecip i ij m = true
        · simp [hb, star_mul']
        · simp [hb]
      _ = _ := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        by_cases hmij : m ≠ i ∧ m ≠ j
        · rw [if_pos hmij]
        · rw [if_neg hmij]
          rcases not_and_or.mp hmij with hmi | hmj
          · have hmi' : m = i := not_ne_iff.mp hmi
            subst m
            have hz : (∑ ij ∈ awayPairs i,
                if touches ij j = true ∧ topRecip i ij i = true then
                  v d ij.1 ij.2 *
                    edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis i))
                else 0) = 0 := by
              exact Finset.sum_eq_zero (fun ij hmem => by
                simp [topRecip_left_false i ij hmem])
            rw [hz]
            simp
          · have hmjeq : m = j := not_ne_iff.mp hmj
            subst m
            have hz : (∑ ij ∈ awayPairs i,
                if touches ij j = true ∧ topRecip i ij j = true then
                  v d ij.1 ij.2 *
                    edgeMask d (SS.bxor (topRecip i ij) (SS.stdBasis j))
                else 0) = 0 := by
              exact Finset.sum_eq_zero (fun ij hmem => by
                by_cases ht : touches ij j = true
                · simp [ht, topRecip_touched_false i j ij hmem ht]
                · simp [ht])
            rw [hz]
            simp
  rw [← hcollect]
  exact hL

end

end SixQubit.Orbit8Universal
