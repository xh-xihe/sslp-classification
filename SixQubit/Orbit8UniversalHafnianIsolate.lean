import SixQubit.Orbit8UniversalHafnianCase0
import SixQubit.Orbit8UniversalHafnianCase1
import SixQubit.Orbit8UniversalHafnianCase2
import SixQubit.Orbit8UniversalHafnianCase3
import SixQubit.Orbit8UniversalHafnianCase4
import SixQubit.Orbit8UniversalHafnianCase5

/-!
# Orbit 8 universal converse, XIV: isolate every complementary hafnian

The star equations omit one summand at a time.  The six fixed-vertex modules
kernel-check that the coefficient is independent of the auxiliary omitted
vertex; summing the five equations then isolates every coefficient.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

theorem hafVia_eq_compHaf (d : SS.BitString 6 → ℂ)
    (i j m : Fin 6) (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    hafVia d i j m = compHaf d i m := by
  fin_cases i
  · exact hafVia_eq_compHaf_zero d j m hij him hjm
  · exact hafVia_eq_compHaf_one d j m hij him hjm
  · exact hafVia_eq_compHaf_two d j m hij him hjm
  · exact hafVia_eq_compHaf_three d j m hij him hjm
  · exact hafVia_eq_compHaf_four d j m hij him hjm
  · exact hafVia_eq_compHaf_five d j m hij him hjm

theorem compHaf_sum (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j) :
    (∑ m, if m ≠ i ∧ m ≠ j then
      u d m * star (compHaf d i m) else 0) = 0 := by
  have h := hafnian_sum c d hc hd hnc hnd hcode i j hij
  calc
    _ = (∑ m, if m ≠ i ∧ m ≠ j then
          u d m * star (hafVia d i j m) else 0) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      by_cases hmi : m ≠ i ∧ m ≠ j
      · rw [if_pos hmi, if_pos hmi, hafVia_eq_compHaf d i j m hij (Ne.symm hmi.1)
          (Ne.symm hmi.2)]
      · simp [hmi]
    _ = 0 := h

def compTotal (d : SS.BitString 6 → ℂ) (i : Fin 6) : ℂ :=
  ∑ m, if m ≠ i then u d m * star (compHaf d i m) else 0

theorem compTotal_omit (d : SS.BitString 6 → ℂ) (i j : Fin 6)
    (hij : i ≠ j) :
    (∑ m, if m ≠ i ∧ m ≠ j then
      u d m * star (compHaf d i m) else 0) =
      compTotal d i - u d j * star (compHaf d i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [compTotal, Fin.sum_univ_succ] at hij ⊢ <;> ring

theorem compTotal_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    compTotal d i = 0 := by
  have heq : ∀ j : Fin 6, j ≠ i →
      u d j * star (compHaf d i j) = compTotal d i := by
    intro j hji
    have h := compHaf_sum c d hc hd hnc hnd hcode i j (Ne.symm hji)
    rw [compTotal_omit d i j (Ne.symm hji)] at h
    linear_combination -h
  have hsum : compTotal d i =
      ∑ j, if j ≠ i then compTotal d i else 0 := by
    change (∑ j, if j ≠ i then u d j * star (compHaf d i j) else 0) = _
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases hji : j ≠ i
    · rw [if_pos hji, if_pos hji]
      exact heq j hji
    · simp [hji]
  have hfive : (∑ j, if j ≠ i then compTotal d i else 0) =
      5 * compTotal d i := by
    fin_cases i <;> simp [Fin.sum_univ_succ] <;> ring
  rw [hfive] at hsum
  have hfour : (-4 : ℂ) * compTotal d i = 0 := by
    calc
      _ = compTotal d i - 5 * compTotal d i := by ring
      _ = 0 := sub_eq_zero.mpr hsum
  exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)

/-- Every complementary hafnian coefficient attached to a singleton
amplitude is zero.  All hypotheses are the original support, normalization,
and genuine distance-three KL conditions. -/
theorem compHaf_forced (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i m : Fin 6) (him : i ≠ m) :
    u d m * star (compHaf d i m) = 0 := by
  have hmEq := compHaf_sum c d hc hd hnc hnd hcode i m him
  rw [compTotal_omit d i m him] at hmEq
  have htot := compTotal_zero c d hc hd hnc hnd hcode i
  rw [htot, zero_sub] at hmEq
  exact neg_eq_zero.mp hmEq

end

end SixQubit.Orbit8Universal
