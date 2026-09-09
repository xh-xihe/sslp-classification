import MainTheory.OrderSevenMoment57
import MainTheory.OrderSevenMoment58
import MainTheory.OrderSevenMoment59
import MainTheory.OrderSevenMoment60
import MainTheory.OrderSevenMoment61

set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace MainTheory.OrderSevenMomentSufficiency
open MainTheory.OrderSevenSupportDisplays MainTheory.MomentPolytope
open MainTheory.OrderEightSupportDisplays (bits)

theorem feasible57 
    (hn : ∀ i,0 ≤ MainTheory.OrderSevenMoment57.pattern i) :
    Feasible bottom57 top57 (Sum.elim MainTheory.OrderSevenMoment57.pattern MainTheory.OrderSevenMoment57.pattern) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSevenMoment57.pattern,Fin.sum_univ_succ]
  · norm_num [MainTheory.OrderSevenMoment57.pattern,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom57,top57,bits,SS.complement,MainTheory.OrderSevenMoment57.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ]
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom57,top57,bits,SS.complement,MainTheory.OrderSevenMoment57.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at *

theorem feasible58 (s t : ℝ)
    (hn : ∀ i,0 ≤ (MainTheory.OrderSevenMoment58.pattern s t) i) :
    Feasible bottom58 top58 (Sum.elim (MainTheory.OrderSevenMoment58.pattern s t) (MainTheory.OrderSevenMoment58.pattern s t)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSevenMoment58.pattern,Fin.sum_univ_succ]
    ring
  · norm_num [MainTheory.OrderSevenMoment58.pattern,Fin.sum_univ_succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom58,top58,bits,SS.complement,MainTheory.OrderSevenMoment58.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom58,top58,bits,SS.complement,MainTheory.OrderSevenMoment58.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

theorem feasible59 
    (hn : ∀ i,0 ≤ MainTheory.OrderSevenMoment59.pattern i) :
    Feasible bottom59 top59 (Sum.elim MainTheory.OrderSevenMoment59.pattern MainTheory.OrderSevenMoment59.pattern) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSevenMoment59.pattern,Fin.sum_univ_succ]
  · norm_num [MainTheory.OrderSevenMoment59.pattern,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom59,top59,bits,SS.complement,MainTheory.OrderSevenMoment59.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ]
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom59,top59,bits,SS.complement,MainTheory.OrderSevenMoment59.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at *

theorem feasible60 (s t : ℝ)
    (hn : ∀ i,0 ≤ (MainTheory.OrderSevenMoment60.pattern s t) i) :
    Feasible bottom60 top60 (Sum.elim (MainTheory.OrderSevenMoment60.pattern s t) (MainTheory.OrderSevenMoment60.pattern s t)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSevenMoment60.pattern,Fin.sum_univ_succ]
    ring
  · norm_num [MainTheory.OrderSevenMoment60.pattern,Fin.sum_univ_succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom60,top60,bits,SS.complement,MainTheory.OrderSevenMoment60.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom60,top60,bits,SS.complement,MainTheory.OrderSevenMoment60.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

theorem feasible61 (s t : ℝ)
    (hn : ∀ i,0 ≤ (MainTheory.OrderSevenMoment61.pattern s t) i) :
    Feasible bottom61 top61 (Sum.elim (MainTheory.OrderSevenMoment61.pattern s t) (MainTheory.OrderSevenMoment61.pattern s t)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSevenMoment61.pattern,Fin.sum_univ_succ]
    ring
  · norm_num [MainTheory.OrderSevenMoment61.pattern,Fin.sum_univ_succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom61,top61,bits,SS.complement,MainTheory.OrderSevenMoment61.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom61,top61,bits,SS.complement,MainTheory.OrderSevenMoment61.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

end MainTheory.OrderSevenMomentSufficiency
