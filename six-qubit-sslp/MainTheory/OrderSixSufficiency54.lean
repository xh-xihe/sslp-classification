import MainTheory.OrderSixMoment54

set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace MainTheory.OrderSixSufficiency54
open MainTheory.OrderSixSupportDisplays MainTheory.MomentPolytope
open MainTheory.OrderEightSupportDisplays (bits)

theorem feasible (s t : ℝ) (hn : ∀ i,0 ≤ (MainTheory.OrderSixMoment54.pattern s t) i) :
    Feasible bottom54 top54 (Sum.elim (MainTheory.OrderSixMoment54.pattern s t) (MainTheory.OrderSixMoment54.pattern s t)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hn i
    | inr i => exact hn i
  · norm_num [MainTheory.OrderSixMoment54.pattern,Fin.sum_univ_succ]
    ring
  · norm_num [MainTheory.OrderSixMoment54.pattern,Fin.sum_univ_succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom54,top54,bits,SS.complement,MainTheory.OrderSixMoment54.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom54,top54,bits,SS.complement,MainTheory.OrderSixMoment54.pattern,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

end MainTheory.OrderSixSufficiency54
