import MainTheory.OrderFour25Moments
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderFour25Sufficiency
open MainTheory.OrderFour25Support MainTheory.OrderFour25Moments MainTheory.MomentPolytope
open MainTheory.OrderEightSupportDisplays (bits)

theorem feasible (t : Fin 5 → ℝ) (sigma : ℝ)
    (hb : ∀ i,0 ≤ bot t sigma i) (hu : ∀ i,0 ≤ up t sigma i) :
    Feasible bottom top (Sum.elim (bot t sigma) (up t sigma)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact hb i
    | inr i => exact hu i
  · norm_num [bot,total,Fin.sum_univ_succ,Fin.succ]
    ring
  · norm_num [up,Fin.sum_univ_succ,Fin.succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottom,top,bits,bot,up,total,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottom,top,bits,bot,up,total,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

end MainTheory.OrderFour25Sufficiency
