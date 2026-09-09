import MainTheory.OrderEightMomentFaces

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderEightMomentSufficiency

open MainTheory.OrderEightMomentFaces MainTheory.OrderEightSupportDisplays
open MainTheory.MomentPolytope

theorem patternB_nonneg_iff (t : ℝ) :
    (∀ i, 0 ≤ patternB t i) ↔ 0 ≤ t ∧ t ≤ 3/16 := by
  constructor
  · intro h
    have h0 := h 0
    have h6 := h 6
    change 0 ≤ t at h0
    change 0 ≤ 3/16-t at h6
    exact ⟨h0,by linarith⟩
  · rintro ⟨h0,h1⟩ i
    fin_cases i <;> norm_num [patternB,Fin.succ] <;> linarith

theorem feasible_B (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 3/16) :
    Feasible bottomB topB (Sum.elim (patternB t) (patternB t)) := by
  constructor
  · intro z
    cases z with
    | inl i => exact (patternB_nonneg_iff t).2 ht i
    | inr i => exact (patternB_nonneg_iff t).2 ht i
  · norm_num [patternB,Fin.sum_univ_succ]
    ring
  · norm_num [patternB,Fin.sum_univ_succ]
    ring
  · intro j
    fin_cases j <;>
      norm_num [mean0,mean1,coord,bottomB,topB,bits,SS.complement,patternB,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] <;> ring
  · intro jk
    obtain ⟨⟨j,k⟩,h⟩ := jk
    fin_cases j <;> fin_cases k <;>
      norm_num [second0,second1,coord,bottomB,topB,bits,SS.complement,patternB,
        Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at * <;> ring

end MainTheory.OrderEightMomentSufficiency
