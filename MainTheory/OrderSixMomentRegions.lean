import MainTheory.OrderSixMoment53
import MainTheory.OrderSixMoment54
import MainTheory.OrderSixMoment55
import MainTheory.OrderSixMoment56

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSixMomentRegions

theorem region53 (r s t : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSixMoment53.pattern r s t i) ↔
    0 ≤ r ∧ r ≤ 1/6 ∧ 0 ≤ s ∧ s ≤ 1/6 ∧ 0 ≤ t ∧ t ≤ 1/3 ∧ 1/4 ≤ r+s+t ∧ r+s+t ≤ 5/12 := by
  constructor
  · intro h
    have h0 := h 0
    change 0 ≤ t at h0
    have h1 := h 1
    change 0 ≤ 1/12 at h1
    have h2 := h 2
    change 0 ≤ 1/12 at h2
    have h3 := h 3
    change 0 ≤ 1/3-t at h3
    have h4 := h 4
    change 0 ≤ s at h4
    have h5 := h 5
    change 0 ≤ r at h5
    have h6 := h 6
    change 0 ≤ 5/12-r-s-t at h6
    have h7 := h 7
    change 0 ≤ 1/6-s at h7
    have h8 := h 8
    change 0 ≤ 1/6-r at h8
    have h9 := h 9
    change 0 ≤ r+s+t-1/4 at h9
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · intro h i
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    fin_cases i <;> norm_num [MainTheory.OrderSixMoment53.pattern,Fin.succ] <;> linarith

theorem region54 (s t : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSixMoment54.pattern s t i) ↔
    0 ≤ s ∧ s ≤ 1/4 ∧ 0 ≤ t ∧ t ≤ 1/4 ∧ 1/6 ≤ s+t ∧ s+t ≤ 5/12 := by
  constructor
  · intro h
    have h0 := h 0
    change 0 ≤ t at h0
    have h1 := h 1
    change 0 ≤ 1/12 at h1
    have h2 := h 2
    change 0 ≤ 1/12 at h2
    have h3 := h 3
    change 0 ≤ 1/12 at h3
    have h4 := h 4
    change 0 ≤ 1/4-t at h4
    have h5 := h 5
    change 0 ≤ s at h5
    have h6 := h 6
    change 0 ≤ 5/12-s-t at h6
    have h7 := h 7
    change 0 ≤ 1/4-s at h7
    have h8 := h 8
    change 0 ≤ s+t-1/6 at h8
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · intro h i
    rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
    fin_cases i <;> norm_num [MainTheory.OrderSixMoment54.pattern,Fin.succ] <;> linarith

theorem region55 (a b g d : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSixMoment55.pattern a b g d i) ↔
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ g ∧ 0 ≤ d ∧ a+b+g+d ≤ 5/12 ∧ b+g+d ≤ 1/3 ∧ 1/12 ≤ b+g ∧ a+g ≤ 1/4 ∧ 1/6 ≤ a+g+d := by
  constructor
  · intro h
    have h0 := h 0
    change 0 ≤ d at h0
    have h1 := h 1
    change 0 ≤ 1/12 at h1
    have h2 := h 2
    change 0 ≤ g at h2
    have h3 := h 3
    change 0 ≤ b at h3
    have h4 := h 4
    change 0 ≤ a at h4
    have h5 := h 5
    change 0 ≤ 5/12-a-b-g-d at h5
    have h6 := h 6
    change 0 ≤ 1/6 at h6
    have h7 := h 7
    change 0 ≤ 1/3-b-g-d at h7
    have h8 := h 8
    change 0 ≤ b+g-1/12 at h8
    have h9 := h 9
    change 0 ≤ 1/4-a-g at h9
    have h10 := h 10
    change 0 ≤ a+g+d-1/6 at h10
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · intro h i
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    fin_cases i <;> norm_num [MainTheory.OrderSixMoment55.pattern,Fin.succ] <;> linarith

theorem region56 (r s t : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSixMoment56.pattern r s t i) ↔
    0 ≤ t ∧ t ≤ 1/6 ∧ 0 ≤ r ∧ r ≤ 1/6 ∧ 0 ≤ s ∧ s ≤ 1/6 ∧ 1/12 ≤ r+s ∧ r+s ≤ 1/4 := by
  constructor
  · intro h
    have h0 := h 0
    change 0 ≤ t at h0
    have h1 := h 1
    change 0 ≤ 1/4-t at h1
    have h2 := h 2
    change 0 ≤ s at h2
    have h3 := h 3
    change 0 ≤ r at h3
    have h4 := h 4
    change 0 ≤ 1/4-r-s at h4
    have h5 := h 5
    change 0 ≤ 1/6-s at h5
    have h6 := h 6
    change 0 ≤ 1/6-r at h6
    have h7 := h 7
    change 0 ≤ r+s-1/12 at h7
    have h8 := h 8
    change 0 ≤ 1/6-t at h8
    have h9 := h 9
    change 0 ≤ t+1/12 at h9
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · intro h i
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    fin_cases i <;> norm_num [MainTheory.OrderSixMoment56.pattern,Fin.succ] <;> linarith

end MainTheory.OrderSixMomentRegions
