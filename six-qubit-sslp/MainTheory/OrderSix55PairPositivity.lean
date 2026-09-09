import MainTheory.OrderSix55Boundary

set_option autoImplicit false

namespace MainTheory.OrderSix55PairPositivity

open MainTheory.OrderSixMoment55

theorem positive_pairs (a b g d : ℝ) (hn : ∀ i,0 ≤ pattern a b g d i) :
    0<pattern a b g d 2+pattern a b g d 3 ∧
    0<pattern a b g d 4+pattern a b g d 5 ∧
    0<pattern a b g d 9+pattern a b g d 10 := by
  obtain ⟨h1,h2,h3⟩ := MainTheory.OrderSix55Boundary.pair_sums a b g d
  rw [h1,h2,h3]
  exact ⟨by linarith [hn 8],by linarith [hn 7],by linarith [hn 0]⟩

end MainTheory.OrderSix55PairPositivity
