import MainTheory.OrderFour26Moments
set_option autoImplicit false
namespace MainTheory.OrderFour26MomentRegion
open MainTheory.OrderFour26Moments

theorem hexagon (a b : ℝ) : (∀ i,0 ≤ pattern a b i) ↔
    0 ≤ a ∧ a ≤ 1/4 ∧ 0 ≤ b ∧ b ≤ 1/4 ∧ 1/8 ≤ a+b ∧ a+b ≤ 3/8 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    change 0 ≤ a+b-1/8 at h0
    change 0 ≤ 3/8-a-b at h1
    change 0 ≤ 1/4-a at h2
    change 0 ≤ a at h3
    change 0 ≤ 1/4-b at h4
    change 0 ≤ b at h5
    exact ⟨h3,by linarith,h5,by linarith,by linarith,by linarith⟩
  · rintro ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ i
    fin_cases i <;> norm_num [pattern,Fin.succ] <;> linarith

theorem pair_sums (a b : ℝ) :
    pattern a b 0+pattern a b 1=1/4 ∧ pattern a b 2+pattern a b 3=1/4 ∧
    pattern a b 4+pattern a b 5=1/4 ∧ pattern a b 6+pattern a b 7=1/4 := by
  change (a+b-1/8)+(3/8-a-b)=1/4 ∧ (1/4-a)+a=1/4 ∧ (1/4-b)+b=1/4 ∧ (1/8 : ℝ)+1/8=1/4
  refine ⟨?_,?_,?_,?_⟩ <;> ring

theorem parity_sums (a b : ℝ) :
    pattern a b 0+pattern a b 2+pattern a b 4=3/8 ∧
    pattern a b 1+pattern a b 3+pattern a b 5=3/8 := by
  change (a+b-1/8)+(1/4-a)+(1/4-b)=3/8 ∧ (3/8-a-b)+a+b=3/8
  constructor <;> ring

end MainTheory.OrderFour26MomentRegion
