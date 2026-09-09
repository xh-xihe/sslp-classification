import MainTheory.OrderSevenMoment58

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderSeven58MomentPoint

open MainTheory.OrderSevenMoment58

theorem nonneg_iff (s t : ℝ) : (∀ i,0 ≤ pattern s t i) ↔
    0 ≤ s ∧ 0 ≤ t ∧ 1/7 ≤ s+t ∧ s+t ≤ 5/14 ∧ s ≤ 3/14 ∧ t ≤ 2/7 := by
  constructor
  · intro h
    have h0 := h 0
    have h3 := h 3
    have h4 := h 4
    have h6 := h 6
    have h7 := h 7
    have h8 := h 8
    change 0 ≤ t at h0
    change 0 ≤ s at h3
    change 0 ≤ 5/14-s-t at h4
    change 0 ≤ 2/7-t at h6
    change 0 ≤ 3/14-s at h7
    change 0 ≤ s+t-1/7 at h8
    exact ⟨h3,h0,by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨hs,ht,hst,hst',hs',ht'⟩ i
    fin_cases i <;> norm_num [pattern,Fin.succ] <;> linarith

theorem first_linear (s t : ℝ) :
    pattern s t 0*pattern s t 8=pattern s t 4*pattern s t 6 ↔ 28*s+49*t=10 := by
  change t*(s+t-1/7)=(5/14-s-t)*(2/7-t) ↔ _
  constructor <;> intro h <;> nlinarith

theorem second_linear (s t : ℝ) :
    pattern s t 0*pattern s t 7=pattern s t 3*pattern s t 6 ↔ 4*s=3*t := by
  change t*(3/14-s)=s*(2/7-t) ↔ _
  constructor <;> intro h <;> nlinarith

theorem unique_parameters (s t : ℝ) (h1 : 28*s+49*t=10) (h2 : 4*s=3*t) :
    s=3/28 ∧ t=1/7 := by constructor <;> linarith

theorem forced_vector : pattern (3/28) (1/7)=
    ![1/7,1/14,1/14,3/28,3/28,1/7,1/7,3/28,3/28] := by
  ext i
  fin_cases i <;> norm_num [pattern,Fin.succ]

theorem forced_positive : ∀ i,0 < pattern (3/28) (1/7) i := by
  intro i
  fin_cases i <;> norm_num [pattern,Fin.succ]

end MainTheory.OrderSeven58MomentPoint
