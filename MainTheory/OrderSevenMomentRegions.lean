import MainTheory.OrderSevenMoment60
import MainTheory.OrderSevenMoment61

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderSevenMomentRegions

theorem region60 (s t : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSevenMoment60.pattern s t i) ↔
    0 ≤ s ∧ s ≤ 1/7 ∧ 0 ≤ t ∧ t ≤ 1/7 ∧ 1/14 ≤ s+t ∧ s+t ≤ 3/14 := by
  constructor
  · intro h
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    change 0 ≤ t at h2
    change 0 ≤ s at h3
    change 0 ≤ 3/14-s-t at h4
    change 0 ≤ 1/7-t at h5
    change 0 ≤ 1/7-s at h6
    change 0 ≤ s+t-1/14 at h7
    exact ⟨h3,by linarith,h2,by linarith,by linarith,by linarith⟩
  · rintro ⟨hs,hs',ht,ht',hst,hst'⟩ i
    fin_cases i <;> norm_num [MainTheory.OrderSevenMoment60.pattern,Fin.succ] <;> linarith

theorem fixed60 (s t : ℝ) : MainTheory.OrderSevenMoment60.pattern s t 0=3/14 ∧
    MainTheory.OrderSevenMoment60.pattern s t 8=2/7 ∧ (0 : ℝ)<3/14 ∧ (0 : ℝ)<2/7 := by
  exact ⟨rfl,rfl,by norm_num,by norm_num⟩

theorem region61 (s t : ℝ) :
    (∀ i,0 ≤ MainTheory.OrderSevenMoment61.pattern s t i) ↔
    0 ≤ t ∧ 1/14 ≤ s ∧ s+t ≤ 3/14 := by
  constructor
  · intro h
    have h0 := h 0
    have h6 := h 6
    have h7 := h 7
    change 0 ≤ t at h0
    change 0 ≤ 3/14-s-t at h6
    change 0 ≤ s-1/14 at h7
    exact ⟨h0,by linarith,by linarith⟩
  · rintro ⟨ht,hs,hst⟩ i
    fin_cases i <;> norm_num [MainTheory.OrderSevenMoment61.pattern,Fin.succ] <;> linarith

theorem positive61 (s t : ℝ) (ht : 0 ≤ t) :
    MainTheory.OrderSevenMoment61.pattern s t 3=3/14 ∧
    MainTheory.OrderSevenMoment61.pattern s t 4=1/7 ∧
    MainTheory.OrderSevenMoment61.pattern s t 8=t+1/14 ∧
    (0 : ℝ)<3/14 ∧ (0 : ℝ)<1/7 ∧ 0<t+1/14 := by
  exact ⟨rfl,rfl,rfl,by norm_num,by norm_num,by linarith⟩

end MainTheory.OrderSevenMomentRegions
