import MainTheory.OrderSixMoment53
import MainTheory.OrderSixMoment54
import MainTheory.OrderSixMoment56

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSixMomentPinning

theorem half_parameter (r t : ℝ) : t*(1/6-r)=(1/3-t)*r ↔ r=t/2 := by
  constructor <;> intro h <;> nlinarith

theorem first53 (t : ℝ) : t*(2*t-1/4)=(1/3-t)*(5/12-2*t) ↔ 6*t=1 := by
  constructor <;> intro h <;> nlinarith

theorem parameters53 (r s t : ℝ)
    (h1 : MainTheory.OrderSixMoment53.pattern r s t 0*MainTheory.OrderSixMoment53.pattern r s t 9=
      MainTheory.OrderSixMoment53.pattern r s t 3*MainTheory.OrderSixMoment53.pattern r s t 6)
    (h2 : MainTheory.OrderSixMoment53.pattern r s t 0*MainTheory.OrderSixMoment53.pattern r s t 8=
      MainTheory.OrderSixMoment53.pattern r s t 3*MainTheory.OrderSixMoment53.pattern r s t 5)
    (h3 : MainTheory.OrderSixMoment53.pattern r s t 0*MainTheory.OrderSixMoment53.pattern r s t 7=
      MainTheory.OrderSixMoment53.pattern r s t 3*MainTheory.OrderSixMoment53.pattern r s t 4) :
    r=1/12 ∧ s=1/12 ∧ t=1/6 := by
  have hr := (half_parameter r t).1 h2
  have hs := (half_parameter s t).1 h3
  change t*(r+s+t-1/4)=(1/3-t)*(5/12-r-s-t) at h1
  rw [hr,hs] at h1
  have ht : 6*t=1 := by nlinarith
  exact ⟨by linarith,by linarith,by linarith⟩

theorem forced53 : MainTheory.OrderSixMoment53.pattern (1/12) (1/12) (1/6)=
    ![1/6,1/12,1/12,1/6,1/12,1/12,1/12,1/12,1/12,1/12] := by
  ext i
  fin_cases i <;> norm_num [MainTheory.OrderSixMoment53.pattern,Fin.succ]

theorem positive53 : ∀ i,0 < MainTheory.OrderSixMoment53.pattern (1/12) (1/12) (1/6) i := by
  intro i
  fin_cases i <;> norm_num [MainTheory.OrderSixMoment53.pattern,Fin.succ]

theorem equal54 (s t : ℝ) : t*(1/4-s)=(1/4-t)*s ↔ t=s := by
  constructor <;> intro h <;> nlinarith

theorem first54 (t : ℝ) : t*(2*t-1/6)=(1/4-t)*(5/12-2*t) ↔ 36*t=5 := by
  constructor <;> intro h <;> nlinarith

theorem parameters54 (s t : ℝ)
    (h1 : MainTheory.OrderSixMoment54.pattern s t 0*MainTheory.OrderSixMoment54.pattern s t 8=
      MainTheory.OrderSixMoment54.pattern s t 4*MainTheory.OrderSixMoment54.pattern s t 6)
    (h2 : MainTheory.OrderSixMoment54.pattern s t 0*MainTheory.OrderSixMoment54.pattern s t 7=
      MainTheory.OrderSixMoment54.pattern s t 4*MainTheory.OrderSixMoment54.pattern s t 5) :
    t=5/36 ∧ s=5/36 := by
  have he := (equal54 s t).1 h2
  change t*(s+t-1/6)=(1/4-t)*(5/12-s-t) at h1
  rw [← he] at h1
  have ht : 36*t=5 := by nlinarith
  exact ⟨by linarith,by linarith⟩

theorem forced54 : MainTheory.OrderSixMoment54.pattern (5/36) (5/36)=
    ![5/36,1/12,1/12,1/12,1/9,5/36,5/36,1/9,1/9] := by
  ext i
  fin_cases i <;> norm_num [MainTheory.OrderSixMoment54.pattern,Fin.succ]

theorem positive54 : ∀ i,0 < MainTheory.OrderSixMoment54.pattern (5/36) (5/36) i := by
  intro i
  fin_cases i <;> norm_num [MainTheory.OrderSixMoment54.pattern,Fin.succ]

theorem first56 (t : ℝ) : t*(t+1/12)=(1/4-t)*(1/6-t) ↔ 12*t=1 := by
  constructor <;> intro h <;> nlinarith

theorem parameter56 (r s t : ℝ)
    (h : MainTheory.OrderSixMoment56.pattern r s t 0*MainTheory.OrderSixMoment56.pattern r s t 9=
      MainTheory.OrderSixMoment56.pattern r s t 1*MainTheory.OrderSixMoment56.pattern r s t 8) :
    t=1/12 := by
  have ht := (first56 t).1 h
  linarith

theorem fixed56 (r s : ℝ) : MainTheory.OrderSixMoment56.pattern r s (1/12) 0=1/12 ∧
    MainTheory.OrderSixMoment56.pattern r s (1/12) 8=1/12 ∧
    MainTheory.OrderSixMoment56.pattern r s (1/12) 1=1/6 ∧
    MainTheory.OrderSixMoment56.pattern r s (1/12) 9=1/6 := by
  change (1/12 : ℝ)=1/12 ∧ 1/6-1/12=1/12 ∧ 1/4-1/12=1/6 ∧ 1/12+1/12=1/6
  norm_num

end MainTheory.OrderSixMomentPinning
