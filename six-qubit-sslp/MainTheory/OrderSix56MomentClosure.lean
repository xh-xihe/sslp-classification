import MainTheory.OrderSixMoment56

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.OrderSix56MomentClosure

theorem equal_parameters (r s : ℝ) : s*(1/6-r)=r*(1/6-s) ↔ r=s := by
  constructor <;> intro h <;> nlinarith

theorem first_equation (r : ℝ) : r*(2*r-1/12)=(1/4-2*r)*(1/6-r) ↔ 12*r=1 := by
  constructor <;> intro h <;> nlinarith

open MainTheory.OrderSixMoment56

theorem parameters (r s t : ℝ)
    (h1 : pattern r s t 3*pattern r s t 7=pattern r s t 4*pattern r s t 6)
    (h3 : pattern r s t 2*pattern r s t 6=pattern r s t 3*pattern r s t 5) :
    r=1/12 ∧ s=1/12 := by
  have he := (equal_parameters r s).1 h3
  change r*(r+s-1/12)=(1/4-r-s)*(1/6-r) at h1
  rw [← he] at h1
  have hr : 12*r=1 := by nlinarith
  exact ⟨by linarith,by linarith⟩

theorem forced : pattern (1/12) (1/12) (1/12)=
    ![1/12,1/6,1/12,1/12,1/12,1/12,1/12,1/12,1/12,1/6] := by
  ext i
  fin_cases i <;> norm_num [pattern,Fin.succ]

theorem positive : ∀ i,0<pattern (1/12) (1/12) (1/12) i := by
  intro i
  fin_cases i <;> norm_num [pattern,Fin.succ]

end MainTheory.OrderSix56MomentClosure
