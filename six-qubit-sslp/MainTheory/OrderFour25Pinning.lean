import Mathlib

set_option autoImplicit false
namespace MainTheory.OrderFour25Pinning

theorem tail_parameter (a0 a1 t : ℝ) (hs : a0+a1=3/8)
    (h : a0*(1/8-t)=a1*t) : a0=3*t := by linear_combination 8*h+8*t*hs

theorem branches (t sigma T : ℝ) (hT : T=5*t+sigma)
    (ha : 3/8-3*T/4+sigma=3*t)
    (hmag : (3/8-3*T/4+sigma)*(1/8-t)=(1/8-T/4+t)*(3/8-sigma)) :
    (T-1)*(2*T-1)=0 := by
  have ht : t=3/64+T/32 := by linarith
  have hs : sigma=27*T/32-15/64 := by linarith
  rw [ht,hs] at hmag
  nlinarith

theorem excluded_branch (t sigma T : ℝ) (hT : T=5*t+sigma)
    (ha : 3/8-3*T/4+sigma=3*t) (h : T=1) :
    t=5/64 ∧ sigma=39/64 ∧ 3/8-sigma < 0 := by
  refine ⟨?_,?_,?_⟩ <;> linarith

theorem forced (t sigma T : ℝ) (hT : T=5*t+sigma)
    (ha : 3/8-3*T/4+sigma=3*t)
    (hmag : (3/8-3*T/4+sigma)*(1/8-t)=(1/8-T/4+t)*(3/8-sigma))
    (hn : 0 ≤ 3/8-sigma) : T=1/2 ∧ t=1/16 ∧ sigma=3/16 := by
  have hb := branches t sigma T hT ha hmag
  rcases mul_eq_zero.mp hb with h | h
  · have he := excluded_branch t sigma T hT ha (by linarith)
    linarith [he.2.2]
  · refine ⟨?_,?_,?_⟩ <;> linarith

theorem pair_sums (t sigma T : ℝ) :
    (3/8-3*T/4+sigma)+(3*T/4-sigma)=3/8 ∧
    (1/8-T/4+t)+(T/4-t)=1/8 := by constructor <;> ring

theorem coherence_equality (A S : ℂ)
    (h : A-(5/3)*S=S-(5/3)*A) : A=S := by linear_combination (3/8 : ℂ)*h

theorem coherence_contradiction (A S : ℂ) (hn : A ≠ 0)
    (he : A-(5/3)*S=S-(5/3)*A) (ho : S= -A) : False := by
  have h := coherence_equality A S he
  apply hn
  linear_combination (1/2 : ℂ)*(h+ho)

end MainTheory.OrderFour25Pinning
