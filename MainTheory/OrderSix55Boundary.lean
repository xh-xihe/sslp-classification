import MainTheory.OrderSixMoment55

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSix55Boundary

theorem positive_six (p : Fin 11 → ℝ) (hn : ∀ i,0 ≤ p i)
    (hs23 : 0<p 2+p 3) (hs45 : 0<p 4+p 5) (hs910 : 0<p 9+p 10)
    (hl1 : p 9+p 2+p 4=1/4) (hl2 : p 5+p 10+p 3=1/4)
    (hm1 : p 2*p 10=p 3*p 9) (hm3 : p 2*p 5=p 3*p 4) :
    0<p 2 ∧ 0<p 3 ∧ 0<p 4 ∧ 0<p 5 ∧ 0<p 9 ∧ 0<p 10 := by
  have h2 : 0<p 2 := by
    by_contra h
    have hz : p 2=0 := le_antisymm (le_of_not_gt h) (hn 2)
    have h3 : 0<p 3 := by linarith
    have hz9 : p 9=0 := (mul_eq_zero.mp (show p 3*p 9=0 by rw [← hm1,hz,zero_mul])).resolve_left (ne_of_gt h3)
    have hz4 : p 4=0 := (mul_eq_zero.mp (show p 3*p 4=0 by rw [← hm3,hz,zero_mul])).resolve_left (ne_of_gt h3)
    rw [hz9,hz,hz4] at hl1
    norm_num at hl1
  have h3 : 0<p 3 := by
    by_contra h
    have hz : p 3=0 := le_antisymm (le_of_not_gt h) (hn 3)
    have hz10 : p 10=0 := (mul_eq_zero.mp (show p 2*p 10=0 by rw [hm1,hz,zero_mul])).resolve_left (ne_of_gt h2)
    have hz5 : p 5=0 := (mul_eq_zero.mp (show p 2*p 5=0 by rw [hm3,hz,zero_mul])).resolve_left (ne_of_gt h2)
    rw [hz5,hz10,hz] at hl2
    norm_num at hl2
  have h4 : 0<p 4 := by
    by_contra h
    have hz : p 4=0 := le_antisymm (le_of_not_gt h) (hn 4)
    have h5 : 0<p 5 := by linarith
    have hp := mul_pos h2 h5
    rw [hm3,hz,mul_zero] at hp
    exact (lt_irrefl 0) hp
  have h5 : 0<p 5 := by
    have hp := mul_pos h3 h4
    rw [← hm3] at hp
    exact (mul_pos_iff.mp hp).resolve_right (by rintro ⟨h,_⟩; linarith) |>.2
  have h9 : 0<p 9 := by
    by_contra h
    have hz : p 9=0 := le_antisymm (le_of_not_gt h) (hn 9)
    have h10 : 0<p 10 := by linarith
    have hp := mul_pos h2 h10
    rw [hm1,hz,mul_zero] at hp
    exact (lt_irrefl 0) hp
  have h10 : 0<p 10 := by
    have hp := mul_pos h3 h9
    rw [← hm1] at hp
    exact (mul_pos_iff.mp hp).resolve_right (by rintro ⟨h,_⟩; linarith) |>.2
  exact ⟨h2,h3,h4,h5,h9,h10⟩

open MainTheory.OrderSixMoment55

theorem pair_sums (a b g d : ℝ) :
    pattern a b g d 2+pattern a b g d 3=pattern a b g d 8+1/12 ∧
    pattern a b g d 4+pattern a b g d 5=pattern a b g d 7+1/12 ∧
    pattern a b g d 9+pattern a b g d 10=pattern a b g d 0+1/12 := by
  change g+b=(b+g-1/12)+1/12 ∧
    a+(5/12-a-b-g-d)=(1/3-b-g-d)+1/12 ∧
    (1/4-a-g)+(a+g+d-1/6)=d+1/12
  constructor
  · ring
  constructor <;> ring

theorem of_pattern (a b g d : ℝ) (hn : ∀ i,0 ≤ pattern a b g d i)
    (hm1 : pattern a b g d 2*pattern a b g d 10=pattern a b g d 3*pattern a b g d 9)
    (hm3 : pattern a b g d 2*pattern a b g d 5=pattern a b g d 3*pattern a b g d 4) :
    0<pattern a b g d 2 ∧ 0<pattern a b g d 3 ∧ 0<pattern a b g d 4 ∧
    0<pattern a b g d 5 ∧ 0<pattern a b g d 9 ∧ 0<pattern a b g d 10 := by
  obtain ⟨h23,h45,h910⟩ := pair_sums a b g d
  apply positive_six _ hn
  · rw [h23]
    linarith [hn 8]
  · rw [h45]
    linarith [hn 7]
  · rw [h910]
    linarith [hn 0]
  · change (1/4-a-g)+g+a=1/4
    ring
  · change (5/12-a-b-g-d)+(a+g+d-1/6)+b=1/4
    ring
  · exact hm1
  · exact hm3

end MainTheory.OrderSix55Boundary
