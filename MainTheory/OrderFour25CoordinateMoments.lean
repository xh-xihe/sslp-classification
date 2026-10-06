import MainTheory.OrderFour25Moments

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace MainTheory.OrderFour25CoordinateMoments
open MainTheory.OrderFour25Support MainTheory.OrderFour25Moments
open MainTheory.OrderEightSupportDisplays (bits)

def ai : Bool → Fin 12 := fun b => if b then 6 else 0
def bi : Bool → Fin 5 → Fin 12 := fun b j =>
  (if b then ![7,8,9,10,11] else ![1,2,3,4,5]) j
def ri : Bool → Fin 5 → Fin 12 := fun b j =>
  (if b then ![6,7,8,9,10] else ![0,1,2,3,4]) j
def si : Bool → Fin 12 := fun b => if b then 11 else 5
theorem anchor_index : ∀ b,anchor b=bottom (ai b) := by decide +kernel
theorem hat_index : ∀ b j,hat b j=bottom (bi b j) := by decide +kernel
theorem tail_index : ∀ b j,tail b j=top (ri b j) := by decide +kernel
theorem full_index : ∀ b,full b=top (si b) := by decide +kernel

theorem coordinate_values (t : Fin 5 → ℝ) (sigma : ℝ) :
    bot t sigma (ai false)=3/8-3*(total t sigma)/4+sigma ∧
    bot t sigma (ai true)=3*(total t sigma)/4-sigma ∧
    up t sigma (si false)=3/8-sigma ∧ up t sigma (si true)=sigma ∧
    (∀ j,bot t sigma (bi false j)=1/8-(total t sigma)/4+t j ∧
      bot t sigma (bi true j)=(total t sigma)/4-t j ∧
      up t sigma (ri false j)=1/8-t j ∧ up t sigma (ri true j)=t j) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro j
  fin_cases j <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem total_eq_sum (t : Fin 5 → ℝ) (sigma : ℝ) : total t sigma=sigma+∑ j,t j := by
  simp only [total,Fin.sum_univ_succ]
  change t 0+t 1+t 2+t 3+t 4+sigma=sigma+(t 0+(t 1+(t 2+(t 3+(t 4+0)))))
  ring

end MainTheory.OrderFour25CoordinateMoments
