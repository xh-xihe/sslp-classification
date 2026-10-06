import MainTheory.OrderFour25CoordinateMoments
import SixQubit.CodeBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25Diagonal
open MainTheory.OrderFour25Support
open SixQubit.Orbit25
open MainTheory.OrderFour25CoordinateMoments
theorem bottom_alias : ∀ i,bottom i=(![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11] : Fin 12 → SS.BitString 6) i := by decide +kernel
theorem top_alias : ∀ i,top i=(![z4,z3,z2,z1,z0,z5,z10,z9,z8,z7,z6,z11] : Fin 12 → SS.BitString 6) i := by decide +kernel
noncomputable def K0 (c : SS.State 6 ℂ) : ℂ :=
  star (c (anchor false))*c (anchor true)+∑ j : Fin 5,star (c (hat false j))*c (hat true j)
noncomputable def K1 (d : SS.State 6 ℂ) : ℂ :=
  (∑ j : Fin 5,star (d (tail false j))*d (tail true j))+star (d (full false))*d (full true)
theorem K0_expanded (c : SS.State 6 ℂ) : K0 c=(star (c y0)*c y6)+(star (c y1)*c y7)+(star (c y2)*c y8)+(star (c y3)*c y9)+(star (c y4)*c y10)+(star (c y5)*c y11) := by
  simp only [K0,anchor_index,hat_index,bottom_alias,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change (star (c y0)*c y6)+((star (c y1)*c y7)+((star (c y2)*c y8)+((star (c y3)*c y9)+((star (c y4)*c y10)+((star (c y5)*c y11)+0)))))=(star (c y0)*c y6)+(star (c y1)*c y7)+(star (c y2)*c y8)+(star (c y3)*c y9)+(star (c y4)*c y10)+(star (c y5)*c y11)
  ring
theorem K1_expanded (d : SS.State 6 ℂ) : K1 d=(star (d z0)*d z6)+(star (d z1)*d z7)+(star (d z2)*d z8)+(star (d z3)*d z9)+(star (d z4)*d z10)+(star (d z5)*d z11) := by
  simp only [K1,tail_index,full_index,top_alias,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change ((star (d z4)*d z10)+((star (d z3)*d z9)+((star (d z2)*d z8)+((star (d z1)*d z7)+((star (d z0)*d z6)+0)))))+(star (d z5)*d z11)=(star (d z0)*d z6)+(star (d z1)*d z7)+(star (d z2)*d z8)+(star (d z3)*d z9)+(star (d z4)*d z10)+(star (d z5)*d z11)
  ring
theorem equal_of_KL (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : K0 c=K1 d := by
  have h0 := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide)
  have h6 := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef5 w6 (by decide)
  change diagBot c ef5 w0=diagTop d ef5 w0 at h0
  change diagBot c ef5 w6=diagTop d ef5 w6 at h6
  rw [dbot_w0,dtop_w0] at h0
  rw [dbot_w6,dtop_w6] at h6
  rw [K0_expanded,K1_expanded]
  linear_combination (1/2 : ℂ)*(h0-h6)
end MainTheory.OrderFour25Diagonal
