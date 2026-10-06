import MainTheory.OrderFour25CoordinateMoments
import MainTheory.SupportKetExpansion

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25Expansion
open MainTheory.OrderFour25Support MainTheory.SupportKetExpansion
open MainTheory.OrderFour25CoordinateMoments
open MainTheory.OrderEightSupportDisplays (bits)

theorem bottom_expansion (c : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ SixQubit.Orbit25.S0 → c x=0) :
    c=(∑ b : Bool,c (anchor b) • ket (anchor b))+
      ∑ b : Bool,∑ j : Fin 5,c (hat b j) • ket (hat b j) := by
  calc
    c=∑ i,c (bottom i) • ket (bottom i) :=
      indexed_expansion _ _ bottom_injective bottom_image c hc
    _=_ := by
      simp only [Fin.sum_univ_succ,Fintype.sum_bool,anchor_index,hat_index]
      change ((c (bottom 0) • ket (bottom 0))+((c (bottom 1) • ket (bottom 1))+((c (bottom 2) • ket (bottom 2))+((c (bottom 3) • ket (bottom 3))+((c (bottom 4) • ket (bottom 4))+((c (bottom 5) • ket (bottom 5))+((c (bottom 6) • ket (bottom 6))+((c (bottom 7) • ket (bottom 7))+((c (bottom 8) • ket (bottom 8))+((c (bottom 9) • ket (bottom 9))+((c (bottom 10) • ket (bottom 10))+((c (bottom 11) • ket (bottom 11))+0))))))))))))=((c (bottom 6) • ket (bottom 6))+(c (bottom 0) • ket (bottom 0)))+(((c (bottom 7) • ket (bottom 7))+((c (bottom 8) • ket (bottom 8))+((c (bottom 9) • ket (bottom 9))+((c (bottom 10) • ket (bottom 10))+((c (bottom 11) • ket (bottom 11))+0)))))+((c (bottom 1) • ket (bottom 1))+((c (bottom 2) • ket (bottom 2))+((c (bottom 3) • ket (bottom 3))+((c (bottom 4) • ket (bottom 4))+((c (bottom 5) • ket (bottom 5))+0))))))
      abel

theorem top_expansion (d : SS.State 6 ℂ)
    (hd : ∀ x,x ∉ SixQubit.Orbit25.S1 → d x=0) :
    d=(∑ b : Bool,∑ j : Fin 5,d (tail b j) • ket (tail b j))+
      ∑ b : Bool,d (full b) • ket (full b) := by
  calc
    d=∑ i,d (top i) • ket (top i) :=
      indexed_expansion _ _ top_injective top_image d hd
    _=_ := by
      simp only [Fin.sum_univ_succ,Fintype.sum_bool,tail_index,full_index]
      change ((d (top 0) • ket (top 0))+((d (top 1) • ket (top 1))+((d (top 2) • ket (top 2))+((d (top 3) • ket (top 3))+((d (top 4) • ket (top 4))+((d (top 5) • ket (top 5))+((d (top 6) • ket (top 6))+((d (top 7) • ket (top 7))+((d (top 8) • ket (top 8))+((d (top 9) • ket (top 9))+((d (top 10) • ket (top 10))+((d (top 11) • ket (top 11))+0))))))))))))=(((d (top 6) • ket (top 6))+((d (top 7) • ket (top 7))+((d (top 8) • ket (top 8))+((d (top 9) • ket (top 9))+((d (top 10) • ket (top 10))+0)))))+((d (top 0) • ket (top 0))+((d (top 1) • ket (top 1))+((d (top 2) • ket (top 2))+((d (top 3) • ket (top 3))+((d (top 4) • ket (top 4))+0))))))+((d (top 11) • ket (top 11))+(d (top 5) • ket (top 5)))
      abel

end MainTheory.OrderFour25Expansion
