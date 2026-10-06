import SixQubit.Orbit9UniversalFinal
import SixQubit.Orbit9Magnitudes

set_option autoImplicit false

namespace MainTheory.Orbit9EnumeratorDisplays

open SixQubit.Orbit9Universal SS.MacWilliams

theorem normalized_enumerators (psi : Fin 2 → SS.State 6 ℂ)
    (hA : IsE2A psi) (hB : IsE2B psi) :
    (fun j : Fin 7 => Aco psi j/4)=![1,0,1,0,11,16,3] ∧
    (fun j : Fin 7 => Bco psi j/4)=![1,0,1,24,35,40,27] := by
  obtain ⟨ha0,ha1,ha2,ha3,ha4,ha5,ha6⟩ := hA
  obtain ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6⟩ := hB
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [ha0,ha1,ha2,ha3,ha4,ha5,ha6,hb0,hb1,hb2,hb3,hb4,hb5,hb6]

theorem uniform_enumerators (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (fun j : Fin 7 => Aco ![c,d] j/4)=![1,0,1,0,11,16,3] ∧
    (fun j : Fin 7 => Bco ![c,d] j/4)=![1,0,1,24,35,40,27] := by
  have hfour := active_card_eq_four_of_ne_two c d H (active_card_ne_two c d H)
  obtain ⟨hA,hB⟩ := enumerator_of_active_card_four c d H hfour
  exact normalized_enumerators ![c,d] hA hB

theorem first_three (c d : SS.State 6 ℂ) (H : FullKL c d) :
    Aco ![c,d] 1/4=0 ∧ Aco ![c,d] 2/4=1 ∧ Aco ![c,d] 3/4=0 := by
  have h := (uniform_enumerators c d H).1
  exact ⟨congrFun h 1,congrFun h 2,congrFun h 3⟩

theorem active_edge_from_p (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b)
    (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b)
    (i j : Fin 6) (hij : i ≠ j) (hi : i ≠ a ∧ i ≠ b) (hj : j ≠ a ∧ j ≠ b) :
    r c i j=p c i+p c j-1/12 := by
  have hpi := singleton_magnitude_formula_of_equal_pair c d H a b hab hc hd i
  have hpj := singleton_magnitude_formula_of_equal_pair c d H a b hab hc hd j
  have hr := edge_magnitude_formula_of_equal_pair c d H a b hab hc hd i j
  simp [expectedEdgeMagnitude,hij,hi.1,hi.2,hj.1,hj.2] at hpi hpj hr
  linarith

end MainTheory.Orbit9EnumeratorDisplays
