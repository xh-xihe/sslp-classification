import MainTheory.Orbit9EnumeratorDisplays

set_option autoImplicit false

namespace MainTheory.OrderTwoEnumeratorDisplays

open SS.MacWilliams

theorem E1_normalized (psi : Fin 2 → SS.State 6 ℂ)
    (hA : IsE1A psi) (hB : IsE1B psi) :
    (fun j : Fin 7 => Aco psi j/4)=![1,1,0,0,15,15,0] ∧
    (fun j : Fin 7 => Bco psi j/4)=![1,1,0,30,45,33,18] := by
  obtain ⟨ha0,ha1,ha2,ha3,ha4,ha5,ha6⟩ := hA
  obtain ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6⟩ := hB
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [ha0,ha1,ha2,ha3,ha4,ha5,ha6,hb0,hb1,hb2,hb3,hb4,hb5,hb6]

theorem shadow (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) (hd : SS.HasDistance psi 3) :
    Aco psi 1/4+Aco psi 2/4+Aco psi 3/4 ≤ 1 := by
  have h := SS.Shadow.shadow_bound psi hd (SixQubit.Pin.Aco_zero psi hnorm)
  linarith

theorem forced_low (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) (hd : SS.HasDistance psi 3)
    (G : SS.PauliString 6) (hG : ∀ i,SS.pauliAct G (psi i)=psi i) :
    (G.wt=1 → Aco psi 1/4=1 ∧ Aco psi 2/4=0 ∧ Aco psi 3/4=0) ∧
    (G.wt=2 → Aco psi 1/4=0 ∧ Aco psi 2/4=1 ∧ Aco psi 3/4=0) := by
  have h0 := SixQubit.Pin.Aco_zero psi hnorm
  constructor
  · intro hw
    obtain ⟨h1,hrest⟩ := SixQubit.Pin.pin_low psi hd h0 hnorm G hG 1 (by omega) hw
    have h2 := hrest 2 (by omega) (by omega)
    have h3 := hrest 3 (by omega) (by omega)
    norm_num [h1,h2,h3]
  · intro hw
    obtain ⟨h2,hrest⟩ := SixQubit.Pin.pin_low psi hd h0 hnorm G hG 2 (by omega) hw
    have h1 := hrest 1 (by omega) (by omega)
    have h3 := hrest 3 (by omega) (by omega)
    norm_num [h1,h2,h3]

def repetition : Matrix (Fin 4) (Fin 2) ℂ := !![1,0; 0,0; 0,0; 0,1]

theorem repetition_basis : repetition.mulVec ![1,0]=![1,0,0,0] ∧
    repetition.mulVec ![0,1]=![0,0,0,1] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [repetition,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem repetition_isometry : repetition.conjTranspose*repetition=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [repetition,Matrix.mul_apply,Fin.sum_univ_succ]

end MainTheory.OrderTwoEnumeratorDisplays
