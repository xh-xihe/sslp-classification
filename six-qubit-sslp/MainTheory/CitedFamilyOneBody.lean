import MainTheory.CitedFamilyMomentSemantics
import MainTheory.WImageIntrinsicBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.CitedFamilyOneBody

open SixQubit.Realize MainTheory.CitedFamilyMomentData MainTheory.CitedFamilyMomentSemantics
open MainTheory.FiveQubitCitedGateSemantics MainTheory.WImageIntrinsicBridge MainTheory.CodeSpec

theorem gram (i j : Fin 2) (b b' : Bool) :
    SS.innerC (word i b) (word j b')=if i=j ∧ b=b' then 1 else 0 := by
  rw [← pauliAct_identity (word j b')]
  rw [word,word,matElt_eq scale _ _ L L_nodup (fun x hx => False.elim (hx (L_complete x)))]
  rw [identityPauli_numY,pow_zero,mul_one]
  simp only [identityPauli,MainTheory.CitedFamilyMomentData.gram]
  split_ifs
  · exact mass_scale
  · simp

theorem numY_zero_of_x (P : SS.PauliString 6) (h : num P.x=0) : P.numY=0 := by
  have hx : P.x=(fun _ => false) := by
    rw [← nbit_num P.x,h]
    decide +kernel
  simp [SS.PauliString.numY,hx]

theorem single_element (P : SS.PauliString 6) (hw : P.wt=1)
    (i j : Fin 2) (b b' : Bool) :
    SS.innerC (word i b) (SS.pauliAct P (word j b'))=
      if num P.x=0 ∧ num P.z=32 ∧ i=j ∧ b=b' then (if b then -1 else 1) else 0 := by
  have h := single_pauli (num P.x) (num_lt P.x) (num P.z) (num_lt P.z)
    (by simpa only [nbit_num] using hw) i j b b'
  simp only [nbit_num] at h
  rw [word,word,matElt_eq scale _ _ L L_nodup (fun x hx => False.elim (hx (L_complete x))),h]
  split_ifs with hh hb
  · rw [numY_zero_of_x P hh.1,pow_zero,mul_one,toC_neg,mul_neg,mass_scale]
  · rw [numY_zero_of_x P hh.1,pow_zero,mul_one,mass_scale]
  · simp

theorem family_single (theta : ℝ) (P : SS.PauliString 6) (hw : P.wt=1) (i j : Fin 2) :
    SS.innerC (MainTheory.CitedAncillaFamily.code theta i)
      (SS.pauliAct P (MainTheory.CitedAncillaFamily.code theta j))=
      if num P.x=0 ∧ num P.z=32 ∧ i=j then (Real.cos theta : ℂ) else 0 := by
  simp only [expansion,pauliAct_add,pauliAct_smul,innerC_add_left,innerC_add_right,
    innerC_smul_left,innerC_smul_right,single_element P hw]
  by_cases hh : num P.x=0 ∧ num P.z=32 ∧ i=j
  · simp only [hh.1,hh.2.1,hh.2.2,true_and,if_true,Bool.false_eq_true,
      Bool.true_eq_false,if_false,Complex.star_def,Complex.conj_ofReal]
    have hcos : Real.cos theta=Real.cos (theta/2)^2-Real.sin (theta/2)^2 := by
      have ht := Real.cos_two_mul (theta/2)
      rw [show 2*(theta/2)=theta by ring] at ht
      nlinarith [Real.sin_sq_add_cos_sq (theta/2)]
    rw [hcos]
    push_cast
    ring
  · have hfalse (b b' : Bool) : ¬(num P.x=0 ∧ num P.z=32 ∧ i=j ∧ b=b') :=
      fun h => hh ⟨h.1,h.2.1,h.2.2.1⟩
    simp only [if_neg hh,if_neg (hfalse _ _),and_true,mul_zero,add_zero]

theorem family_gram (theta : ℝ) (i j : Fin 2) :
    SS.innerC (MainTheory.CitedAncillaFamily.code theta i)
      (MainTheory.CitedAncillaFamily.code theta j)=if i=j then 1 else 0 := by
  simp only [expansion,innerC_add_left,innerC_add_right,innerC_smul_left,innerC_smul_right,gram]
  by_cases h : i=j
  · subst j
    simp only [true_and,if_true,Bool.false_eq_true,Bool.true_eq_false,if_false,
      Complex.star_def,Complex.conj_ofReal,mul_zero,mul_one,zero_add,add_zero]
    have ht := Real.sin_sq_add_cos_sq (theta/2)
    exact_mod_cast (by nlinarith [ht] : Real.cos (theta/2)*Real.cos (theta/2)+
      Real.sin (theta/2)*Real.sin (theta/2)=1)
  · simp [h]

end MainTheory.CitedFamilyOneBody
