import MainTheory.CitedFamilyFullKLData
import MainTheory.CitedFamilyOneBody

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.CitedFamilyFullKL

open SixQubit.Realize MainTheory.CitedFamilyMomentData MainTheory.CitedFamilyMomentSemantics
open MainTheory.FiveQubitCitedGateSemantics MainTheory.CodeSpec

theorem blocks (P : SS.PauliString 6) (hw : P.wt ≤ 2)
    (i j : Fin 2) (b b' : Bool) :
    SS.innerC (word i b) (SS.pauliAct P (word j b'))=
      if i=j then SS.innerC (word 0 b) (SS.pauliAct P (word 0 b')) else 0 := by
  have h := MainTheory.CitedFamilyFullKLData.checked (num P.x) (num_lt P.x)
    (num P.z) (num_lt P.z) (by simpa only [nbit_num] using hw) i j b b'
  simp only [nbit_num] at h
  simp only [word]
  simp_rw [matElt_eq scale _ _ L L_nodup (fun x hx => False.elim (hx (L_complete x)))]
  rw [h]
  split_ifs <;> simp

theorem condition (theta : ℝ) (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.KLCondition (MainTheory.CitedAncillaFamily.code theta) P := by
  refine ⟨SS.innerC (MainTheory.CitedAncillaFamily.code theta 0)
    (SS.pauliAct P (MainTheory.CitedAncillaFamily.code theta 0)),?_⟩
  intro i j
  simp only [expansion,pauliAct_add,pauliAct_smul,innerC_add_left,innerC_add_right,
    innerC_smul_left,innerC_smul_right]
  rw [blocks P hw i j false false, blocks P hw i j false true,
    blocks P hw i j true false, blocks P hw i j true true]
  by_cases h : i=j <;> simp [h]

theorem hasDistance (theta : ℝ) : SS.HasDistance (MainTheory.CitedAncillaFamily.code theta) 3 := by
  intro P hw
  exact condition theta P hw

end MainTheory.CitedFamilyFullKL
