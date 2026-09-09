import MainTheory.OrderSevenSupportDisplays
import MainTheory.FlipCharacterObstruction
import MainTheory.OrderSevenWalshMatrix

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSeven58Walsh

open MainTheory.OrderSevenSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open MainTheory.OrderSevenWalshMatrix
open SixQubit.Orbit58 (S0 S1)

def sources1 : Fin 4 → SS.BitString 6 := ![top58 8,top58 6,top58 4,top58 0]
def sources2 : Fin 4 → SS.BitString 6 := ![top58 7,top58 6,top58 3,top58 0]
def targets1 : Fin 4 → SS.BitString 6 := ![bottom58 0,bottom58 4,bottom58 6,bottom58 8]
def targets2 : Fin 4 → SS.BitString 6 := ![bottom58 0,bottom58 3,bottom58 6,bottom58 7]
def dressings1 : Fin 3 → SS.BitString 6 := ![bits 0,bits 16,bits 8]
def dressings2 : Fin 3 → SS.BitString 6 := ![bits 0,bits 32,bits 8]

theorem injective1 : Function.Injective sources1 := by decide +kernel
theorem injective2 : Function.Injective sources2 := by decide +kernel
theorem incidences1 : Finset.univ.image sources1=incidenceSet S0 S1 (bits 32) := by decide +kernel
theorem incidences2 : Finset.univ.image sources2=incidenceSet S0 S1 (bits 16) := by decide +kernel
theorem flips1 : ∀ j,SS.bxor (sources1 j) (bits 32)=targets1 j := by decide +kernel
theorem flips2 : ∀ j,SS.bxor (sources2 j) (bits 16)=targets2 j := by decide +kernel
theorem signs1 : ∀ i j,SS.bdot (dressings1 i) (sources1 j)=
    (!![false,false,false,false;false,true,false,true;false,false,true,true] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem signs2 : ∀ i j,SS.bdot (dressings2 i) (sources2 j)=
    (!![false,false,false,false;false,true,false,true;false,false,true,true] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel

theorem characters1 : ∀ i j,character (dressings1 i) (sources1 j)=W i j := by
  intro i j
  simp only [character,signs1]
  fin_cases i <;> fin_cases j <;> norm_num [W] <;> decide

theorem characters2 : ∀ i j,character (dressings2 i) (sources2 j)=W i j := by
  intro i j
  simp only [character,signs2]
  fin_cases i <;> fin_cases j <;> norm_num [W] <;> decide

noncomputable def products1 (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets1 j))*d (sources1 j)
noncomputable def products2 (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets2 j))*d (sources2 j)

theorem matrix1 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products1 c d)=0 := by
  ext i
  have hw : ∀ i,(⟨bits 32,dressings1 i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
    (bits 32) (dressings1 i) (hw i)
  rw [offSum_eq_indexed S0 S1 c d (bits 32) (dressings1 i) sources1 injective1 incidences1] at h
  simpa only [characters1,incidenceMonomial,flips1] using h

theorem matrix2 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products2 c d)=0 := by
  ext i
  have hw : ∀ i,(⟨bits 16,dressings2 i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
    (bits 16) (dressings2 i) (hw i)
  rw [offSum_eq_indexed S0 S1 c d (bits 16) (dressings2 i) sources2 injective2 incidences2] at h
  simpa only [characters2,incidenceMonomial,flips2] using h

end MainTheory.OrderSeven58Walsh
