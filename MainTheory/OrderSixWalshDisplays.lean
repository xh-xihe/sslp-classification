import MainTheory.OrderSixSupportDisplays
import MainTheory.WalshFourIncidence

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace MainTheory.OrderSixWalshDisplays
open MainTheory.OrderSixSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open MainTheory.OrderSevenWalshMatrix


namespace Orbit53X1
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 0,top53 3,top53 6,top53 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 9,bottom53 6,bottom53 3,bottom53 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 4,bits 16]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 32) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 32)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 32,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 32) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit53X1


namespace Orbit53X2
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 0,top53 3,top53 5,top53 8]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 8,bottom53 5,bottom53 3,bottom53 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 4,bits 32]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 16) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 16)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 16,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 16) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit53X2


namespace Orbit53X3
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 0,top53 3,top53 4,top53 7]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 7,bottom53 4,bottom53 3,bottom53 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 4,bits 32]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 8) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 8)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 8,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 8) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit53X3


namespace Orbit54X1
open SixQubit.Orbit54 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top54 0,top54 4,top54 6,top54 8]
def targets : Fin 4 → SS.BitString 6 := ![bottom54 8,bottom54 6,bottom54 4,bottom54 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 8,bits 16]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 32) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 32)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 32,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 32) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit54X1


namespace Orbit54X2
open SixQubit.Orbit54 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top54 0,top54 4,top54 5,top54 7]
def targets : Fin 4 → SS.BitString 6 := ![bottom54 7,bottom54 5,bottom54 4,bottom54 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 8,bits 32]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 16) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 16)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 16,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 16) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit54X2


namespace Orbit54X6
open SixQubit.Orbit54 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top54 5,top54 6,top54 7,top54 8]
def targets : Fin 4 → SS.BitString 6 := ![bottom54 8,bottom54 7,bottom54 6,bottom54 5]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 32,bits 8]
def signs : Fin 3 → ℂ := ![1,1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 1) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 1)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;false,true,false,true;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 1,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 1) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit54X6


namespace Orbit56X1
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 0,top56 1,top56 8,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 9,bottom56 8,bottom56 1,bottom56 0]
def zs : Fin 3 → SS.BitString 6 := ![bits 0,bits 16,bits 2]
def signs : Fin 3 → ℂ := ![1,-1,-1]
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 32) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 32)=targets j := by decide +kernel
theorem dot_signs : ∀ i j,SS.bdot (zs i) (ys j)=
    (!![false,false,false,false;true,false,true,false;true,true,false,false] : Matrix (Fin 3) (Fin 4) Bool) i j := by decide +kernel
theorem character_rows : ∀ i j,character (zs i) (ys j)=signs i*W i j := by
  intro i j
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases j <;> norm_num [signs,W] <;> decide
theorem weights : ∀ i,(⟨bits 32,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) : Fin 4 → ℂ :=
  fun j => star (c (targets j))*d (ys j)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d)=0 := by
  have hn : ∀ i,signs i ≠ 0 := by intro i; fin_cases i <;> norm_num [signs]
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (bits 32) ys zs injective incidences weights signs hn character_rows
  simpa only [incidenceMonomial,flips] using h
end Orbit56X1


end MainTheory.OrderSixWalshDisplays
