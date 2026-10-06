import MainTheory.OrderFour25Support
import MainTheory.WalshFourIncidence

set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFour25Walsh
open MainTheory.OrderFour25Support MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open MainTheory.OrderSevenWalshMatrix
open SixQubit.Orbit25 (S0 S1)

def ys (j : Fin 5) : Fin 4 → SS.BitString 6 :=
  ![tail false j,tail true j,full false,full true]
def targets (j : Fin 5) : Fin 4 → SS.BitString 6 :=
  ![anchor false,anchor true,hat false j,hat true j]
def zs (j : Fin 5) : Fin 3 → SS.BitString 6 :=
  ![bits 0,bits 32,if j=0 then bits 8 else bits 16]
theorem injective : ∀ j,Function.Injective (ys j) := by decide +kernel
theorem incidences : ∀ j,Finset.univ.image (ys j)=incidenceSet S0 S1 (unit j) := by decide +kernel
theorem flips : ∀ j i,SS.bxor (ys j i) (unit j)=targets j i := by decide +kernel
theorem dot_signs : ∀ j i k,SS.bdot (zs j i) (ys j k)=
    (!![false,false,false,false;false,true,false,true;false,false,true,true] : Matrix (Fin 3) (Fin 4) Bool) i k := by decide +kernel
theorem character_rows : ∀ j i k,character (zs j i) (ys j k)=1*W i k := by
  intro j i k
  simp only [character,dot_signs]
  fin_cases i <;> fin_cases k <;> norm_num [W] <;> decide
theorem weights : ∀ j i,(⟨unit j,zs j i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
noncomputable def products (c d : SS.State 6 ℂ) (j : Fin 5) : Fin 4 → ℂ :=
  fun i => star (c (targets j i))*d (ys j i)

theorem matrix_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 5) : W.mulVec (products c d j)=0 := by
  have h := MainTheory.WalshFourIncidence.matrix_equation S0 S1 c d hc hd hkl
    (unit j) (ys j) (zs j) (injective j) (incidences j) (weights j)
    (fun _ => 1) (by intro i; norm_num) (character_rows j)
  simpa only [incidenceMonomial,flips] using h

theorem kernel_relations (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 5) :
    ∃ l : ℂ,star (c (anchor false))*d (tail false j)=l ∧
      star (c (anchor true))*d (tail true j)= -l ∧
      star (c (hat false j))*d (full false)= -l ∧
      star (c (hat true j))*d (full true)=l := by
  have h := relations _ (matrix_equation c d hc hd hkl j)
  change star (c (anchor false))*d (tail false j)=star (c (hat true j))*d (full true) ∧
    star (c (anchor true))*d (tail true j)=star (c (hat false j))*d (full false) ∧
    star (c (anchor true))*d (tail true j)= -(star (c (anchor false))*d (tail false j)) at h
  exact ⟨_,rfl,h.2.2,h.2.1.symm.trans h.2.2,h.1.symm⟩

end MainTheory.OrderFour25Walsh
