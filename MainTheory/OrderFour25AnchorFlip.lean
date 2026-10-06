import MainTheory.OrderFour25Walsh
import MainTheory.FlipLinearCombination

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace MainTheory.OrderFour25AnchorFlip
open MainTheory.OrderFour25Support MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open MainTheory.OrderFour25Walsh (ys injective)
open SixQubit.Orbit25 (S0 S1)
def mask (j : Fin 5) := SS.bxor (bits 32) (unit j)
def targets (j : Fin 5) : Fin 4 → SS.BitString 6 :=
  ![anchor true,anchor false,hat true j,hat false j]
def zs : Fin 2 → SS.BitString 6 := ![bits 0,bits 32]
theorem incidences : ∀ j,Finset.univ.image (ys j)=incidenceSet S0 S1 (mask j) := by decide +kernel
theorem flips : ∀ j i,SS.bxor (ys j i) (mask j)=targets j i := by decide +kernel
theorem weights : ∀ j i,(⟨mask j,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem signs : ∀ j i k,SS.bdot (zs i) (ys j k)=
    (!![false,false,false,false;false,true,false,true] : Matrix (Fin 2) (Fin 4) Bool) i k := by decide +kernel
theorem certificate : ∀ j k,∑ i : Fin 2,(1/2 : ℂ)*character (zs i) (ys j k)=
    (![1,0,1,0] : Fin 4 → ℂ) k := by
  intro j k
  simp only [character,signs,Fin.sum_univ_two]
  fin_cases k <;> norm_num

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 5) :
    star (c (anchor true))*d (tail false j)+star (c (hat true j))*d (full false)=0 := by
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl
    (mask j) (ys j) zs (injective j) (incidences j) (weights j)
    (fun _ => 1/2) ![1,0,1,0] (certificate j)
  simp only [incidenceMonomial,flips] at h
  simpa [targets,MainTheory.OrderFour25Walsh.ys,Fin.sum_univ_succ] using h

end MainTheory.OrderFour25AnchorFlip
