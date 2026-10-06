import MainTheory.OrderSixSupportDisplays
import MainTheory.FlipLinearCombination

set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace MainTheory.OrderSixPhaseRows
open MainTheory.OrderSixSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)

def characterQ (z y : SS.BitString 6) : ℚ := if SS.bdot z y then -1 else 1
theorem character_cast (z y : SS.BitString 6) : (characterQ z y : ℂ)=character z y := by
  unfold characterQ character
  split_ifs <;> norm_num


namespace Orbit53_pair46a
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 0,top53 2,top53 1,top53 3]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 2,bottom53 0,bottom53 3,bottom53 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 4,bits 5]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (-1/2 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 5) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 5)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 5,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom53 2))*d (top53 0)+star (c (bottom53 0))*d (top53 2)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 5)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit53_pair46a


namespace Orbit53_pair46b
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 1,top53 3,top53 0,top53 2]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 3,bottom53 1,bottom53 2,bottom53 0]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 4,bits 5]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (1/2 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 5) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 5)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 5,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom53 3))*d (top53 1)+star (c (bottom53 1))*d (top53 3)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 5)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit53_pair46b


namespace Orbit53_pair56a
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 0,top53 1,top53 2,top53 3]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 1,bottom53 0,bottom53 3,bottom53 2]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 2,bits 3]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (-1/2 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 3) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 3)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 3,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom53 1))*d (top53 0)+star (c (bottom53 0))*d (top53 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 3)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit53_pair56a


namespace Orbit53_pair56b
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 2,top53 3,top53 0,top53 1]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 3,bottom53 2,bottom53 1,bottom53 0]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 2,bits 3]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (1/2 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 3) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 3)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 3,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom53 3))*d (top53 2)+star (c (bottom53 2))*d (top53 3)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 3)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit53_pair56b


namespace Orbit53_four16
open SixQubit.Orbit53 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top53 4,top53 5,top53 7,top53 8]
def targets : Fin 4 → SS.BitString 6 := ![bottom53 8,bottom53 7,bottom53 5,bottom53 4]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 32,bits 33]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 33) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 33)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 33,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom53 8))*d (top53 4)+star (c (bottom53 7))*d (top53 5)+star (c (bottom53 5))*d (top53 7)+star (c (bottom53 4))*d (top53 8)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 33)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit53_four16


namespace Orbit55_edge64
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 4,top55 6]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 6,bottom55 4]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 8,bits 32,bits 40]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 40) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 40)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 40,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 6))*d (top55 4)+star (c (bottom55 4))*d (top55 6)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 40)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge64


namespace Orbit55_edge62
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 2,top55 6]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 6,bottom55 2]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 4,bits 32,bits 36]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 36) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 36)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 36,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 6))*d (top55 2)+star (c (bottom55 2))*d (top55 6)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 36)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge62


namespace Orbit55_edge96
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 6,top55 9]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 9,bottom55 6]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 32,bits 33]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 33) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 33)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 33,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 9))*d (top55 6)+star (c (bottom55 6))*d (top55 9)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 33)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge96


namespace Orbit55_edge65
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 5,top55 6]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 6,bottom55 5]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 8,bits 16,bits 24]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 24) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 24)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 24,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 6))*d (top55 5)+star (c (bottom55 5))*d (top55 6)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 24)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge65


namespace Orbit55_edge63
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 3,top55 6]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 6,bottom55 3]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 4,bits 16,bits 20]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 20) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 20)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 20,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 6))*d (top55 3)+star (c (bottom55 3))*d (top55 6)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 20)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge63


namespace Orbit55_edge106
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 2 → SS.BitString 6 := ![top55 6,top55 10]
def targets : Fin 2 → SS.BitString 6 := ![bottom55 10,bottom55 6]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 16,bits 17]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 2) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 17) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 17)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 17,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 10))*d (top55 6)+star (c (bottom55 6))*d (top55 10)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 17)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_edge106


namespace Orbit55_binomial1
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 6 → SS.BitString 6 := ![top55 2,top55 3,top55 9,top55 10,top55 1,top55 7]
def targets : Fin 6 → SS.BitString 6 := ![bottom55 10,bottom55 9,bottom55 3,bottom55 2,bottom55 7,bottom55 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 8,bits 10]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 6) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 10) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 10)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 10,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 10))*d (top55 2)+star (c (bottom55 9))*d (top55 3)+star (c (bottom55 3))*d (top55 9)+star (c (bottom55 2))*d (top55 10)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 10)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_binomial1


namespace Orbit55_binomial2
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 6 → SS.BitString 6 := ![top55 4,top55 5,top55 9,top55 10,top55 1,top55 8]
def targets : Fin 6 → SS.BitString 6 := ![bottom55 10,bottom55 9,bottom55 5,bottom55 4,bottom55 8,bottom55 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 4,bits 6]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 6) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 6)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 6,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 10))*d (top55 4)+star (c (bottom55 9))*d (top55 5)+star (c (bottom55 5))*d (top55 9)+star (c (bottom55 4))*d (top55 10)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 6)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_binomial2


namespace Orbit55_binomial3
open SixQubit.Orbit55 (S0 S1)
def ys : Fin 6 → SS.BitString 6 := ![top55 2,top55 3,top55 4,top55 5,top55 0,top55 1]
def targets : Fin 6 → SS.BitString 6 := ![bottom55 5,bottom55 4,bottom55 3,bottom55 2,bottom55 1,bottom55 0]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 2,bits 3]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (1/2 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 6) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 3) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 3)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 3,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom55 5))*d (top55 2)+star (c (bottom55 4))*d (top55 3)+star (c (bottom55 3))*d (top55 4)+star (c (bottom55 2))*d (top55 5)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 3)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit55_binomial3


namespace Orbit56_edge1_5
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 5,top56 1,top56 2,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 5,bottom56 9,bottom56 2]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 16,bits 18]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 18) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 18)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 18,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 5)+star (c (bottom56 5))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 18)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_5


namespace Orbit56_edge2_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 2,top56 1,top56 5]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 2,bottom56 9,bottom56 5,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 16,bits 18]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 18) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 18)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 18,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 2))*d (top56 9)+star (c (bottom56 9))*d (top56 2)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 18)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge2_9


namespace Orbit56_edge1_2
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 2,top56 1,top56 5,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 2,bottom56 9,bottom56 5]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 16,bits 17]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 17) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 17)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 17,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 2)+star (c (bottom56 2))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 17)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_2


namespace Orbit56_edge5_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 5,top56 1,top56 2]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 5,bottom56 9,bottom56 2,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 16,bits 17]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 17) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 17)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 17,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 5))*d (top56 9)+star (c (bottom56 9))*d (top56 5)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 17)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge5_9


namespace Orbit56_edge1_6
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 6,top56 1,top56 3,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 6,bottom56 9,bottom56 3]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 8,bits 10]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 10) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 10)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 10,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 6)+star (c (bottom56 6))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 10)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_6


namespace Orbit56_edge3_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 3,top56 1,top56 6]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 3,bottom56 9,bottom56 6,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 8,bits 10]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 10) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 10)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 10,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 3))*d (top56 9)+star (c (bottom56 9))*d (top56 3)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 10)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge3_9


namespace Orbit56_edge1_3
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 3,top56 1,top56 6,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 3,bottom56 9,bottom56 6]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 9]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 9) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 9)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 9,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 3)+star (c (bottom56 3))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 9)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_3


namespace Orbit56_edge6_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 6,top56 1,top56 3]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 6,bottom56 9,bottom56 3,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 9]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 9) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 9)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 9,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 6))*d (top56 9)+star (c (bottom56 9))*d (top56 6)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 9)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge6_9


namespace Orbit56_edge1_7
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 7,top56 1,top56 4,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 7,bottom56 9,bottom56 4]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 4,bits 6]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 6)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 6,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 7)+star (c (bottom56 7))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 6)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_7


namespace Orbit56_edge4_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 4,top56 1,top56 7]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 4,bottom56 9,bottom56 7,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 2,bits 4,bits 6]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 6) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 6)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 6,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 4))*d (top56 9)+star (c (bottom56 9))*d (top56 4)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 6)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge4_9


namespace Orbit56_edge1_4
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 4,top56 1,top56 7,top56 9]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 1,bottom56 4,bottom56 9,bottom56 7]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 4,bits 5]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (-1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 5) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 5)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 5,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 1))*d (top56 4)+star (c (bottom56 4))*d (top56 1)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 5)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge1_4


namespace Orbit56_edge7_9
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 9,top56 7,top56 1,top56 4]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 7,bottom56 9,bottom56 4,bottom56 1]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 1,bits 4,bits 5]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1/2 : ℚ) else if i.val=1 then (1/2 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<2 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 5) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 5)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 5,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 7))*d (top56 9)+star (c (bottom56 9))*d (top56 7)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 5)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_edge7_9


namespace Orbit56_binomial1
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 7,top56 6,top56 4,top56 3]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 3,bottom56 4,bottom56 6,bottom56 7]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 16,bits 32,bits 48]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 48) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 48)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 48,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 3))*d (top56 7)+star (c (bottom56 4))*d (top56 6)+star (c (bottom56 6))*d (top56 4)+star (c (bottom56 7))*d (top56 3)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 48)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_binomial1


namespace Orbit56_binomial2
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 7,top56 5,top56 4,top56 2]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 2,bottom56 4,bottom56 5,bottom56 7]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 8,bits 32,bits 40]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 40) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 40)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 40,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 2))*d (top56 7)+star (c (bottom56 4))*d (top56 5)+star (c (bottom56 5))*d (top56 4)+star (c (bottom56 7))*d (top56 2)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 40)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_binomial2


namespace Orbit56_binomial3
open SixQubit.Orbit56 (S0 S1)
def ys : Fin 4 → SS.BitString 6 := ![top56 6,top56 5,top56 3,top56 2]
def targets : Fin 4 → SS.BitString 6 := ![bottom56 2,bottom56 3,bottom56 5,bottom56 6]
def zs : Fin 4 → SS.BitString 6 := ![bits 0,bits 4,bits 32,bits 36]
def coeffQ (i : Fin 4) : ℚ := if i.val=0 then (1 : ℚ) else if i.val=1 then (0 : ℚ) else if i.val=2 then (0 : ℚ) else (0 : ℚ)
def targetQ (j : Fin 4) : ℚ := if j.val<4 then 1 else 0
theorem injective : Function.Injective ys := by decide +kernel
theorem incidences : Finset.univ.image ys=incidenceSet S0 S1 (bits 36) := by decide +kernel
theorem flips : ∀ j,SS.bxor (ys j) (bits 36)=targets j := by decide +kernel
theorem weights : ∀ i,(⟨bits 36,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : ∀ j,∑ i,coeffQ i*characterQ (zs i) (ys j)=targetQ j := by decide +kernel

theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom56 2))*d (top56 6)+star (c (bottom56 3))*d (top56 5)+star (c (bottom56 5))*d (top56 3)+star (c (bottom56 6))*d (top56 2)=0 := by
  have hcert : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (ys j)=(targetQ j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.FlipLinearCombination.equation S0 S1 c d hc hd hkl (bits 36)
    ys zs injective incidences weights (fun i => (coeffQ i : ℂ)) (fun j => (targetQ j : ℂ)) hcert
  simp only [incidenceMonomial,flips] at h
  norm_num [targetQ,targets,ys,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply] at h
  linear_combination h
end Orbit56_binomial3


end MainTheory.OrderSixPhaseRows
