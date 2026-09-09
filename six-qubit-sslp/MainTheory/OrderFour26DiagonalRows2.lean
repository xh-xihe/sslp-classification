import MainTheory.OrderFour26Support
import MainTheory.DiagonalLinearCombination
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderFour26DiagonalRows2
open MainTheory.OrderFour26Support MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit26 (S0 S1)
def characterQ (z y : SS.BitString 6) : ℚ := if SS.bdot z y then -1 else 1
theorem character_cast (z y : SS.BitString 6) : (characterQ z y : ℂ)=character z y := by
  unfold characterQ character
  split_ifs <;> norm_num

namespace Entry00
def zs : Fin 8 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 16,bits 32,bits 33,bits 40,bits 48]
def coeffQ : Fin 8 → ℚ := ![-1/8,-1/8,-1/8,1/8,-1/8,-1/8,-1/8,1/8]
def tx : Fin 16 → ℚ := ![-1/2,-1/2,-1/2,-1/2,1/2,1/2,-1/2,-1/2,0,0,0,0,0,0,0,0]
def ty : Fin 16 → ℚ := ![0,0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0]
def fx : Fin 16 → SS.BitString 6 := ![bottom 0,bottom 1,bottom 2,bottom 3,bottom 4,bottom 5,bottom 6,bottom 7,bottom 8,bottom 9,bottom 10,bottom 11,bottom 12,bottom 13,bottom 14,bottom 15]
def fy : Fin 16 → SS.BitString 6 := ![top 0,top 1,top 2,top 3,top 4,top 5,top 6,top 7,top 8,top 9,top 10,top 11,top 12,top 13,top 14,top 15]
theorem incidences : Finset.univ.image bottom=incidenceSet S0 S0 (bits 0) ∧
    Finset.univ.image top=incidenceSet S1 S1 (bits 0) := by decide +kernel
theorem flips : (∀ i,SS.bxor (bottom i) (bits 0)=fx i) ∧
    (∀ i,SS.bxor (top i) (bits 0)=fy i) := by decide +kernel
theorem weights : ∀ i,(⟨bits 0,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : (∀ j,∑ i,coeffQ i*characterQ (zs i) (bottom j)=tx j) ∧
    (∀ j,∑ i,coeffQ i*characterQ (zs i) (top j)=ty j) := by decide +kernel
theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom 4))*c (bottom 4)+star (c (bottom 5))*c (bottom 5)+star (d (top 4))*d (top 4)+star (d (top 5))*d (top 5)=(1/2)*(star (c (bottom 0))*c (bottom 0)+star (c (bottom 1))*c (bottom 1)+star (c (bottom 2))*c (bottom 2)+star (c (bottom 3))*c (bottom 3)+star (c (bottom 4))*c (bottom 4)+star (c (bottom 5))*c (bottom 5)+star (c (bottom 6))*c (bottom 6)+star (c (bottom 7))*c (bottom 7)) := by
  have cx : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (bottom j)=(tx j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.1 j)
    push_cast at h
    simpa only [character_cast] using h
  have cy : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (top j)=(ty j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.2 j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.DiagonalLinearCombination.equation S0 S1 c d hc hd hkl (bits 0)
    bottom top zs bottom_injective top_injective incidences.1 incidences.2 weights
    (fun i => (coeffQ i : ℂ)) (fun j => (tx j : ℂ)) (fun j => (ty j : ℂ)) cx cy
  simp only [incidenceMonomial,flips.1,flips.2] at h
  norm_num [tx,ty,fx,fy,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply, Fin.reduceFinMk] at h ⊢
  linear_combination h
end Entry00

namespace Entry01
def zs : Fin 8 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 16,bits 32,bits 33,bits 40,bits 48]
def coeffQ : Fin 8 → ℚ := ![-1/8,-1/8,-1/8,1/8,-1/8,-1/8,-1/8,1/8]
def tx : Fin 16 → ℚ := ![-1/2,-1/2,-1/2,-1/2,1/2,1/2,-1/2,-1/2,0,0,0,0,0,0,0,0]
def ty : Fin 16 → ℚ := ![0,0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0]
def fx : Fin 16 → SS.BitString 6 := ![bottom 8,bottom 9,bottom 10,bottom 11,bottom 12,bottom 13,bottom 14,bottom 15,bottom 0,bottom 1,bottom 2,bottom 3,bottom 4,bottom 5,bottom 6,bottom 7]
def fy : Fin 16 → SS.BitString 6 := ![top 8,top 9,top 10,top 11,top 12,top 13,top 14,top 15,top 0,top 1,top 2,top 3,top 4,top 5,top 6,top 7]
theorem incidences : Finset.univ.image bottom=incidenceSet S0 S0 (bits 32) ∧
    Finset.univ.image top=incidenceSet S1 S1 (bits 32) := by decide +kernel
theorem flips : (∀ i,SS.bxor (bottom i) (bits 32)=fx i) ∧
    (∀ i,SS.bxor (top i) (bits 32)=fy i) := by decide +kernel
theorem weights : ∀ i,(⟨bits 32,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : (∀ j,∑ i,coeffQ i*characterQ (zs i) (bottom j)=tx j) ∧
    (∀ j,∑ i,coeffQ i*characterQ (zs i) (top j)=ty j) := by decide +kernel
theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom 12))*c (bottom 4)+star (c (bottom 13))*c (bottom 5)+star (d (top 12))*d (top 4)+star (d (top 13))*d (top 5)=(1/2)*(star (c (bottom 8))*c (bottom 0)+star (c (bottom 9))*c (bottom 1)+star (c (bottom 10))*c (bottom 2)+star (c (bottom 11))*c (bottom 3)+star (c (bottom 12))*c (bottom 4)+star (c (bottom 13))*c (bottom 5)+star (c (bottom 14))*c (bottom 6)+star (c (bottom 15))*c (bottom 7)) := by
  have cx : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (bottom j)=(tx j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.1 j)
    push_cast at h
    simpa only [character_cast] using h
  have cy : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (top j)=(ty j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.2 j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.DiagonalLinearCombination.equation S0 S1 c d hc hd hkl (bits 32)
    bottom top zs bottom_injective top_injective incidences.1 incidences.2 weights
    (fun i => (coeffQ i : ℂ)) (fun j => (tx j : ℂ)) (fun j => (ty j : ℂ)) cx cy
  simp only [incidenceMonomial,flips.1,flips.2] at h
  norm_num [tx,ty,fx,fy,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply, Fin.reduceFinMk] at h ⊢
  linear_combination h
end Entry01

namespace Entry10
def zs : Fin 8 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 16,bits 32,bits 33,bits 40,bits 48]
def coeffQ : Fin 8 → ℚ := ![-1/8,-1/8,-1/8,1/8,1/8,1/8,1/8,-1/8]
def tx : Fin 16 → ℚ := ![0,0,0,0,0,0,0,0,-1/2,-1/2,-1/2,-1/2,1/2,1/2,-1/2,-1/2]
def ty : Fin 16 → ℚ := ![0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0]
def fx : Fin 16 → SS.BitString 6 := ![bottom 8,bottom 9,bottom 10,bottom 11,bottom 12,bottom 13,bottom 14,bottom 15,bottom 0,bottom 1,bottom 2,bottom 3,bottom 4,bottom 5,bottom 6,bottom 7]
def fy : Fin 16 → SS.BitString 6 := ![top 8,top 9,top 10,top 11,top 12,top 13,top 14,top 15,top 0,top 1,top 2,top 3,top 4,top 5,top 6,top 7]
theorem incidences : Finset.univ.image bottom=incidenceSet S0 S0 (bits 32) ∧
    Finset.univ.image top=incidenceSet S1 S1 (bits 32) := by decide +kernel
theorem flips : (∀ i,SS.bxor (bottom i) (bits 32)=fx i) ∧
    (∀ i,SS.bxor (top i) (bits 32)=fy i) := by decide +kernel
theorem weights : ∀ i,(⟨bits 32,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : (∀ j,∑ i,coeffQ i*characterQ (zs i) (bottom j)=tx j) ∧
    (∀ j,∑ i,coeffQ i*characterQ (zs i) (top j)=ty j) := by decide +kernel
theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom 4))*c (bottom 12)+star (c (bottom 5))*c (bottom 13)+star (d (top 4))*d (top 12)+star (d (top 5))*d (top 13)=(1/2)*(star (c (bottom 0))*c (bottom 8)+star (c (bottom 1))*c (bottom 9)+star (c (bottom 2))*c (bottom 10)+star (c (bottom 3))*c (bottom 11)+star (c (bottom 4))*c (bottom 12)+star (c (bottom 5))*c (bottom 13)+star (c (bottom 6))*c (bottom 14)+star (c (bottom 7))*c (bottom 15)) := by
  have cx : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (bottom j)=(tx j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.1 j)
    push_cast at h
    simpa only [character_cast] using h
  have cy : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (top j)=(ty j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.2 j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.DiagonalLinearCombination.equation S0 S1 c d hc hd hkl (bits 32)
    bottom top zs bottom_injective top_injective incidences.1 incidences.2 weights
    (fun i => (coeffQ i : ℂ)) (fun j => (tx j : ℂ)) (fun j => (ty j : ℂ)) cx cy
  simp only [incidenceMonomial,flips.1,flips.2] at h
  norm_num [tx,ty,fx,fy,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply, Fin.reduceFinMk] at h ⊢
  linear_combination h
end Entry10

namespace Entry11
def zs : Fin 8 → SS.BitString 6 := ![bits 0,bits 1,bits 8,bits 16,bits 32,bits 33,bits 40,bits 48]
def coeffQ : Fin 8 → ℚ := ![-1/8,-1/8,-1/8,1/8,1/8,1/8,1/8,-1/8]
def tx : Fin 16 → ℚ := ![0,0,0,0,0,0,0,0,-1/2,-1/2,-1/2,-1/2,1/2,1/2,-1/2,-1/2]
def ty : Fin 16 → ℚ := ![0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0]
def fx : Fin 16 → SS.BitString 6 := ![bottom 0,bottom 1,bottom 2,bottom 3,bottom 4,bottom 5,bottom 6,bottom 7,bottom 8,bottom 9,bottom 10,bottom 11,bottom 12,bottom 13,bottom 14,bottom 15]
def fy : Fin 16 → SS.BitString 6 := ![top 0,top 1,top 2,top 3,top 4,top 5,top 6,top 7,top 8,top 9,top 10,top 11,top 12,top 13,top 14,top 15]
theorem incidences : Finset.univ.image bottom=incidenceSet S0 S0 (bits 0) ∧
    Finset.univ.image top=incidenceSet S1 S1 (bits 0) := by decide +kernel
theorem flips : (∀ i,SS.bxor (bottom i) (bits 0)=fx i) ∧
    (∀ i,SS.bxor (top i) (bits 0)=fy i) := by decide +kernel
theorem weights : ∀ i,(⟨bits 0,zs i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem certificate : (∀ j,∑ i,coeffQ i*characterQ (zs i) (bottom j)=tx j) ∧
    (∀ j,∑ i,coeffQ i*characterQ (zs i) (top j)=ty j) := by decide +kernel
theorem equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : star (c (bottom 12))*c (bottom 12)+star (c (bottom 13))*c (bottom 13)+star (d (top 12))*d (top 12)+star (d (top 13))*d (top 13)=(1/2)*(star (c (bottom 8))*c (bottom 8)+star (c (bottom 9))*c (bottom 9)+star (c (bottom 10))*c (bottom 10)+star (c (bottom 11))*c (bottom 11)+star (c (bottom 12))*c (bottom 12)+star (c (bottom 13))*c (bottom 13)+star (c (bottom 14))*c (bottom 14)+star (c (bottom 15))*c (bottom 15)) := by
  have cx : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (bottom j)=(tx j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.1 j)
    push_cast at h
    simpa only [character_cast] using h
  have cy : ∀ j,∑ i,(coeffQ i : ℂ)*character (zs i) (top j)=(ty j : ℂ) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℂ)) (certificate.2 j)
    push_cast at h
    simpa only [character_cast] using h
  have h := MainTheory.DiagonalLinearCombination.equation S0 S1 c d hc hd hkl (bits 0)
    bottom top zs bottom_injective top_injective incidences.1 incidences.2 weights
    (fun i => (coeffQ i : ℂ)) (fun j => (tx j : ℂ)) (fun j => (ty j : ℂ)) cx cy
  simp only [incidenceMonomial,flips.1,flips.2] at h
  norm_num [tx,ty,fx,fy,Fin.sum_univ_succ,Fin.succ] at h
  simp only [starRingEnd_apply, Fin.reduceFinMk] at h ⊢
  linear_combination h
end Entry11

end MainTheory.OrderFour26DiagonalRows2
