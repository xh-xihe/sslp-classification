import SixQubit.Orbit7UniversalShell
import SixQubit.CodeEquivEnum
import SixQubit.Orbit7Real

/-!
# Orbit 7: exact original-to-uniform gauge transport

The manuscript proves the converse in the uniform presentation
`(0,1,1,1,1,1)`, with logical residues zero and two.  The repository's
manifest representative is `(0,1,1,1,2,2)`, with residues zero and one.

Flipping the last two physical bits adds two to the residue; interchanging
the two logical words therefore sends the original representative exactly to
the uniform presentation.  This file proves support, normalization,
distance-three, and both weight-enumerator invariances for that fixed gauge.
-/

namespace SixQubit.Orbit7Gauge

open SixQubit
open SixQubit.CodeEquiv
open SixQubit.Realize

noncomputable section

def flip45 : SS.BitString 6 := bs false false false false true true

def bottom (d : SS.State 6 ℂ) : SS.State 6 ℂ := flipAct flip45 d
def top (c : SS.State 6 ℂ) : SS.State 6 ℂ := flipAct flip45 c
def uniformCode (c d : SS.State 6 ℂ) : Fin 2 -> SS.State 6 ℂ :=
  ![bottom d, top c]

theorem uniform0_iff_original1 : ∀ x : SS.BitString 6,
    SS.weight SixQubit.Orbit7Universal.uniformAv x = 0 ↔
      SS.weight SixQubit.Orbit7Real.av (SS.bxor x flip45) = 1 := by
  decide

theorem uniform2_iff_original0 : ∀ x : SS.BitString 6,
    SS.weight SixQubit.Orbit7Universal.uniformAv x = 2 ↔
      SS.weight SixQubit.Orbit7Real.av (SS.bxor x flip45) = 0 := by
  decide

theorem bottom_full_fiber (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 -> d x = 0) :
    ∀ x, SS.weight SixQubit.Orbit7Universal.uniformAv x ≠ 0 ->
      bottom d x = 0 := by
  intro x hx
  unfold bottom flipAct
  apply hd
  intro horig
  exact hx ((uniform0_iff_original1 x).mpr horig)

theorem top_full_fiber (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 -> c x = 0) :
    ∀ x, SS.weight SixQubit.Orbit7Universal.uniformAv x ≠ 2 ->
      top c x = 0 := by
  intro x hx
  unfold top flipAct
  apply hc
  intro horig
  exact hx ((uniform2_iff_original0 x).mpr horig)

lemma innerC_flipAct (f : SS.BitString 6) (u : SS.State 6 ℂ) :
    SS.innerC (flipAct f u) (flipAct f u) = SS.innerC u u := by
  unfold SS.innerC flipAct
  exact Equiv.sum_comp (SS.bxorEquiv f) (fun x => star (u x) * u x)

theorem bottom_normalized (d : SS.State 6 ℂ) (hnd : SS.innerC d d = 1) :
    SS.innerC (bottom d) (bottom d) = 1 := by
  rw [bottom, innerC_flipAct, hnd]

theorem top_normalized (c : SS.State 6 ℂ) (hnc : SS.innerC c c = 1) :
    SS.innerC (top c) (top c) = 1 := by
  rw [top, innerC_flipAct, hnc]

theorem hasDistance (c d : SS.State 6 ℂ)
    (hcode : SS.HasDistance ![c,d] 3) :
    SS.HasDistance (uniformCode c d) 3 := by
  have hraw : DetectsRaw ![c,d] 2 := (hasDistance_iff ![c,d]).mp hcode
  have hswap := detectsRaw_swap true hraw
  have hflip := detectsRaw_flipAct flip45 hswap
  apply (hasDistance_iff (uniformCode c d)).mpr
  simpa [uniformCode, bottom, top, swapIdx] using hflip

theorem Aco_invariant (c d : SS.State 6 ℂ) (j : Nat) :
    SS.MacWilliams.Aco (uniformCode c d) j = SS.MacWilliams.Aco ![c,d] j := by
  have h := Aco_fixed_perm_flip_swap (Equiv.refl (Fin 6)) flip45 ![c,d] true j
  simpa [uniformCode, bottom, top, permAct, permStr, swapIdx] using h

theorem Bco_invariant (c d : SS.State 6 ℂ) (j : Nat) :
    SS.MacWilliams.Bco (uniformCode c d) j = SS.MacWilliams.Bco ![c,d] j := by
  have h := Bco_fixed_perm_flip_swap (Equiv.refl (Fin 6)) flip45 ![c,d] true j
  simpa [uniformCode, bottom, top, permAct, permStr, swapIdx] using h

end

end SixQubit.Orbit7Gauge
