import SixQubit.Orbit8UniversalHafnianBridge

/-! Finite decoding infrastructure for the Orbit 8 complementary hafnians. -/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

set_option maxRecDepth 20000

noncomputable section

def edgeDecode (q : SS.BitString 6) : Fin 6 × Fin 6 :=
  if q 0 then
    if q 1 then (0,1)
    else if q 2 then (0,2)
    else if q 3 then (0,3)
    else if q 4 then (0,4) else (0,5)
  else if q 1 then
    if q 2 then (1,2)
    else if q 3 then (1,3)
    else if q 4 then (1,4) else (1,5)
  else if q 2 then
    if q 3 then (2,3)
    else if q 4 then (2,4) else (2,5)
  else if q 3 then
    if q 4 then (3,4) else (3,5)
  else (4,5)

theorem pairMask_edgeDecode : ∀ q : SS.BitString 6,
    SS.hammingWt q = 2 → pairMask (edgeDecode q).1 (edgeDecode q).2 = q := by
  decide

theorem toggle_true_weight_two : ∀ (q : SS.BitString 6) (m : Fin 6),
    SS.hammingWt q = 3 → q m = true →
      SS.hammingWt (SS.bxor q (SS.stdBasis m)) = 2 := by
  decide

lemma edgeMask_decode (d : SS.BitString 6 → ℂ) (q : SS.BitString 6)
    (hq : SS.hammingWt q = 2) :
    edgeMask d q = v d (edgeDecode q).1 (edgeDecode q).2 := by
  unfold edgeMask v
  rw [pairMask_edgeDecode q hq]

theorem hafVia_decode (d : SS.BitString 6 → ℂ) (i j m : Fin 6) :
    hafVia d i j m =
      ∑ ij ∈ awayPairs i,
        if touches ij j = true ∧ topRecip i ij m = true then
          v d ij.1 ij.2 *
            v d (edgeDecode (SS.bxor (topRecip i ij) (SS.stdBasis m))).1
              (edgeDecode (SS.bxor (topRecip i ij) (SS.stdBasis m))).2
        else 0 := by
  unfold hafVia
  refine Finset.sum_congr rfl (fun ij hmem => ?_)
  by_cases hb : touches ij j = true ∧ topRecip i ij m = true
  · rw [if_pos hb, if_pos hb, edgeMask_decode]
    exact toggle_true_weight_two _ _ (topRecip_weight i ij hmem) hb.2
  · simp [hb]

theorem awayPairs_zero : awayPairs 0 =
    ({(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)} :
      Finset (Fin 6 × Fin 6)) := by decide
theorem awayPairs_one : awayPairs 1 =
    ({(0,2),(0,3),(0,4),(0,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)} :
      Finset (Fin 6 × Fin 6)) := by decide
theorem awayPairs_two : awayPairs 2 =
    ({(0,1),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(3,4),(3,5),(4,5)} :
      Finset (Fin 6 × Fin 6)) := by decide
theorem awayPairs_three : awayPairs 3 =
    ({(0,1),(0,2),(0,4),(0,5),(1,2),(1,4),(1,5),(2,4),(2,5),(4,5)} :
      Finset (Fin 6 × Fin 6)) := by decide
theorem awayPairs_four : awayPairs 4 =
    ({(0,1),(0,2),(0,3),(0,5),(1,2),(1,3),(1,5),(2,3),(2,5),(3,5)} :
      Finset (Fin 6 × Fin 6)) := by decide
theorem awayPairs_five : awayPairs 5 =
    ({(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)} :
      Finset (Fin 6 × Fin 6)) := by decide

def spare (i m : Fin 6) : Fin 6 :=
  if i ≠ 0 ∧ m ≠ 0 then 0
  else if i ≠ 1 ∧ m ≠ 1 then 1
  else 2

theorem spare_ne_left : ∀ i m : Fin 6, i ≠ m → spare i m ≠ i := by decide
theorem spare_ne_right : ∀ i m : Fin 6, i ≠ m → spare i m ≠ m := by decide

def compHaf (d : SS.BitString 6 → ℂ) (i m : Fin 6) : ℂ :=
  hafVia d i (spare i m) m

end

end SixQubit.Orbit8Universal
