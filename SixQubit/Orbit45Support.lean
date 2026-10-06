import Mathlib

import SixQubit.CodeBridge
import SixQubit.Orbit45Gram
import SixQubit.Realize

/-!
# Orbit 45: the two full fibres and their exact moment reduction

This is the finite bridge from the genuine distance-three predicate to the
five four-amplitude blocks used by `Orbit45Gram`.  All support and Walsh
identities are checked by the Lean kernel on six-bit strings.
-/

namespace SixQubit.Orbit45Support

open scoped BigOperators ComplexConjugate
open SixQubit.Realize

noncomputable section

def av : Fin 6 → ZMod 6 := ![1, 1, 2, 3, 4, 4]

-- Bottom amplitudes, ordered by the five `xor 55` blocks.
def x0 : SS.BitString 6 := nbit 0
def x1 : SS.BitString 6 := nbit 55
def x2 : SS.BitString 6 := nbit 36
def x3 : SS.BitString 6 := nbit 19
def x4 : SS.BitString 6 := nbit 20
def x5 : SS.BitString 6 := nbit 35
def x6 : SS.BitString 6 := nbit 58
def x7 : SS.BitString 6 := nbit 13
def x8 : SS.BitString 6 := nbit 14
def x9 : SS.BitString 6 := nbit 57

-- Top amplitudes are the corresponding bottom amplitudes xor `nbit 8`.
def y0 : SS.BitString 6 := nbit 8
def y1 : SS.BitString 6 := nbit 63
def y2 : SS.BitString 6 := nbit 44
def y3 : SS.BitString 6 := nbit 27
def y4 : SS.BitString 6 := nbit 28
def y5 : SS.BitString 6 := nbit 43
def y6 : SS.BitString 6 := nbit 50
def y7 : SS.BitString 6 := nbit 5
def y8 : SS.BitString 6 := nbit 6
def y9 : SS.BitString 6 := nbit 49

def S0 : Finset (SS.BitString 6) := {x0,x1,x2,x3,x4,x5,x6,x7,x8,x9}
def S1 : Finset (SS.BitString 6) := {y0,y1,y2,y3,y4,y5,y6,y7,y8,y9}

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 0) = S0 := by decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight av x = 3) = S1 := by decide

theorem S0_disjoint_S1 : Disjoint S0 S1 := by decide

theorem mass_bottom (c : SS.BitString 6 → ℂ) :
    SixQubit.massOn S0 c =
      Complex.normSq (c x0) + Complex.normSq (c x1) +
      Complex.normSq (c x2) + Complex.normSq (c x3) +
      Complex.normSq (c x4) + Complex.normSq (c x5) +
      Complex.normSq (c x6) + Complex.normSq (c x7) +
      Complex.normSq (c x8) + Complex.normSq (c x9) := by
  unfold SixQubit.massOn
  rw [show S0 = ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} :
        Finset (SS.BitString 6)) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem mass_top (d : SS.BitString 6 → ℂ) :
    SixQubit.massOn S1 d = Complex.normSq (d y0) + (Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y3) + (Complex.normSq (d y4) + (Complex.normSq (d y5) + (Complex.normSq (d y6) + (Complex.normSq (d y7) + (Complex.normSq (d y8) + (Complex.normSq (d y9)))))))))) := by
  unfold SixQubit.massOn
  rw [show S1 = ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} :
        Finset (SS.BitString 6)) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-! The six one-bit and fifteen two-bit occupation expansions.

Every displayed subset is checked independently by decide; the expressions
are not trusted generated data. -/

theorem occ_bottom0 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 0 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x5) + (Complex.normSq (c x7) + (Complex.normSq (c x9))))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 0 = true) =
      ({x1,x3,x5,x7,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top0 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 0 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y5) + (Complex.normSq (d y7) + (Complex.normSq (d y9))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 0 = true) =
      ({y1,y3,y5,y7,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_bottom1 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 1 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x5) + (Complex.normSq (c x6) + (Complex.normSq (c x8))))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 1 = true) =
      ({x1,x3,x5,x6,x8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top1 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 1 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y5) + (Complex.normSq (d y6) + (Complex.normSq (d y8))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 1 = true) =
      ({y1,y3,y5,y6,y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_bottom2 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 2 = Complex.normSq (c x1) + (Complex.normSq (c x2) + (Complex.normSq (c x4) + (Complex.normSq (c x7) + (Complex.normSq (c x8))))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 2 = true) =
      ({x1,x2,x4,x7,x8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top2 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 2 = Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y4) + (Complex.normSq (d y7) + (Complex.normSq (d y8))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 2 = true) =
      ({y1,y2,y4,y7,y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_bottom3 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 3 = Complex.normSq (c x6) + (Complex.normSq (c x7) + (Complex.normSq (c x8) + (Complex.normSq (c x9)))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 3 = true) =
      ({x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top3 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 3 = Complex.normSq (d y0) + (Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y3) + (Complex.normSq (d y4) + (Complex.normSq (d y5)))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 3 = true) =
      ({y0,y1,y2,y3,y4,y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_bottom4 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 4 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x4) + (Complex.normSq (c x6) + (Complex.normSq (c x9))))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 4 = true) =
      ({x1,x3,x4,x6,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top4 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 4 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y4) + (Complex.normSq (d y6) + (Complex.normSq (d y9))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 4 = true) =
      ({y1,y3,y4,y6,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_bottom5 (c : SS.BitString 6 → ℂ) :
    SixQubit.occOn S0 c 5 = Complex.normSq (c x1) + (Complex.normSq (c x2) + (Complex.normSq (c x5) + (Complex.normSq (c x6) + (Complex.normSq (c x9))))) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun s => s 5 = true) =
      ({x1,x2,x5,x6,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ_top5 (d : SS.BitString 6 → ℂ) :
    SixQubit.occOn S1 d 5 = Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y5) + (Complex.normSq (d y6) + (Complex.normSq (d y9))))) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun s => s 5 = true) =
      ({y1,y2,y5,y6,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom01 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 0 1 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x5))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 0 = true ∧ s 1 = true) =
      ({x1,x3,x5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top01 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 0 1 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y5))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 0 = true ∧ s 1 = true) =
      ({y1,y3,y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom02 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 0 2 = Complex.normSq (c x1) + (Complex.normSq (c x7)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 0 = true ∧ s 2 = true) =
      ({x1,x7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top02 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 0 2 = Complex.normSq (d y1) + (Complex.normSq (d y7)) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 0 = true ∧ s 2 = true) =
      ({y1,y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom03 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 0 3 = Complex.normSq (c x7) + (Complex.normSq (c x9)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 0 = true ∧ s 3 = true) =
      ({x7,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top03 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 0 3 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y5))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 0 = true ∧ s 3 = true) =
      ({y1,y3,y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom04 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 0 4 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x9))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 0 = true ∧ s 4 = true) =
      ({x1,x3,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top04 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 0 4 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y9))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 0 = true ∧ s 4 = true) =
      ({y1,y3,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom05 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 0 5 = Complex.normSq (c x1) + (Complex.normSq (c x5) + (Complex.normSq (c x9))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 0 = true ∧ s 5 = true) =
      ({x1,x5,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top05 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 0 5 = Complex.normSq (d y1) + (Complex.normSq (d y5) + (Complex.normSq (d y9))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 0 = true ∧ s 5 = true) =
      ({y1,y5,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom12 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 1 2 = Complex.normSq (c x1) + (Complex.normSq (c x8)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 1 = true ∧ s 2 = true) =
      ({x1,x8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top12 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 1 2 = Complex.normSq (d y1) + (Complex.normSq (d y8)) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 1 = true ∧ s 2 = true) =
      ({y1,y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom13 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 1 3 = Complex.normSq (c x6) + (Complex.normSq (c x8)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 1 = true ∧ s 3 = true) =
      ({x6,x8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top13 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 1 3 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y5))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 1 = true ∧ s 3 = true) =
      ({y1,y3,y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom14 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 1 4 = Complex.normSq (c x1) + (Complex.normSq (c x3) + (Complex.normSq (c x6))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 1 = true ∧ s 4 = true) =
      ({x1,x3,x6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top14 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 1 4 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y6))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 1 = true ∧ s 4 = true) =
      ({y1,y3,y6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom15 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 1 5 = Complex.normSq (c x1) + (Complex.normSq (c x5) + (Complex.normSq (c x6))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 1 = true ∧ s 5 = true) =
      ({x1,x5,x6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top15 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 1 5 = Complex.normSq (d y1) + (Complex.normSq (d y5) + (Complex.normSq (d y6))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 1 = true ∧ s 5 = true) =
      ({y1,y5,y6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom23 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 2 3 = Complex.normSq (c x7) + (Complex.normSq (c x8)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 2 = true ∧ s 3 = true) =
      ({x7,x8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top23 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 2 3 = Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y4))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 2 = true ∧ s 3 = true) =
      ({y1,y2,y4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom24 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 2 4 = Complex.normSq (c x1) + (Complex.normSq (c x4)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 2 = true ∧ s 4 = true) =
      ({x1,x4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top24 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 2 4 = Complex.normSq (d y1) + (Complex.normSq (d y4)) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 2 = true ∧ s 4 = true) =
      ({y1,y4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom25 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 2 5 = Complex.normSq (c x1) + (Complex.normSq (c x2)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 2 = true ∧ s 5 = true) =
      ({x1,x2} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top25 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 2 5 = Complex.normSq (d y1) + (Complex.normSq (d y2)) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 2 = true ∧ s 5 = true) =
      ({y1,y2} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom34 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 3 4 = Complex.normSq (c x6) + (Complex.normSq (c x9)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 3 = true ∧ s 4 = true) =
      ({x6,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top34 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 3 4 = Complex.normSq (d y1) + (Complex.normSq (d y3) + (Complex.normSq (d y4))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 3 = true ∧ s 4 = true) =
      ({y1,y3,y4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom35 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 3 5 = Complex.normSq (c x6) + (Complex.normSq (c x9)) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 3 = true ∧ s 5 = true) =
      ({x6,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top35 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 3 5 = Complex.normSq (d y1) + (Complex.normSq (d y2) + (Complex.normSq (d y5))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 3 = true ∧ s 5 = true) =
      ({y1,y2,y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_bottom45 (c : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S0 c 4 5 = Complex.normSq (c x1) + (Complex.normSq (c x6) + (Complex.normSq (c x9))) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun s => s 4 = true ∧ s 5 = true) =
      ({x1,x6,x9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2_top45 (d : SS.BitString 6 → ℂ) :
    SixQubit.occ2On S1 d 4 5 = Complex.normSq (d y1) + (Complex.normSq (d y6) + (Complex.normSq (d y9))) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun s => s 4 = true ∧ s 5 = true) =
      ({y1,y6,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-! ## Exact diagonal moment reduction -/

structure MomentSystem
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
      r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ) : Prop where
  n0 : q0+q1+q2+q3+q4+q5+q6+q7+q8+q9 = 1
  n1 : r0+r1+r2+r3+r4+r5+r6+r7+r8+r9 = 1
  m1 : q1+q3+q5+q7+q9 = r1+r3+r5+r7+r9
  m2 : q1+q3+q5+q6+q8 = r1+r3+r5+r6+r8
  m3 : q1+q2+q4+q7+q8 = r1+r2+r4+r7+r8
  m4 : q6+q7+q8+q9 = r0+r1+r2+r3+r4+r5
  m5 : q1+q3+q4+q6+q9 = r1+r3+r4+r6+r9
  m6 : q1+q2+q5+q6+q9 = r1+r2+r5+r6+r9
  m12 : q1+q3+q5 = r1+r3+r5
  m13 : q1+q7 = r1+r7
  m14 : q7+q9 = r1+r3+r5
  m15 : q1+q3+q9 = r1+r3+r9
  m16 : q1+q5+q9 = r1+r5+r9
  m23 : q1+q8 = r1+r8
  m24 : q6+q8 = r1+r3+r5
  m25 : q1+q3+q6 = r1+r3+r6
  m26 : q1+q5+q6 = r1+r5+r6
  m34 : q7+q8 = r1+r2+r4
  m35 : q1+q4 = r1+r4
  m36 : q1+q2 = r1+r2
  m45 : q6+q9 = r1+r3+r4
  m46 : q6+q9 = r1+r2+r5
  m56 : q1+q6+q9 = r1+r6+r9
  nq0 : 0 ≤ q0
  nq1 : 0 ≤ q1
  nq2 : 0 ≤ q2
  nq3 : 0 ≤ q3
  nq4 : 0 ≤ q4
  nq5 : 0 ≤ q5
  nq6 : 0 ≤ q6
  nq7 : 0 ≤ q7
  nq8 : 0 ≤ q8
  nq9 : 0 ≤ q9
  nr0 : 0 ≤ r0
  nr1 : 0 ≤ r1
  nr2 : 0 ≤ r2
  nr3 : 0 ≤ r3
  nr4 : 0 ≤ r4
  nr5 : 0 ≤ r5
  nr6 : 0 ≤ r6
  nr7 : 0 ≤ r7
  nr8 : 0 ≤ r8
  nr9 : 0 ≤ r9

/-- Every diagonal equation is derived from the genuine KL predicate. -/
theorem moments (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    MomentSystem
      (Complex.normSq (c x0)) (Complex.normSq (c x1))
      (Complex.normSq (c x2)) (Complex.normSq (c x3))
      (Complex.normSq (c x4)) (Complex.normSq (c x5))
      (Complex.normSq (c x6)) (Complex.normSq (c x7))
      (Complex.normSq (c x8)) (Complex.normSq (c x9))
      (Complex.normSq (d y0)) (Complex.normSq (d y1))
      (Complex.normSq (d y2)) (Complex.normSq (d y3))
      (Complex.normSq (d y4)) (Complex.normSq (d y5))
      (Complex.normSq (d y6)) (Complex.normSq (d y7))
      (Complex.normSq (d y8)) (Complex.normSq (d y9)) := by
  have hB := SixQubit.massOn_eq_one S0 c hc hnc
  have hT := SixQubit.massOn_eq_one S1 d hd hnd
  rw [mass_bottom] at hB
  rw [mass_top] at hT
  have hs0 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0
  have hs1 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1
  have hs2 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2
  have hs3 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3
  have hs4 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 4
  have hs5 := SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 5
  rw [occ_bottom0, occ_top0] at hs0
  rw [occ_bottom1, occ_top1] at hs1
  rw [occ_bottom2, occ_top2] at hs2
  rw [occ_bottom3, occ_top3] at hs3
  rw [occ_bottom4, occ_top4] at hs4
  rw [occ_bottom5, occ_top5] at hs5
  have hp01 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 1
  have hp02 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 2
  have hp03 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 3
  have hp04 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 4
  have hp05 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 5
  have hp12 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 2
  have hp13 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 3
  have hp14 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 4
  have hp15 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 5
  have hp23 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 3
  have hp24 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 4
  have hp25 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 5
  have hp34 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3 4
  have hp35 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3 5
  have hp45 := SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 4 5
  rw [occ2_bottom01, occ2_top01] at hp01
  rw [occ2_bottom02, occ2_top02] at hp02
  rw [occ2_bottom03, occ2_top03] at hp03
  rw [occ2_bottom04, occ2_top04] at hp04
  rw [occ2_bottom05, occ2_top05] at hp05
  rw [occ2_bottom12, occ2_top12] at hp12
  rw [occ2_bottom13, occ2_top13] at hp13
  rw [occ2_bottom14, occ2_top14] at hp14
  rw [occ2_bottom15, occ2_top15] at hp15
  rw [occ2_bottom23, occ2_top23] at hp23
  rw [occ2_bottom24, occ2_top24] at hp24
  rw [occ2_bottom25, occ2_top25] at hp25
  rw [occ2_bottom34, occ2_top34] at hp34
  rw [occ2_bottom35, occ2_top35] at hp35
  rw [occ2_bottom45, occ2_top45] at hp45
  refine ⟨by linarith [hB], by linarith [hT],
    by linarith [hs0], by linarith [hs1], by linarith [hs2],
    by linarith [hs3], by linarith [hs4], by linarith [hs5],
    by linarith [hp01], by linarith [hp02], by linarith [hp03],
    by linarith [hp04], by linarith [hp05], by linarith [hp12],
    by linarith [hp13], by linarith [hp14], by linarith [hp15],
    by linarith [hp23], by linarith [hp24], by linarith [hp25],
    by linarith [hp34], by linarith [hp35], by linarith [hp45],
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _,
    Complex.normSq_nonneg _, Complex.normSq_nonneg _⟩

structure BlockSolution
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
      r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ) : Prop where
  b1 : q0 = q1 ∧ q0 = r0 ∧ q0 = r1
  b2 : q2 = q3 ∧ q2 = r2 ∧ q2 = r3
  b3 : q4 = q5 ∧ q4 = r4 ∧ q4 = r5
  b4 : q6 = q7 ∧ q6 = r6 ∧ q6 = r7
  b5 : q8 = q9 ∧ q8 = r8 ∧ q8 = r9
  moving_sum : q0 + q2 + q4 = 1/4
  fixed_sum : q6 + q8 = 1/4

/-- Exact rational row reduction of the 23 diagonal KL equations. -/
theorem MomentSystem.solve
    {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
      r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (h : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
      r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) :
    BlockSolution q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
      r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 := by
  rcases h with ⟨n0,n1,m1,m2,m3,m4,m5,m6,m12,m13,m14,m15,m16,
    m23,m24,m25,m26,m34,m35,m36,m45,m46,m56,
    nq0,nq1,nq2,nq3,nq4,nq5,nq6,nq7,nq8,nq9,
    nr0,nr1,nr2,nr3,nr4,nr5,nr6,nr7,nr8,nr9⟩
  refine ⟨⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩,
    by linarith, by linarith⟩

/-- The ten displayed points are exactly five bottom pairs and their xor-eight
top partners. -/
theorem block_table_check :
    S0.card = 10 ∧ S1.card = 10 ∧
      SS.bxor x0 (nbit 8) = y0 ∧ SS.bxor x1 (nbit 8) = y1 ∧
      SS.bxor x2 (nbit 8) = y2 ∧ SS.bxor x3 (nbit 8) = y3 ∧
      SS.bxor x4 (nbit 8) = y4 ∧ SS.bxor x5 (nbit 8) = y5 ∧
      SS.bxor x6 (nbit 8) = y6 ∧ SS.bxor x7 (nbit 8) = y7 ∧
      SS.bxor x8 (nbit 8) = y8 ∧ SS.bxor x9 (nbit 8) = y9 := by decide

/-! ## The two Walsh combinations needed for the Gram simplex -/

def flip8 : SS.BitString 6 := nbit 8
def z00 : SS.BitString 6 := nbit 0
def z04 : SS.BitString 6 := nbit 4
def z08 : SS.BitString 6 := nbit 8
def z12 : SS.BitString 6 := nbit 12
def z32 : SS.BitString 6 := nbit 32
def z40 : SS.BitString 6 := nbit 40

theorem off8_00 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z00 = star (c x0) * d y0 + star (c x1) * d y1 + star (c x2) * d y2 + star (c x3) * d y3 + star (c x4) * d y4 + star (c x5) * d y5 + star (c x6) * d y6 + star (c x7) * d y7 + star (c x8) * d y8 + star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z00 y0 = false from by decide,
    show SS.bdot z00 y1 = false from by decide,
    show SS.bdot z00 y2 = false from by decide,
    show SS.bdot z00 y3 = false from by decide,
    show SS.bdot z00 y4 = false from by decide,
    show SS.bdot z00 y5 = false from by decide,
    show SS.bdot z00 y6 = false from by decide,
    show SS.bdot z00 y7 = false from by decide,
    show SS.bdot z00 y8 = false from by decide,
    show SS.bdot z00 y9 = false from by decide,
    SixQubit.signMul_false]
  ring

theorem off8_04 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z04 = star (c x0) * d y0 + (-star (c x1) * d y1) + (-star (c x2) * d y2) + star (c x3) * d y3 + (-star (c x4) * d y4) + star (c x5) * d y5 + star (c x6) * d y6 + (-star (c x7) * d y7) + (-star (c x8) * d y8) + star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z04 y0 = false from by decide,
    show SS.bdot z04 y1 = true from by decide,
    show SS.bdot z04 y2 = true from by decide,
    show SS.bdot z04 y3 = false from by decide,
    show SS.bdot z04 y4 = true from by decide,
    show SS.bdot z04 y5 = false from by decide,
    show SS.bdot z04 y6 = false from by decide,
    show SS.bdot z04 y7 = true from by decide,
    show SS.bdot z04 y8 = true from by decide,
    show SS.bdot z04 y9 = false from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem off8_08 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z08 = (-star (c x0) * d y0) + (-star (c x1) * d y1) + (-star (c x2) * d y2) + (-star (c x3) * d y3) + (-star (c x4) * d y4) + (-star (c x5) * d y5) + star (c x6) * d y6 + star (c x7) * d y7 + star (c x8) * d y8 + star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z08 y0 = true from by decide,
    show SS.bdot z08 y1 = true from by decide,
    show SS.bdot z08 y2 = true from by decide,
    show SS.bdot z08 y3 = true from by decide,
    show SS.bdot z08 y4 = true from by decide,
    show SS.bdot z08 y5 = true from by decide,
    show SS.bdot z08 y6 = false from by decide,
    show SS.bdot z08 y7 = false from by decide,
    show SS.bdot z08 y8 = false from by decide,
    show SS.bdot z08 y9 = false from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem off8_12 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z12 = (-star (c x0) * d y0) + star (c x1) * d y1 + star (c x2) * d y2 + (-star (c x3) * d y3) + star (c x4) * d y4 + (-star (c x5) * d y5) + star (c x6) * d y6 + (-star (c x7) * d y7) + (-star (c x8) * d y8) + star (c x9) * d y9 := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z12 y0 = true from by decide,
    show SS.bdot z12 y1 = false from by decide,
    show SS.bdot z12 y2 = false from by decide,
    show SS.bdot z12 y3 = true from by decide,
    show SS.bdot z12 y4 = false from by decide,
    show SS.bdot z12 y5 = true from by decide,
    show SS.bdot z12 y6 = false from by decide,
    show SS.bdot z12 y7 = true from by decide,
    show SS.bdot z12 y8 = true from by decide,
    show SS.bdot z12 y9 = false from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem off8_32 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z32 = star (c x0) * d y0 + (-star (c x1) * d y1) + (-star (c x2) * d y2) + star (c x3) * d y3 + star (c x4) * d y4 + (-star (c x5) * d y5) + (-star (c x6) * d y6) + star (c x7) * d y7 + star (c x8) * d y8 + (-star (c x9) * d y9) := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z32 y0 = false from by decide,
    show SS.bdot z32 y1 = true from by decide,
    show SS.bdot z32 y2 = true from by decide,
    show SS.bdot z32 y3 = false from by decide,
    show SS.bdot z32 y4 = false from by decide,
    show SS.bdot z32 y5 = true from by decide,
    show SS.bdot z32 y6 = true from by decide,
    show SS.bdot z32 y7 = false from by decide,
    show SS.bdot z32 y8 = false from by decide,
    show SS.bdot z32 y9 = true from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

theorem off8_40 (c d : SS.BitString 6 → ℂ) :
    SixQubit.offSumOn S0 S1 c d flip8 z40 = (-star (c x0) * d y0) + star (c x1) * d y1 + star (c x2) * d y2 + (-star (c x3) * d y3) + (-star (c x4) * d y4) + star (c x5) * d y5 + (-star (c x6) * d y6) + star (c x7) * d y7 + star (c x8) * d y8 + (-star (c x9) * d y9) := by
  unfold SixQubit.offSumOn
  rw [show S1.filter (fun y => SS.bxor y flip8 ∈ S0) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor y0 flip8 = x0 from by decide,
    show SS.bxor y1 flip8 = x1 from by decide,
    show SS.bxor y2 flip8 = x2 from by decide,
    show SS.bxor y3 flip8 = x3 from by decide,
    show SS.bxor y4 flip8 = x4 from by decide,
    show SS.bxor y5 flip8 = x5 from by decide,
    show SS.bxor y6 flip8 = x6 from by decide,
    show SS.bxor y7 flip8 = x7 from by decide,
    show SS.bxor y8 flip8 = x8 from by decide,
    show SS.bxor y9 flip8 = x9 from by decide]
  simp only [show SS.bdot z40 y0 = true from by decide,
    show SS.bdot z40 y1 = false from by decide,
    show SS.bdot z40 y2 = false from by decide,
    show SS.bdot z40 y3 = true from by decide,
    show SS.bdot z40 y4 = true from by decide,
    show SS.bdot z40 y5 = false from by decide,
    show SS.bdot z40 y6 = true from by decide,
    show SS.bdot z40 y7 = false from by decide,
    show SS.bdot z40 y8 = false from by decide,
    show SS.bdot z40 y9 = true from by decide,
    SixQubit.signMul_true, SixQubit.signMul_false]
  ring

/-- The exact four-row Walsh certificate for the moving three-block triangle. -/
theorem cross_triangle (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    star (c x0) * d y0 + star (c x3) * d y3 + star (c x4) * d y4 = 0 := by
  have h0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z00 (by decide)
  have h8 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z08 (by decide)
  have h32 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z32 (by decide)
  have h40 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z40 (by decide)
  rw [off8_00] at h0
  rw [off8_08] at h8
  rw [off8_32] at h32
  rw [off8_40] at h40
  linear_combination (1/4) * h0 - (1/4) * h8 + (1/4) * h32 - (1/4) * h40

/-- The exact four-row Walsh certificate that equates the two fixed masses. -/
theorem cross_fixed (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    star (c x7) * d y7 + star (c x8) * d y8 = 0 := by
  have h0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z00 (by decide)
  have h4 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z04 (by decide)
  have h8 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z08 (by decide)
  have h12 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    flip8 z12 (by decide)
  rw [off8_00] at h0
  rw [off8_04] at h4
  rw [off8_08] at h8
  rw [off8_12] at h12
  linear_combination (1/4) * h0 - (1/4) * h4 + (1/4) * h8 - (1/4) * h12
end

end SixQubit.Orbit45Support
