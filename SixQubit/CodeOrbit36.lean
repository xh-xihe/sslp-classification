import Mathlib

import SixQubit.CodeBridge
import SixQubit.Orbit36
import SixQubit.Orbit36Final

/-!
# Orbit 36 at the level of codes

`Orbit36Final.orbit36_rigidity` and its companions take the moment system and
twenty-two Knill--Laflamme rows as hypotheses.  This module *derives* every one
of them from the statement that `![c, d]` is a normalized two-dimensional code
of distance three supported on the two fibers of orbit 36, which is what the
fifty-one no-go wrappers already did for their orbits.

The difference matters for what the rigidity theorem is about.  Before this,
it spoke of amplitude pairs satisfying certain moment conditions; after it, of
every exact code in the orbit.

Every Pauli instantiated below is checked to have weight at most two by
`decide`, since `SS.HasDistance _ 3` supplies only weight `<= 2` rows.

Generated mechanically by `tools/generators/gencode36.py`; no `sorry`, no
`native_decide`.
-/

namespace SixQubit.Orbit36

open scoped BigOperators
open scoped ComplexConjugate
-- the lifted conclusion names `AEnum` unqualified, as `Orbit36Final` does
open SixQubit.Orbit36Phase (AEnum)

noncomputable section

/-! ## Expanding the generic sums over this orbit's two supports -/

theorem massB :
    SixQubit.massOn S0 c =
      Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) := by
  unfold SixQubit.massOn
  rw [show S0
        = ({y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem massT :
    SixQubit.massOn S1 d =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) := by
  unfold SixQubit.massOn
  rw [show S1
        = ({z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB0 :
    SixQubit.occOn S0 c 0 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 0 = true)
        = ({y3, y4, y5, y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT0 :
    SixQubit.occOn S1 d 0 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 0 = true)
        = ({z0, z1, z2, z9, z10, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB1 :
    SixQubit.occOn S0 c 1 =
      Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 1 = true)
        = ({y2, y4, y5, y6, y9, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT1 :
    SixQubit.occOn S1 d 1 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z3) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z11) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 1 = true)
        = ({z0, z1, z3, z7, z8, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB2 :
    SixQubit.occOn S0 c 2 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y11) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 2 = true)
        = ({y2, y3, y5, y7, y9, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT2 :
    SixQubit.occOn S1 d 2 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z4) + Complex.normSq (d z6) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 2 = true)
        = ({z0, z1, z4, z6, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB3 :
    SixQubit.occOn S0 c 3 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y8) + Complex.normSq (c y10) + Complex.normSq (c y11) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 3 = true)
        = ({y2, y3, y4, y8, y10, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT3 :
    SixQubit.occOn S1 d 3 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z9) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 3 = true)
        = ({z0, z1, z5, z6, z7, z9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB4 :
    SixQubit.occOn S0 c 4 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 4 = true)
        = ({y1, y2, y3, y4, y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT4 :
    SixQubit.occOn S1 d 4 =
      Complex.normSq (d z0) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 4 = true)
        = ({z0, z6, z7, z8, z9, z10, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB5 :
    SixQubit.occOn S0 c 5 =
      Complex.normSq (c y1) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 5 = true)
        = ({y1, y6, y7, y8, y9, y10, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT5 :
    SixQubit.occOn S1 d 5 =
      Complex.normSq (d z0) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 5 = true)
        = ({z0, z2, z3, z4, z5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B01 :
    SixQubit.occ2On S0 c 0 1 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({y4, y5, y6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T01 :
    SixQubit.occ2On S1 d 0 1 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z11) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({z0, z1, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B02 :
    SixQubit.occ2On S0 c 0 2 =
      Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({y3, y5, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T02 :
    SixQubit.occ2On S1 d 0 2 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({z0, z1, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B03 :
    SixQubit.occ2On S0 c 0 3 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({y3, y4, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T03 :
    SixQubit.occ2On S1 d 0 3 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z9) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({z0, z1, z9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B04 :
    SixQubit.occ2On S0 c 0 4 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({y3, y4, y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T04 :
    SixQubit.occ2On S1 d 0 4 =
      Complex.normSq (d z0) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({z0, z9, z10, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B05 :
    SixQubit.occ2On S0 c 0 5 =
      Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T05 :
    SixQubit.occ2On S1 d 0 5 =
      Complex.normSq (d z0) + Complex.normSq (d z2) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({z0, z2} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2B12 :
    SixQubit.occ2On S0 c 1 2 =
      Complex.normSq (c y2) + Complex.normSq (c y5) + Complex.normSq (c y9) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({y2, y5, y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T12 :
    SixQubit.occ2On S1 d 1 2 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({z0, z1, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B13 :
    SixQubit.occ2On S0 c 1 3 =
      Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({y2, y4, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T13 :
    SixQubit.occ2On S1 d 1 3 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z7) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({z0, z1, z7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B14 :
    SixQubit.occ2On S0 c 1 4 =
      Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y5) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({y2, y4, y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T14 :
    SixQubit.occ2On S1 d 1 4 =
      Complex.normSq (d z0) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z11) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({z0, z7, z8, z11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B15 :
    SixQubit.occ2On S0 c 1 5 =
      Complex.normSq (c y6) + Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({y6, y9, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T15 :
    SixQubit.occ2On S1 d 1 5 =
      Complex.normSq (d z0) + Complex.normSq (d z3) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({z0, z3} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2B23 :
    SixQubit.occ2On S0 c 2 3 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y11) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({y2, y3, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T23 :
    SixQubit.occ2On S1 d 2 3 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z6) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({z0, z1, z6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B24 :
    SixQubit.occ2On S0 c 2 4 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y5) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({y2, y3, y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T24 :
    SixQubit.occ2On S1 d 2 4 =
      Complex.normSq (d z0) + Complex.normSq (d z6) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({z0, z6, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B25 :
    SixQubit.occ2On S0 c 2 5 =
      Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y11) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({y7, y9, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T25 :
    SixQubit.occ2On S1 d 2 5 =
      Complex.normSq (d z0) + Complex.normSq (d z4) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({z0, z4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2B34 :
    SixQubit.occ2On S0 c 3 4 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({y2, y3, y4} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T34 :
    SixQubit.occ2On S1 d 3 4 =
      Complex.normSq (d z0) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z9) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({z0, z6, z7, z9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B35 :
    SixQubit.occ2On S0 c 3 5 =
      Complex.normSq (c y8) + Complex.normSq (c y10) + Complex.normSq (c y11) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({y8, y10, y11} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T35 :
    SixQubit.occ2On S1 d 3 5 =
      Complex.normSq (d z0) + Complex.normSq (d z5) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({z0, z5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2B45 :
    SixQubit.occ2On S0 c 4 5 =
      Complex.normSq (c y1) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({y1} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]

theorem occ2T45 :
    SixQubit.occ2On S1 d 4 5 =
      Complex.normSq (d z0) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({z0} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]

/-! ## The moment system, derived from distance three -/

/-- Every row of `MomentSystem` is a consequence of the honest
Knill--Laflamme conditions: the normalizations come from the unit norms, the
one- and two-bit rows are the diagonal conditions for `Z_i` and `Z_i Z_j`
after the occupation change of basis, and the nonnegativity rows hold because
every entry is a squared modulus. -/
theorem moments (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    MomentSystem
      (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
      (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) := by
  have hB : SixQubit.massOn S0 c = 1 := SixQubit.massOn_eq_one S0 c hc hnc
  have hT : SixQubit.massOn S1 d = 1 := SixQubit.massOn_eq_one S1 d hd hnd
  rw [massB] at hB
  rw [massT] at hT
  have hs0 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0
  rw [occB0, occT0] at hs0
  have hs1 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1
  rw [occB1, occT1] at hs1
  have hs2 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2
  rw [occB2, occT2] at hs2
  have hs3 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3
  rw [occB3, occT3] at hs3
  have hs4 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 4
  rw [occB4, occT4] at hs4
  have hs5 :=
    SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 5
  rw [occB5, occT5] at hs5
  have hp01 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 1
  rw [occ2B01, occ2T01] at hp01
  have hp02 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 2
  rw [occ2B02, occ2T02] at hp02
  have hp03 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 3
  rw [occ2B03, occ2T03] at hp03
  have hp04 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 4
  rw [occ2B04, occ2T04] at hp04
  have hp05 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 0 5
  rw [occ2B05, occ2T05] at hp05
  have hp12 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 2
  rw [occ2B12, occ2T12] at hp12
  have hp13 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 3
  rw [occ2B13, occ2T13] at hp13
  have hp14 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 4
  rw [occ2B14, occ2T14] at hp14
  have hp15 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 1 5
  rw [occ2B15, occ2T15] at hp15
  have hp23 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 3
  rw [occ2B23, occ2T23] at hp23
  have hp24 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 4
  rw [occ2B24, occ2T24] at hp24
  have hp25 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 2 5
  rw [occ2B25, occ2T25] at hp25
  have hp34 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3 4
  rw [occ2B34, occ2T34] at hp34
  have hp35 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 3 5
  rw [occ2B35, occ2T35] at hp35
  have hp45 :=
    SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist 4 5
  rw [occ2B45, occ2T45] at hp45
  exact ⟨hB, hT, hs0, hs1, hs2, hs3, hs4, hs5, hp01, hp02, hp03, hp04, hp05, hp12, hp13, hp14, hp15, hp23, hp24, hp25, hp34, hp35, hp45, (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _)⟩

/-! ## The bridge -/

/-- The twenty-two Knill--Laflamme rows the rigidity theorem needs, each
derived from `hdist` rather than assumed. -/
theorem klRows (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdist : SS.HasDistance ![c, d] 3) :
     offSum c d ex1 w0 = 0 ∧
         offSum c d ex1 w2 = 0 ∧
         offSum c d ex1 w3 = 0 ∧
         offSum c d ex1 w4 = 0 ∧
         offSum c d ex2 w0 = 0 ∧
         offSum c d ex2 w1 = 0 ∧
         offSum c d ex2 w3 = 0 ∧
         offSum c d ex2 w4 = 0 ∧
         offSum c d ex3 w0 = 0 ∧
         offSum c d ex3 w1 = 0 ∧
         offSum c d ex3 w2 = 0 ∧
         offSum c d ex3 w4 = 0 ∧
         offSum c d ex4 w0 = 0 ∧
         offSum c d ex4 w1 = 0 ∧
         offSum c d ex4 w2 = 0 ∧
         offSum c d ex4 w3 = 0 ∧
         offSum c d ex15 w0 = 0 ∧
         offSum c d ex25 w0 = 0 ∧
         offSum c d ex35 w0 = 0 ∧
         offSum c d ex45 w0 = 0 ∧
         offSum c d ex56 w0 = 0 ∧
         offSum c d SixQubit.Orbit36Enum.ex16 w0 = 0 :=
  ⟨SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex1 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex1 w2 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex1 w3 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex1 w4 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex2 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex2 w1 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex2 w3 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex2 w4 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex3 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex3 w1 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex3 w2 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex3 w4 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex4 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex4 w1 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex4 w2 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex4 w3 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex15 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex25 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex35 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex45 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist ex56 w0 (by decide), SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist SixQubit.Orbit36Enum.ex16 w0 (by decide)⟩

/-- **Orbit 36 is rigid, at the level of codes.**

Not one moment row and not one Knill--Laflamme row is assumed.  `hdist` is the
genuine distance-three condition, and everything
`Orbit36Final.orbit36_rigidity` needs is derived from it above.  So this says
what the manuscript says: every exact code in orbit 36 has the stated
magnitudes, is local-monomial equivalent to the canonical pair, and has the
stated weight enumerator. -/
theorem rigid_code (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    (Complex.normSq (c y0) = 1/10
        ∧ Complex.normSq (c y1) = 1/10
        ∧ Complex.normSq (c y2) = 1/10
        ∧ Complex.normSq (c y3) = 1/10
        ∧ Complex.normSq (c y4) = 1/10
        ∧ Complex.normSq (c y5) = 1/10
        ∧ Complex.normSq (c y6) = 1/15
        ∧ Complex.normSq (c y7) = 1/15
        ∧ Complex.normSq (c y8) = 1/15
        ∧ Complex.normSq (c y9) = 1/15
        ∧ Complex.normSq (c y10) = 1/15
        ∧ Complex.normSq (c y11) = 1/15
        ∧ Complex.normSq (d z0) = 1/10
        ∧ Complex.normSq (d z1) = 1/10
        ∧ Complex.normSq (d z2) = 1/10
        ∧ Complex.normSq (d z3) = 1/10
        ∧ Complex.normSq (d z4) = 1/10
        ∧ Complex.normSq (d z5) = 1/10
        ∧ Complex.normSq (d z6) = 1/15
        ∧ Complex.normSq (d z7) = 1/15
        ∧ Complex.normSq (d z8) = 1/15
        ∧ Complex.normSq (d z9) = 1/15
        ∧ Complex.normSq (d z10) = 1/15
        ∧ Complex.normSq (d z11) = 1/15)
      ∧ (c y0 ≠ 0
        ∧ c y1 ≠ 0
        ∧ c y2 ≠ 0
        ∧ c y3 ≠ 0
        ∧ c y4 ≠ 0
        ∧ c y5 ≠ 0
        ∧ c y6 ≠ 0
        ∧ c y7 ≠ 0
        ∧ c y8 ≠ 0
        ∧ c y9 ≠ 0
        ∧ c y10 ≠ 0
        ∧ c y11 ≠ 0
        ∧ d z0 ≠ 0
        ∧ d z1 ≠ 0
        ∧ d z2 ≠ 0
        ∧ d z3 ≠ 0
        ∧ d z4 ≠ 0
        ∧ d z5 ≠ 0
        ∧ d z6 ≠ 0
        ∧ d z7 ≠ 0
        ∧ d z8 ≠ 0
        ∧ d z9 ≠ 0
        ∧ d z10 ≠ 0
        ∧ d z11 ≠ 0)
      ∧ CodeEquiv.Equivalent ![c, d] ![Orbit36Code.c36, Orbit36Code.d36]
      ∧ SS.HasDistance ![c, d] 3
      ∧ (AEnum c d 0 = 1
          ∧ AEnum c d 1 = 0
          ∧ AEnum c d 2 = 21/25
          ∧ AEnum c d 3 = 0
          ∧ AEnum c d 4 = 291/25
          ∧ AEnum c d 5 = 384/25
          ∧ AEnum c d 6 = 79/25) := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21⟩ :=
    klRows c d hc hd hdist
  exact Orbit36Final.orbit36_rigidity c d hc hd
    (moments c d hc hd hnc hnd hdist)
    r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21

end

end SixQubit.Orbit36
