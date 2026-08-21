import Mathlib

import SixQubit.CodeBridge
import SixQubit.Orbit55

/-!
# Orbit55: the no-go with no Knill--Laflamme hypothesis

`SixQubit.Orbit55.no_go_of_moments` takes its Knill--Laflamme rows as
hypotheses.  This module *derives* every one of them, from the statement
that `![c, d]` is a normalized two-dimensional code of distance three whose
two logical states are supported on `S0` and `S1`.  The bridge is
`SixQubit.CodeBridge`; the resulting `no_code` has no Knill--Laflamme
hypothesis left, so it says that no such code exists, not merely that a
finite system of equations is unsatisfiable.

Every Pauli instantiated below is checked to have weight at most two by
`decide`, since `SS.HasDistance _ 3` only supplies weight `≤ 2` rows.

Generated mechanically; no `sorry`, no `native_decide`.
-/

namespace SixQubit.Orbit55

open scoped BigOperators

noncomputable section

/-! ## Explicit evaluation of the masses and occupation numbers -/

theorem massB (c : SS.BitString 6 -> ℂ) :
    SixQubit.massOn S0 c =
      Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.massOn
  rw [show S0
        = ({y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10} : Finset (SS.BitString 6)) from by decide,
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

theorem massT (d : SS.BitString 6 -> ℂ) :
    SixQubit.massOn S1 d =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.massOn
  rw [show S1
        = ({z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
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

theorem occB0 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 0 =
      Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 0 = true)
        = ({y6, y7, y8, y9, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT0 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 0 =
      Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 0 = true)
        = ({z5, z6, z7, z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 1 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 1 = true)
        = ({y3, y4, y5, y9, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 1 =
      Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 1 = true)
        = ({z2, z3, z4, z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 2 =
      Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y10) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 2 = true)
        = ({y2, y4, y5, y7, y8, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 2 =
      Complex.normSq (d z1) + Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 2 = true)
        = ({z1, z4, z7, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 3 =
      Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) + Complex.normSq (c y10) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 3 = true)
        = ({y1, y3, y5, y6, y8, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 3 =
      Complex.normSq (d z1) + Complex.normSq (d z3) + Complex.normSq (d z6) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 3 = true)
        = ({z1, z3, z6, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 4 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 4 = true)
        = ({y3, y4, y5, y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 4 =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 4 = true)
        = ({z0, z1, z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occB5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 5 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y5) + Complex.normSq (c y8) + Complex.normSq (c y9) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 5 = true)
        = ({y1, y2, y5, y8, y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occT5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 5 =
      Complex.normSq (d z0) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z10) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 5 = true)
        = ({z0, z3, z4, z6, z7, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B01 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 1 =
      Complex.normSq (c y9) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({y9, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2T01 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 1 =
      Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B02 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 2 =
      Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({y7, y8, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T02 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 2 =
      Complex.normSq (d z7) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({z7, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B03 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 3 =
      Complex.normSq (c y6) + Complex.normSq (c y8) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({y6, y8, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T03 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 3 =
      Complex.normSq (d z6) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({z6, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B04 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 4 =
      Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T04 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 4 =
      Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B05 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 5 =
      Complex.normSq (c y8) + Complex.normSq (c y9) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({y8, y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2T05 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 5 =
      Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({z6, z7, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B12 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 2 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({y4, y5, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T12 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 2 =
      Complex.normSq (d z4) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({z4, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B13 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 3 =
      Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({y3, y5, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T13 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 3 =
      Complex.normSq (d z3) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({z3, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B14 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 4 =
      Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({y3, y4, y5} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T14 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 4 =
      Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({z8, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B15 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 5 =
      Complex.normSq (c y5) + Complex.normSq (c y9) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({y5, y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2T15 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 5 =
      Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({z3, z4, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B23 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 3 =
      Complex.normSq (c y5) + Complex.normSq (c y8) + Complex.normSq (c y10) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({y5, y8, y10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T23 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 3 =
      Complex.normSq (d z1) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({z1, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2B24 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 4 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({y4, y5, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T24 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 4 =
      Complex.normSq (d z1) + Complex.normSq (d z9) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({z1, z9, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B25 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 5 =
      Complex.normSq (c y2) + Complex.normSq (c y5) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({y2, y5, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T25 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 5 =
      Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({z4, z7, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B34 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 3 4 =
      Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({y3, y5, y6, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T34 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 3 4 =
      Complex.normSq (d z1) + Complex.normSq (d z8) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({z1, z8, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B35 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 3 5 =
      Complex.normSq (c y1) + Complex.normSq (c y5) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({y1, y5, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2T35 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 3 5 =
      Complex.normSq (d z3) + Complex.normSq (d z6) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({z3, z6, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem occ2B45 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 4 5 =
      Complex.normSq (c y5) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({y5, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

theorem occ2T45 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 4 5 =
      Complex.normSq (d z0) + Complex.normSq (d z10) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({z0, z10} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-! ## The moment system, derived from distance three -/

/-- Every row of `MomentSystem` is a consequence of the honest
Knill--Laflamme conditions: the normalizations come from `⟪c,c⟫ = ⟪d,d⟫ = 1`,
and the one- and two-bit rows are the diagonal conditions for `Zᵢ` and
`Zᵢ Zⱼ` after the character/occupation change of basis. -/
theorem moments (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    MomentSystem
      (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10))
      (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) := by
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
  exact ⟨hB, hT, hs0, hs1, hs2, hs3, hs4, hs5, hp01, hp02, hp03, hp04, hp05, hp12, hp13, hp14, hp15, hp23, hp24, hp25, hp34, hp35, hp45, (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _)⟩

/-! ## The wrapper -/

/-- The two fibers are disjoint, so the two logical states are automatically
orthogonal.  This is proved, never assumed. -/
theorem orthogonal (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0) :
    SS.innerC c d = 0 :=
  SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d hc hd (by decide)

/-- **No such code exists.**  Not one Knill--Laflamme row is assumed:
`hdist` is the genuine distance-three condition, and every row that
`no_go_of_moments` needs is derived from it. -/
theorem no_code (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : False :=
  no_go_of_moments c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef5 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef7 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w0 (by decide))

end

end SixQubit.Orbit55
