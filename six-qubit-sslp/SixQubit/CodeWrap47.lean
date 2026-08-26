import Mathlib

import SixQubit.CodeBridge
import SixQubit.Orbit47

/-!
# Orbit47: a code-level wrapper with no Knill--Laflamme hypothesis

`SixQubit.Orbit47.no_go_of_moments` takes each Knill--Laflamme row as a
hypothesis, so read literally it says only that a finite system of equations
is unsatisfiable.  This module *derives* every one of those rows from

* support of the two logical states on the two residue fibers `S0`, `S1`,
* normalization `⟪c, c⟫ = ⟪d, d⟫ = 1`, and
* `SS.HasDistance ![c, d] 3`, the genuine distance-three condition,

via `SixQubit.CodeBridge`, and concludes `no_code`: no such code exists.
Orthogonality of the two logical states is proved from disjointness of the
fibers (`orthogonal`), never assumed.

Every Pauli instantiated below carries a named weight bound `wt_*`, checked
by the kernel, since `SS.HasDistance _ 3 = SS.Detects _ 2` supplies rows only
for Paulis of weight at most two.

No `sorry`, no `native_decide`.
-/

namespace SixQubit.CodeWrap47

open scoped BigOperators
open SixQubit.Orbit47

noncomputable section

/-! ## Explicit evaluation of the masses and occupation numbers

Each finset identity below is decided by the Lean kernel. -/

theorem massB (c : SS.BitString 6 -> ℂ) :
    SixQubit.massOn S0 c =
      Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.massOn
  rw [show S0
        = ({y0, y1, y2, y3, y4, y5, y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem massT (d : SS.BitString 6 -> ℂ) :
    SixQubit.massOn S1 d =
      Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.massOn
  rw [show S1
        = ({z0, z1, z2, z3, z4, z5, z6, z7, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB0 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 0 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 0 = true)
        = ({y4, y5, y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 1 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 1 = true)
        = ({y2, y3, y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 2 =
      Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 2 = true)
        = ({y1, y3, y5, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 3 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 3 = true)
        = ({y1, y2, y4, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 4 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 4 = true)
        = ({y1, y2, y3, y4, y5, y6, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occB5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S0 c 5 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.occOn
  rw [show S0.filter (fun x => x 5 = true)
        = ({y1, y2, y3, y4, y5, y6, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT0 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 0 =
      Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 0 = true)
        = ({z5, z6, z7, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 1 =
      Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 1 = true)
        = ({z3, z4, z7, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 2 =
      Complex.normSq (d z2) + Complex.normSq (d z4) + Complex.normSq (d z6) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 2 = true)
        = ({z2, z4, z6, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 3 =
      Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z5) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 3 = true)
        = ({z2, z3, z5, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 4 =
      Complex.normSq (d z1) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 4 = true)
        = ({z1, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occT5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occOn S1 d 5 =
      Complex.normSq (d z0) + Complex.normSq (d z8) := by
  unfold SixQubit.occOn
  rw [show S1.filter (fun x => x 5 = true)
        = ({z0, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B01 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 1 =
      Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({y6, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B02 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 2 =
      Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({y5, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B03 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 3 =
      Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({y4, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B04 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 4 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({y4, y5, y6, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B05 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 0 5 =
      Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({y4, y5, y6, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B12 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 2 =
      Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({y3, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B13 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 3 =
      Complex.normSq (c y2) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({y2, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B14 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 4 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({y2, y3, y6, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B15 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 1 5 =
      Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({y2, y3, y6, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B23 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 3 =
      Complex.normSq (c y1) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({y1, y7, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B24 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 4 =
      Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({y1, y3, y5, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B25 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 2 5 =
      Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({y1, y3, y5, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B34 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 3 4 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y8) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({y1, y2, y4, y8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B35 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 3 5 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({y1, y2, y4, y7} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2B45 (c : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S0 c 4 5 =
      Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) := by
  unfold SixQubit.occ2On
  rw [show S0.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({y1, y2, y3, y4, y5, y6} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T01 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 1 =
      Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 1 = true)
        = ({z7, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T02 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 2 =
      Complex.normSq (d z6) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 2 = true)
        = ({z6, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T03 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 3 =
      Complex.normSq (d z5) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 3 = true)
        = ({z5, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T04 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 4 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 4 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T05 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 0 5 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 0 = true ∧ x 5 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T12 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 2 =
      Complex.normSq (d z4) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 2 = true)
        = ({z4, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T13 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 3 =
      Complex.normSq (d z3) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 3 = true)
        = ({z3, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T14 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 4 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 4 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T15 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 1 5 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 1 = true ∧ x 5 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T23 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 3 =
      Complex.normSq (d z2) + Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 3 = true)
        = ({z2, z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  try ring

theorem occ2T24 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 4 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 4 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T25 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 2 5 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 2 = true ∧ x 5 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T34 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 3 4 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 4 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T35 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 3 5 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 3 = true ∧ x 5 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

theorem occ2T45 (d : SS.BitString 6 -> ℂ) :
    SixQubit.occ2On S1 d 4 5 =
      Complex.normSq (d z8) := by
  unfold SixQubit.occ2On
  rw [show S1.filter (fun x => x 4 = true ∧ x 5 = true)
        = ({z8} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_singleton]
  try ring

/-! ## Obligation (B'): the moment system

The `MomentSystem` rows are occupation-number equalities.  They come from the
diagonal Knill--Laflamme conditions for the pure-`Z` Paulis `Zᵢ` and `ZᵢZⱼ`
after the explicit character/occupation change of basis carried out in
`SixQubit.CodeBridge` (`charOn_stdBasis`, `charOn_stdBasis_pair`); the two
normalization rows come from `⟪c, c⟫ = ⟪d, d⟫ = 1`, and every
nonnegativity row from `Complex.normSq_nonneg`. -/
theorem moments (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    MomentSystem
      (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
      (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) := by
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
  exact ⟨hB, hT, hs0, hs1, hs2, hs3, hs4, hs5, hp01, hp02, hp03, hp04, hp05, hp12, hp13, hp14, hp15, hp23, hp24, hp25, hp34, hp35, hp45, (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _), (Complex.normSq_nonneg _)⟩

/-! ## The Pauli weight bounds

`SS.HasDistance ![c, d] 3` unfolds to `SS.Detects ![c, d] 2`, so a row is
available only for a Pauli of weight at most two.  Each bound below is
decided by the kernel. -/

/-- The Pauli with flip mask `ef` and dressing `w0` has weight 1. -/
theorem wt_ef_w0 : (⟨ef, w0⟩ : SS.PauliString 6).wt ≤ 2 := by decide
/-- The Pauli with flip mask `ef` and dressing `w1` has weight 2. -/
theorem wt_ef_w1 : (⟨ef, w1⟩ : SS.PauliString 6).wt ≤ 2 := by decide

/-! ## The wrapper -/

/-- The two residue fibers are disjoint, so the two logical states are
automatically orthogonal.  This is proved, not assumed. -/
theorem orthogonal (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0) :
    SS.innerC c d = 0 :=
  SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d hc hd (by decide)

/-- **No such code exists.**  Not one Knill--Laflamme row is assumed: `hdist`
is the genuine distance-three condition and every row that
`Orbit47.no_go_of_moments` needs is derived from it.

Obligation (A) supplies the `offSum` rows from the `j ≠ k` Knill--Laflamme
condition. -/
theorem no_code (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : False :=
  no_go_of_moments c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef w0 wt_ef_w0)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef w1 wt_ef_w1)

end

end SixQubit.CodeWrap47
