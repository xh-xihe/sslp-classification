import Mathlib

import SixQubit.MaskBridge
import SixQubit.Orbit47

/-!
# Orbit 47: no code, not merely no solution

`SixQubit.Orbit47.no_go_of_moments` takes its Knill--Laflamme data as
hypotheses.  This module discharges those hypotheses from the honest
hypothesis `SS.HasDistance ![c, d] 3`, using `SixQubit.MaskBridge`, and
records the resulting hypothesis-free statement `no_code`.

The two Paulis the orbit needs off-diagonally are `X_6` and `X_6 Z_5`
(masks `ef = 000001` with dressings `w0 = 000000`, `w1 = 000010`); both have
weight `≤ 2`, checked by `decide` in `wt_ef_w0` / `wt_ef_w1`.  The twenty-one
moment rows are the diagonal conditions for the pure-`Z` Paulis `Z_i` and
`Z_i Z_j`, and the two normalisations are `⟪ c, c ⟫ = ⟪ d, d ⟫ = 1`.

No `sorry`, no `native_decide`.
-/

namespace SixQubit.Orbit47

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The orbit's Walsh sum is the generic one -/

/-- The orbit-local `offSum` is the generic `offSumG` at this orbit's supports. -/
theorem offSum_eq_offSumG (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) :
    offSum c d e z = SixQubit.MaskBridge.offSumG S0 S1 c d e z := rfl

/-! ## Disjoint fibers, hence orthogonal logical states -/

theorem S0_disjoint_S1 : Disjoint S0 S1 := by
  rw [Finset.disjoint_left]
  decide

/-- Orthogonality of the two logical states is **derived**, not assumed. -/
theorem logical_orthogonal (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    SS.innerC c d = 0 :=
  SixQubit.MaskBridge.IsCode.orthogonal ⟨hc, hd, hnc, hnd, hdist⟩ S0_disjoint_S1

/-! ## The two Paulis used off-diagonally have weight at most two -/

theorem wt_ef_w0 : (SS.PauliString.mk ef w0).wt ≤ 2 := by decide
theorem wt_ef_w1 : (SS.PauliString.mk ef w1).wt ≤ 2 := by decide

/-! ## Total mass -/
theorem mass_bot (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.mass S0 c
      = Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.mass S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem mass_top (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.mass S1 d
      = Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.mass S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ## Single-qubit occupation rows -/
theorem fil1_bot_0 : S0.filter (fun x => x (0 : Fin 6) = true) = {y4, y5, y6, y7, y8} := by decide
theorem occ1_bot_0 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 0 = Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_0 : S1.filter (fun x => x (0 : Fin 6) = true) = {z5, z6, z7, z8} := by decide
theorem occ1_top_0 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 0 = Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_1 : S0.filter (fun x => x (1 : Fin 6) = true) = {y2, y3, y6, y7, y8} := by decide
theorem occ1_bot_1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 1 = Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_1 : S1.filter (fun x => x (1 : Fin 6) = true) = {z3, z4, z7, z8} := by decide
theorem occ1_top_1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 1 = Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_2 : S0.filter (fun x => x (2 : Fin 6) = true) = {y1, y3, y5, y7, y8} := by decide
theorem occ1_bot_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 2 = Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_2 : S1.filter (fun x => x (2 : Fin 6) = true) = {z2, z4, z6, z8} := by decide
theorem occ1_top_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 2 = Complex.normSq (d z2) + Complex.normSq (d z4) + Complex.normSq (d z6) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_3 : S0.filter (fun x => x (3 : Fin 6) = true) = {y1, y2, y4, y7, y8} := by decide
theorem occ1_bot_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 3 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_3 : S1.filter (fun x => x (3 : Fin 6) = true) = {z2, z3, z5, z8} := by decide
theorem occ1_top_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 3 = Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z5) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_4 : S0.filter (fun x => x (4 : Fin 6) = true) = {y1, y2, y3, y4, y5, y6, y8} := by decide
theorem occ1_bot_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 4 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_4 : S1.filter (fun x => x (4 : Fin 6) = true) = {z1, z8} := by decide
theorem occ1_top_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 4 = Complex.normSq (d z1) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_4]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil1_bot_5 : S0.filter (fun x => x (5 : Fin 6) = true) = {y1, y2, y3, y4, y5, y6, y7} := by decide
theorem occ1_bot_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 5 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_5 : S1.filter (fun x => x (5 : Fin 6) = true) = {z0, z8} := by decide
theorem occ1_top_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 5 = Complex.normSq (d z0) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## Pair occupation rows -/
theorem fil2_bot_0_1 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (1 : Fin 6) = true) = {y6, y7, y8} := by decide
theorem occ2_bot_0_1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 1 = Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_1 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (1 : Fin 6) = true) = {z7, z8} := by decide
theorem occ2_top_0_1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 1 = Complex.normSq (d z7) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_1]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_0_2 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {y5, y7, y8} := by decide
theorem occ2_bot_0_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 2 = Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_2 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {z6, z8} := by decide
theorem occ2_top_0_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 2 = Complex.normSq (d z6) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_0_3 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y4, y7, y8} := by decide
theorem occ2_bot_0_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 3 = Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_3 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z5, z8} := by decide
theorem occ2_top_0_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 3 = Complex.normSq (d z5) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_0_4 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y4, y5, y6, y8} := by decide
theorem occ2_bot_0_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 4 = Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_4 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_0_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 4 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_4]
  rw [Finset.sum_singleton]

theorem fil2_bot_0_5 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y4, y5, y6, y7} := by decide
theorem occ2_bot_0_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 5 = Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_5 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_0_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 5 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_5]
  rw [Finset.sum_singleton]

theorem fil2_bot_1_2 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {y3, y7, y8} := by decide
theorem occ2_bot_1_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 2 = Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_2 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {z4, z8} := by decide
theorem occ2_top_1_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 2 = Complex.normSq (d z4) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_2]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_1_3 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y2, y7, y8} := by decide
theorem occ2_bot_1_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 3 = Complex.normSq (c y2) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_3 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z3, z8} := by decide
theorem occ2_top_1_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 3 = Complex.normSq (d z3) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_1_4 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y2, y3, y6, y8} := by decide
theorem occ2_bot_1_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 4 = Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_4 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_1_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 4 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_4]
  rw [Finset.sum_singleton]

theorem fil2_bot_1_5 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y2, y3, y6, y7} := by decide
theorem occ2_bot_1_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 5 = Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_5 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_1_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 5 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_5]
  rw [Finset.sum_singleton]

theorem fil2_bot_2_3 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y1, y7, y8} := by decide
theorem occ2_bot_2_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 3 = Complex.normSq (c y1) + Complex.normSq (c y7) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_3 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z2, z8} := by decide
theorem occ2_top_2_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 3 = Complex.normSq (d z2) + Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_3]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_2_4 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y1, y3, y5, y8} := by decide
theorem occ2_bot_2_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 4 = Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_4 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_2_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 4 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_4]
  rw [Finset.sum_singleton]

theorem fil2_bot_2_5 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y1, y3, y5, y7} := by decide
theorem occ2_bot_2_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 5 = Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_5 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_2_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 5 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_5]
  rw [Finset.sum_singleton]

theorem fil2_bot_3_4 : S0.filter (fun x => x (3 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y1, y2, y4, y8} := by decide
theorem occ2_bot_3_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 3 4 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_3_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_3_4 : S1.filter (fun x => x (3 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_3_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 3 4 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_3_4]
  rw [Finset.sum_singleton]

theorem fil2_bot_3_5 : S0.filter (fun x => x (3 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y1, y2, y4, y7} := by decide
theorem occ2_bot_3_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 3 5 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_3_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_3_5 : S1.filter (fun x => x (3 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_3_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 3 5 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_3_5]
  rw [Finset.sum_singleton]

theorem fil2_bot_4_5 : S0.filter (fun x => x (4 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y1, y2, y3, y4, y5, y6} := by decide
theorem occ2_bot_4_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 4 5 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_4_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_4_5 : S1.filter (fun x => x (4 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8} := by decide
theorem occ2_top_4_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 4 5 = Complex.normSq (d z8) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_4_5]
  rw [Finset.sum_singleton]

/-! ## The moment system, derived -/

/-- Every row of `MomentSystem` holds for a genuine distance-3 code on these
two fibers. -/
theorem moments (c d : SS.BitString 6 -> ℂ)
    (hcode : SixQubit.MaskBridge.IsCode S0 S1 c d) :
    MomentSystem
      (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8))
      (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) := by
  refine ⟨?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mass_bot c]; exact hcode.mass0_eq_one
  · rw [← mass_top d]; exact hcode.mass1_eq_one
  · rw [← occ1_bot_0 c, ← occ1_top_0 d]; exact hcode.occ1_eq 0
  · rw [← occ1_bot_1 c, ← occ1_top_1 d]; exact hcode.occ1_eq 1
  · rw [← occ1_bot_2 c, ← occ1_top_2 d]; exact hcode.occ1_eq 2
  · rw [← occ1_bot_3 c, ← occ1_top_3 d]; exact hcode.occ1_eq 3
  · rw [← occ1_bot_4 c, ← occ1_top_4 d]; exact hcode.occ1_eq 4
  · rw [← occ1_bot_5 c, ← occ1_top_5 d]; exact hcode.occ1_eq 5
  · rw [← occ2_bot_0_1 c, ← occ2_top_0_1 d]; exact hcode.occ2_eq 0 1
  · rw [← occ2_bot_0_2 c, ← occ2_top_0_2 d]; exact hcode.occ2_eq 0 2
  · rw [← occ2_bot_0_3 c, ← occ2_top_0_3 d]; exact hcode.occ2_eq 0 3
  · rw [← occ2_bot_0_4 c, ← occ2_top_0_4 d]; exact hcode.occ2_eq 0 4
  · rw [← occ2_bot_0_5 c, ← occ2_top_0_5 d]; exact hcode.occ2_eq 0 5
  · rw [← occ2_bot_1_2 c, ← occ2_top_1_2 d]; exact hcode.occ2_eq 1 2
  · rw [← occ2_bot_1_3 c, ← occ2_top_1_3 d]; exact hcode.occ2_eq 1 3
  · rw [← occ2_bot_1_4 c, ← occ2_top_1_4 d]; exact hcode.occ2_eq 1 4
  · rw [← occ2_bot_1_5 c, ← occ2_top_1_5 d]; exact hcode.occ2_eq 1 5
  · rw [← occ2_bot_2_3 c, ← occ2_top_2_3 d]; exact hcode.occ2_eq 2 3
  · rw [← occ2_bot_2_4 c, ← occ2_top_2_4 d]; exact hcode.occ2_eq 2 4
  · rw [← occ2_bot_2_5 c, ← occ2_top_2_5 d]; exact hcode.occ2_eq 2 5
  · rw [← occ2_bot_3_4 c, ← occ2_top_3_4 d]; exact hcode.occ2_eq 3 4
  · rw [← occ2_bot_3_5 c, ← occ2_top_3_5 d]; exact hcode.occ2_eq 3 5
  · rw [← occ2_bot_4_5 c, ← occ2_top_4_5 d]; exact hcode.occ2_eq 4 5
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _

/-! ## The hypothesis-free no-go -/

/-- **Orbit 47 admits no code.**  There is no pair of unit vectors supported on
the two residue fibers whose span has distance `≥ 3`.  Compare
`no_go_of_moments`, which assumes the Knill--Laflamme rows; here they are
derived from `SS.HasDistance`. -/
theorem no_code (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1)
    (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    False := by
  have hcode : SixQubit.MaskBridge.IsCode S0 S1 c d := ⟨hc, hd, hnc, hnd, hdist⟩
  refine no_go_of_moments c d (moments c d hcode) ?_ ?_
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef w0 wt_ef_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef w1 wt_ef_w1

end

end SixQubit.Orbit47
