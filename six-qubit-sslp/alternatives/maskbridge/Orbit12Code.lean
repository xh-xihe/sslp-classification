import Mathlib

import SixQubit.MaskBridge
import SixQubit.Orbit12

/-!
# Orbit 12: no code, not merely no solution

`SixQubit.Orbit12.no_go_of_moments` takes twenty off-diagonal Walsh rows, four
diagonal rows and a `MomentSystem` as hypotheses.  This module discharges all of
them from `SS.HasDistance ![c, d] 3` via `SixQubit.MaskBridge`, and records the
hypothesis-free statement `no_code`.

Orbit 12 exercises the diagonal half of the bridge as well as the off-diagonal
half: the four `diagBot _ efA _ = diagTop _ efA _` rows come from the *equal
scalars* in the Knill--Laflamme condition at `j = k`, and the twenty-three
moment rows come from the pure-`Z` Paulis after the character-to-occupation
change of basis.

Every Pauli instantiated below is checked in Lean to have weight `≤ 2`.

No `sorry`, no `native_decide`.
-/

namespace SixQubit.Orbit12

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-! ## The orbit's Walsh sums are the generic ones -/

theorem offSum_eq_offSumG (c d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) :
    offSum c d e z = SixQubit.MaskBridge.offSumG S0 S1 c d e z := rfl

theorem diagBot_eq_diagBotG (c : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) :
    diagBot c e z = SixQubit.MaskBridge.diagBotG S0 c e z := rfl

theorem diagTop_eq_diagTopG (d : SS.BitString 6 -> ℂ) (e z : SS.BitString 6) :
    diagTop d e z = SixQubit.MaskBridge.diagTopG S1 d e z := rfl

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

/-! ## Every Pauli instantiated has weight at most two -/

theorem wt_ef0_w0 : (SS.PauliString.mk ef0 w0).wt ≤ 2 := by decide
theorem wt_ef0_w1 : (SS.PauliString.mk ef0 w1).wt ≤ 2 := by decide
theorem wt_ef0_w5 : (SS.PauliString.mk ef0 w5).wt ≤ 2 := by decide
theorem wt_ef0_w6 : (SS.PauliString.mk ef0 w6).wt ≤ 2 := by decide
theorem wt_ef1_w0 : (SS.PauliString.mk ef1 w0).wt ≤ 2 := by decide
theorem wt_ef1_w1 : (SS.PauliString.mk ef1 w1).wt ≤ 2 := by decide
theorem wt_ef1_w5 : (SS.PauliString.mk ef1 w5).wt ≤ 2 := by decide
theorem wt_ef1_w6 : (SS.PauliString.mk ef1 w6).wt ≤ 2 := by decide
theorem wt_ef2_w0 : (SS.PauliString.mk ef2 w0).wt ≤ 2 := by decide
theorem wt_ef2_w4 : (SS.PauliString.mk ef2 w4).wt ≤ 2 := by decide
theorem wt_ef3_w0 : (SS.PauliString.mk ef3 w0).wt ≤ 2 := by decide
theorem wt_ef3_w2 : (SS.PauliString.mk ef3 w2).wt ≤ 2 := by decide
theorem wt_ef4_w0 : (SS.PauliString.mk ef4 w0).wt ≤ 2 := by decide
theorem wt_ef4_w3 : (SS.PauliString.mk ef4 w3).wt ≤ 2 := by decide
theorem wt_ef5_w0 : (SS.PauliString.mk ef5 w0).wt ≤ 2 := by decide
theorem wt_ef5_w2 : (SS.PauliString.mk ef5 w2).wt ≤ 2 := by decide
theorem wt_ef6_w0 : (SS.PauliString.mk ef6 w0).wt ≤ 2 := by decide
theorem wt_ef6_w2 : (SS.PauliString.mk ef6 w2).wt ≤ 2 := by decide
theorem wt_ef7_w0 : (SS.PauliString.mk ef7 w0).wt ≤ 2 := by decide
theorem wt_ef7_w3 : (SS.PauliString.mk ef7 w3).wt ≤ 2 := by decide
theorem wt_efA_w0 : (SS.PauliString.mk efA w0).wt ≤ 2 := by decide
theorem wt_efA_w1 : (SS.PauliString.mk efA w1).wt ≤ 2 := by decide
theorem wt_efA_w5 : (SS.PauliString.mk efA w5).wt ≤ 2 := by decide
theorem wt_efA_w6 : (SS.PauliString.mk efA w6).wt ≤ 2 := by decide

/-! ## Total mass -/
theorem mass_bot (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.mass S0 c
      = Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.mass S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem mass_top (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.mass S1 d
      = Complex.normSq (d z0) + Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) + Complex.normSq (d z12) + Complex.normSq (d z13) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.mass S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ## Single-qubit occupation rows -/
theorem fil1_bot_0 : S0.filter (fun x => x (0 : Fin 6) = true) = {y8, y9, y10, y11, y12, y13, y14, y15} := by decide
theorem occ1_bot_0 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 0 = Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_0 : S1.filter (fun x => x (0 : Fin 6) = true) = {z8, z9, z10, z11, z12, z13, z14, z15} := by decide
theorem occ1_top_0 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 0 = Complex.normSq (d z8) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z11) + Complex.normSq (d z12) + Complex.normSq (d z13) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_1 : S0.filter (fun x => x (1 : Fin 6) = true) = {y4, y5, y6, y7, y12, y13, y14, y15} := by decide
theorem occ1_bot_1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 1 = Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_1 : S1.filter (fun x => x (1 : Fin 6) = true) = {z4, z5, z6, z7, z12, z13, z14, z15} := by decide
theorem occ1_top_1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 1 = Complex.normSq (d z4) + Complex.normSq (d z5) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z12) + Complex.normSq (d z13) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_2 : S0.filter (fun x => x (2 : Fin 6) = true) = {y2, y3, y6, y7, y10, y11, y14, y15} := by decide
theorem occ1_bot_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 2 = Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_2 : S1.filter (fun x => x (2 : Fin 6) = true) = {z2, z3, z6, z7, z10, z11, z14, z15} := by decide
theorem occ1_top_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 2 = Complex.normSq (d z2) + Complex.normSq (d z3) + Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z10) + Complex.normSq (d z11) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_3 : S0.filter (fun x => x (3 : Fin 6) = true) = {y1, y3, y5, y7, y9, y11, y13, y15} := by decide
theorem occ1_bot_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 3 = Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y11) + Complex.normSq (c y13) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_3 : S1.filter (fun x => x (3 : Fin 6) = true) = {z1, z3, z5, z7, z9, z11, z13, z15} := by decide
theorem occ1_top_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 3 = Complex.normSq (d z1) + Complex.normSq (d z3) + Complex.normSq (d z5) + Complex.normSq (d z7) + Complex.normSq (d z9) + Complex.normSq (d z11) + Complex.normSq (d z13) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_4 : S0.filter (fun x => x (4 : Fin 6) = true) = {y1, y2, y4, y7, y9, y10, y12, y15} := by decide
theorem occ1_bot_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 4 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y12) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_4 : S1.filter (fun x => x (4 : Fin 6) = true) = {z1, z2, z4, z7, z9, z10, z12, z15} := by decide
theorem occ1_top_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 4 = Complex.normSq (d z1) + Complex.normSq (d z2) + Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z12) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil1_bot_5 : S0.filter (fun x => x (5 : Fin 6) = true) = {y1, y2, y3, y4, y5, y6, y9, y10, y11, y12, y13, y14} := by decide
theorem occ1_bot_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S0 c 5 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_bot_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil1_top_5 : S1.filter (fun x => x (5 : Fin 6) = true) = {z0, z7, z8, z15} := by decide
theorem occ1_top_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ1 S1 d 5 = Complex.normSq (d z0) + Complex.normSq (d z7) + Complex.normSq (d z8) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ1
  rw [fil1_top_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ## Pair occupation rows -/
theorem fil2_bot_0_1 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (1 : Fin 6) = true) = {y12, y13, y14, y15} := by decide
theorem occ2_bot_0_1 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 1 = Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_1 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (1 : Fin 6) = true) = {z12, z13, z14, z15} := by decide
theorem occ2_top_0_1 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 1 = Complex.normSq (d z12) + Complex.normSq (d z13) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_0_2 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {y10, y11, y14, y15} := by decide
theorem occ2_bot_0_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 2 = Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_2 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {z10, z11, z14, z15} := by decide
theorem occ2_top_0_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 2 = Complex.normSq (d z10) + Complex.normSq (d z11) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_0_3 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y9, y11, y13, y15} := by decide
theorem occ2_bot_0_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 3 = Complex.normSq (c y9) + Complex.normSq (c y11) + Complex.normSq (c y13) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_3 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z9, z11, z13, z15} := by decide
theorem occ2_top_0_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 3 = Complex.normSq (d z9) + Complex.normSq (d z11) + Complex.normSq (d z13) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_0_4 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y9, y10, y12, y15} := by decide
theorem occ2_bot_0_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 4 = Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y12) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_4 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z9, z10, z12, z15} := by decide
theorem occ2_top_0_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 4 = Complex.normSq (d z9) + Complex.normSq (d z10) + Complex.normSq (d z12) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_0_5 : S0.filter (fun x => x (0 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y9, y10, y11, y12, y13, y14} := by decide
theorem occ2_bot_0_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 0 5 = Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_0_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_0_5 : S1.filter (fun x => x (0 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z8, z15} := by decide
theorem occ2_top_0_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 0 5 = Complex.normSq (d z8) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_0_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_1_2 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {y6, y7, y14, y15} := by decide
theorem occ2_bot_1_2 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 2 = Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y14) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_2 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (2 : Fin 6) = true) = {z6, z7, z14, z15} := by decide
theorem occ2_top_1_2 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 2 = Complex.normSq (d z6) + Complex.normSq (d z7) + Complex.normSq (d z14) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_1_3 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y5, y7, y13, y15} := by decide
theorem occ2_bot_1_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 3 = Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y13) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_3 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z5, z7, z13, z15} := by decide
theorem occ2_top_1_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 3 = Complex.normSq (d z5) + Complex.normSq (d z7) + Complex.normSq (d z13) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_1_4 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y4, y7, y12, y15} := by decide
theorem occ2_bot_1_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 4 = Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y12) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_4 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z4, z7, z12, z15} := by decide
theorem occ2_top_1_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 4 = Complex.normSq (d z4) + Complex.normSq (d z7) + Complex.normSq (d z12) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_1_5 : S0.filter (fun x => x (1 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y4, y5, y6, y12, y13, y14} := by decide
theorem occ2_bot_1_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 1 5 = Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_1_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_1_5 : S1.filter (fun x => x (1 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z7, z15} := by decide
theorem occ2_top_1_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 1 5 = Complex.normSq (d z7) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_1_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_2_3 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {y3, y7, y11, y15} := by decide
theorem occ2_bot_2_3 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 3 = Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y11) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_3 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (3 : Fin 6) = true) = {z3, z7, z11, z15} := by decide
theorem occ2_top_2_3 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 3 = Complex.normSq (d z3) + Complex.normSq (d z7) + Complex.normSq (d z11) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_2_4 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y2, y7, y10, y15} := by decide
theorem occ2_bot_2_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 4 = Complex.normSq (c y2) + Complex.normSq (c y7) + Complex.normSq (c y10) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_4 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z2, z7, z10, z15} := by decide
theorem occ2_top_2_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 4 = Complex.normSq (d z2) + Complex.normSq (d z7) + Complex.normSq (d z10) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_2_5 : S0.filter (fun x => x (2 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y2, y3, y6, y10, y11, y14} := by decide
theorem occ2_bot_2_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 2 5 = Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y14) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_2_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_2_5 : S1.filter (fun x => x (2 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z7, z15} := by decide
theorem occ2_top_2_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 2 5 = Complex.normSq (d z7) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_2_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_3_4 : S0.filter (fun x => x (3 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {y1, y7, y9, y15} := by decide
theorem occ2_bot_3_4 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 3 4 = Complex.normSq (c y1) + Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_3_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_3_4 : S1.filter (fun x => x (3 : Fin 6) = true ∧ x (4 : Fin 6) = true) = {z1, z7, z9, z15} := by decide
theorem occ2_top_3_4 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 3 4 = Complex.normSq (d z1) + Complex.normSq (d z7) + Complex.normSq (d z9) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_3_4]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem fil2_bot_3_5 : S0.filter (fun x => x (3 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y1, y3, y5, y9, y11, y13} := by decide
theorem occ2_bot_3_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 3 5 = Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y9) + Complex.normSq (c y11) + Complex.normSq (c y13) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_3_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_3_5 : S1.filter (fun x => x (3 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z7, z15} := by decide
theorem occ2_top_3_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 3 5 = Complex.normSq (d z7) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_3_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem fil2_bot_4_5 : S0.filter (fun x => x (4 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {y1, y2, y4, y9, y10, y12} := by decide
theorem occ2_bot_4_5 (c : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S0 c 4 5 = Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y12) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_bot_4_5]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem fil2_top_4_5 : S1.filter (fun x => x (4 : Fin 6) = true ∧ x (5 : Fin 6) = true) = {z7, z15} := by decide
theorem occ2_top_4_5 (d : SS.BitString 6 -> ℂ) :
    SixQubit.MaskBridge.occ2 S1 d 4 5 = Complex.normSq (d z7) + Complex.normSq (d z15) := by
  unfold SixQubit.MaskBridge.occ2
  rw [fil2_top_4_5]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## The moment system, derived -/

theorem moments (c d : SS.BitString 6 -> ℂ)
    (hcode : SixQubit.MaskBridge.IsCode S0 S1 c d) :
    MomentSystem
      (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
      (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)) := by
  refine ⟨?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- **Orbit 12 admits no code.**  There is no pair of unit vectors supported on
the two residue fibers whose span has distance `≥ 3`. -/
theorem no_code (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0)
    (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1)
    (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    False := by
  have hcode : SixQubit.MaskBridge.IsCode S0 S1 c d := ⟨hc, hd, hnc, hnd, hdist⟩
  refine no_go_of_moments c d (moments c d hcode)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef0 w0 wt_ef0_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef0 w1 wt_ef0_w1
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef0 w5 wt_ef0_w5
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef0 w6 wt_ef0_w6
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef1 w0 wt_ef1_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef1 w1 wt_ef1_w1
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef1 w5 wt_ef1_w5
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef1 w6 wt_ef1_w6
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef2 w0 wt_ef2_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef2 w4 wt_ef2_w4
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef3 w0 wt_ef3_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef3 w2 wt_ef3_w2
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef4 w0 wt_ef4_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef4 w3 wt_ef4_w3
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef5 w0 wt_ef5_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef5 w2 wt_ef5_w2
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef6 w0 wt_ef6_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef6 w2 wt_ef6_w2
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef7 w0 wt_ef7_w0
  · rw [offSum_eq_offSumG]
    exact hcode.offSumG_eq_zero ef7 w3 wt_ef7_w3
  · rw [diagBot_eq_diagBotG, diagTop_eq_diagTopG]
    exact hcode.diagBotG_eq_diagTopG efA w0 wt_efA_w0
  · rw [diagBot_eq_diagBotG, diagTop_eq_diagTopG]
    exact hcode.diagBotG_eq_diagTopG efA w1 wt_efA_w1
  · rw [diagBot_eq_diagBotG, diagTop_eq_diagTopG]
    exact hcode.diagBotG_eq_diagTopG efA w5 wt_efA_w5
  · rw [diagBot_eq_diagBotG, diagTop_eq_diagTopG]
    exact hcode.diagBotG_eq_diagTopG efA w6 wt_efA_w6

end

end SixQubit.Orbit12
