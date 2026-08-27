import Mathlib
import SS.Basic
import SS.Pauli
import MainTheory.Gate

/-!
# The normalizations of the two-fiber theorem

Theorem 2.6 of `main.tex` reaches its normal form by three moves: conjugating by
a local `X` string so that a supported string becomes `0^n`; observing that the
logical order `m` divides the physical order `q`; and replacing the generator by
a coprime power so that the residue gap becomes exactly `q / m`.  This file
supplies all three.

The first is the identity `weight_bxor` below, and it is also the source of the
Boolean-cube equivalence the six-qubit classification quotients by: flipping the
bits of `x0` negates exactly the angles `a_j` with `x0_j = 1` and shifts every
residue by the constant `A_a(x0)`.  The paper states this in words; here it is
an equation.

For the third, `main.tex` spends a paragraph building a unit of `Z_q` congruent
to the inverse of `c` modulo `m`, prime by prime and then by the Chinese
remainder theorem.  Mathlib's `ZMod.unitsMap_surjective` is that statement, so
the proof below is three lines.
-/

namespace MainTheory.Normalize

open SS

variable {n q : ℕ} [NeZero q]

/-! ## Local `X` conjugation -/

/-- The angle vector after conjugating by the `X` string `x0`: the angles at the
flipped coordinates change sign. -/
def flip (a : Fin n → ZMod q) (x0 : BitString n) : Fin n → ZMod q :=
  fun j => if x0 j then -a j else a j

omit [NeZero q] in
@[simp] theorem flip_flip (a : Fin n → ZMod q) (x0 : BitString n) :
    flip (flip a x0) x0 = a := by
  funext j
  by_cases h : x0 j = true
  · simp [flip, h]
  · simp [flip, h]

omit [NeZero q] in
/-- **Conjugating by `X^{x0}` flips signs and shifts the residue.**

This is the exact form of the sentence in `main.tex` that a local `X`
normalization "changes selected signs and a common scalar only". -/
theorem weight_bxor (a : Fin n → ZMod q) (x0 s : BitString n) :
    SS.weight a (SS.bxor s x0) = SS.weight (flip a x0) s + SS.weight a x0 := by
  rw [SS.weight, SS.weight, SS.weight, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hx : x0 j = true
  · cases hs : s j
    · simp [flip, hx, hs, SS.bit]
    · simp [flip, hx, hs, SS.bit]
  · simp only [Bool.not_eq_true] at hx
    simp [flip, hx, SS.bit]

omit [NeZero q] in
/-- In particular the flipped angle vector negates the residue of `x0` itself,
which is what puts the conjugated word at residue zero. -/
theorem weight_flip_self (a : Fin n → ZMod q) (x0 : BitString n) :
    SS.weight (flip a x0) x0 = - SS.weight a x0 := by
  rw [SS.weight, SS.weight, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hx : x0 j = true
  · simp [flip, hx]
  · simp only [Bool.not_eq_true] at hx
    simp [flip, hx]

/-! ## The logical order divides the physical order -/

omit [NeZero q] in
/-- `main.tex` eq. 2.28: the residue gap has additive order `m` in `Z_q`, and
every additive order divides `q`. -/
theorem addOrderOf_dvd (delta : ZMod q) : addOrderOf delta ∣ q := by
  have : addOrderOf delta ∣ Nat.card (ZMod q) := addOrderOf_dvd_natCard delta
  simpa [Nat.card_eq_fintype_card, ZMod.card] using this

/-! ## Replacing the generator by a coprime power -/

/-- **The unit-lifting step.**

Given `m | q` and a unit `c` of `Z_m`, there is a unit `u` of `Z_q` whose
reduction inverts `c`.  `main.tex` proves this prime by prime and recombines by
CRT; `ZMod.unitsMap_surjective` is exactly the statement. -/
theorem exists_unit_reduction_inv {m : ℕ} (hmq : m ∣ q) (cu : (ZMod m)ˣ) :
    ∃ u : (ZMod q)ˣ, ZMod.unitsMap hmq u = cu⁻¹ := by
  obtain ⟨ u, hu ⟩ := ZMod.unitsMap_surjective (n := m) (m := q) hmq cu⁻¹
  exact ⟨ u, hu ⟩

/-- The same conclusion as a congruence, which is the form Theorem 2.6 uses. -/
theorem exists_unit_mul_eq_one {m : ℕ} (hmq : m ∣ q) (cu : (ZMod m)ˣ) :
    ∃ u : (ZMod q)ˣ,
      (ZMod.castHom hmq (ZMod m)) (u : ZMod q) * (cu : ZMod m) = 1 := by
  obtain ⟨ u, hu ⟩ := exists_unit_reduction_inv hmq cu
  refine ⟨ u, ?_ ⟩
  have : ((ZMod.unitsMap hmq u : (ZMod m)ˣ) : ZMod m) = ((cu⁻¹ : (ZMod m)ˣ) : ZMod m) := by
    rw [hu]
  rw [ZMod.unitsMap_def] at this
  simp only [Units.coe_map, MonoidHom.coe_coe] at this
  rw [this]
  exact Units.inv_mul cu

/-! ## The state-level consequence, and an independent check -/

omit [NeZero q] in
/-- **Conjugating a logical word by `X^{x0}`.**

A word supported in the residue-`r` fiber of `a` is carried to one supported in
the residue-`r - A_a(x0)` fiber of the flipped vector.  Choosing `x0` in the
support therefore moves that support to residue zero, which is the normalization
Theorem 2.6 opens with. -/
theorem ssCondition_bxor (a : Fin n → ZMod q) (x0 : BitString n) (r : ZMod q)
    (c : SS.State n ℂ) (h : SS.SSConditionState a r c) :
    SS.SSConditionState (flip a x0) (r - SS.weight a x0)
      (fun s => c (SS.bxor s x0)) := by
  intro s hs
  have hw := h _ hs
  rw [weight_bxor] at hw
  linear_combination hw

/-- Orbit 21's angle vector, used below as an independent check. -/
def a21 : Fin 6 → ZMod 4 := ![1, 1, 1, 2, 2, 3]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- The flip identity, re-checked by the kernel on all 4096 pairs for a concrete
angle vector.  `weight_bxor` is the kind of identity where a sign error in
`flip` and a matching error in the shift would cancel and still typecheck; this
rules that out arithmetically. -/
theorem weight_bxor_check :
    ∀ x0 s : BitString 6,
      SS.weight a21 (SS.bxor s x0) = SS.weight (flip a21 x0) s + SS.weight a21 x0 := by
  decide

end MainTheory.Normalize
