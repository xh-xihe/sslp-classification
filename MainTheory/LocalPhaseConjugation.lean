import MainTheory.ClassificationLevels
import MainTheory.IntrinsicClassBridge

/-!
# Local `X` conjugation on local phases

The normalization standing between the bounded outer record and the original
code is a local `X` conjugation: `D3NormalizedFreshPhase.normalizedState` is
literally `fun s => vec k (SS.bxor s x0)`.  This file works out what that
conjugation does to a local diagonal phase, which is the step the transport
machinery does not currently take -- it moves codes, gates and records, but
never the intrinsic quotient group.

The computation is elementary.  Reading the product for `diagonalValue u` at
`s + x0` and splitting on `x0 j`,

    prod_j [ (s+x0)_j ] u_j  =  ( prod_{x0 j} u_j ) * prod_j [ s_j ] (flip u x0)_j

where `flip u x0` inverts exactly the sites `x0` flips.  The leading factor does
not depend on `s`, so it is a global scalar -- and the intrinsic group is the
quotient by exactly the scalar actions.  Conjugation therefore descends to the
quotient, which is what makes the bounded record transportable.
-/

namespace MainTheory.LocalPhaseConjugation

open MainTheory.ClassificationLevels

variable {n : ℕ}

/-- Coercion of the group inverse in `unitary ℂ`. -/
theorem coe_mul_coe_inv (z : unitary ℂ) : (z : ℂ) * ((z⁻¹ : unitary ℂ) : ℂ) = 1 := by
  rw [show (z⁻¹ : unitary ℂ) = star z from rfl]
  exact Unitary.coe_mul_star_self z

/-- The local phase after conjugating by the `X` string `x0`: the flipped sites
carry the inverse phase. -/
def flipPhase (u : LocalPhase n) (x0 : SS.BitString n) : LocalPhase n :=
  fun j => if x0 j then (u j)⁻¹ else u j

/-- The scalar picked up by the conjugation: the product over the flipped
sites. -/
def flipScalar (u : LocalPhase n) (x0 : SS.BitString n) : ℂ :=
  ∏ j, if x0 j then ((u j : ℂ)) else 1

@[simp] theorem flipPhase_flipPhase (u : LocalPhase n) (x0 : SS.BitString n) :
    flipPhase (flipPhase u x0) x0 = u := by
  funext j
  by_cases h : x0 j
  · simp [flipPhase, h]
  · simp [flipPhase, h]

/-- **The conjugation identity.**

Evaluating a local phase at `s + x0` is the same as evaluating the flipped phase
at `s`, up to a scalar that does not depend on `s`. -/
theorem diagonalValue_bxor (u : LocalPhase n) (x0 s : SS.BitString n) :
    diagonalValue u (SS.bxor s x0)
      = flipScalar u x0 * diagonalValue (flipPhase u x0) s := by
  rw [diagonalValue, flipScalar, diagonalValue, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hx : x0 j
  · by_cases hs : s j
    · simp [hx, hs, flipPhase, SS.bxor, coe_mul_coe_inv]
    · simp [hx, hs, SS.bxor]
  · by_cases hs : s j
    · simp [hx, hs, flipPhase, SS.bxor]
    · simp [hx, hs, SS.bxor]

/-- The scalar is never zero, being a product of unit-modulus numbers. -/
theorem flipScalar_ne_zero (u : LocalPhase n) (x0 : SS.BitString n) :
    flipScalar u x0 ≠ 0 := by
  rw [flipScalar]
  refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
  by_cases h : x0 j
  · simp only [h, if_true]
    exact Units.ne_zero (Unitary.toUnits (u j))
  · simp [h]

end MainTheory.LocalPhaseConjugation
