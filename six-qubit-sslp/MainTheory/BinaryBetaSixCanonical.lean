import MainTheory.BinaryBetaSixSemantic

/-!
# List-free canonical endpoint for the six-by-six beta bound

The arithmetic generator naturally ranges over the six coordinates
`0 ≤ a₀ ≤ ... ≤ a₅ < 8`.  Requiring it to look the same tuple up in the
1716-element `weakAngles6` list adds no mathematical information and makes
high-index bridge files needlessly deep.  This module exposes the equivalent
canonical-tuple interface and connects it to the already checked
`AllPatternBottomBound` semantic endpoint.

The list is still used for its proved soundness theorem.  It is never reduced
inside a numerical leaf.
-/

namespace MainTheory.BinaryBetaSixCanonical

open MainTheory.BinaryBeta
open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.BinaryBetaSixSemantic
open MainTheory.OuterCompleteness

/-- A determinant bound for every in-range weakly increasing six-tuple of
three-bit column patterns. -/
def AllCanonicalBottomBound (B : ℕ) : Prop :=
  ∀ p : MainTheory.OuterEnumeration.Angle6,
    IsCanonicalAngle6 8 p →
      BottomDetBound (topOfPattern (R := ℤ) p) B

/-- Canonical-tuple coverage supplies the existing authoritative-list
interface without evaluating any `patternAt` lookup. -/
theorem allPatternBottomBound_of_allCanonical {B : ℕ}
    (h : AllCanonicalBottomBound B) : AllPatternBottomBound B := by
  intro i
  exact h (patternAt i)
    (mem_weakAngles6_implies_canonical (patternAt_mem i))

/-- List-free generated arithmetic implies the universal six-by-six beta
upper bound. -/
theorem betaSixBound_of_allCanonicalBottomBound {B : ℕ}
    (h : AllCanonicalBottomBound B) : BetaBound 6 B :=
  betaSixBound_of_allPatternBottomBound
    (allPatternBottomBound_of_allCanonical h)

end MainTheory.BinaryBetaSixCanonical
