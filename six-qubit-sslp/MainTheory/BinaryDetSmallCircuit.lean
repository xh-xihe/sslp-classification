import MainTheory.BinaryDetLastRow
import MainTheory.BinaryDetCircuit

/-!
# Shallow determinant circuits for the size-four and size-five leaves

`Matrix.det` is the semantic definition, but reducing its generic permutation
sum directly makes even one closed five-by-five prefix exceed the default
elaborator recursion depth.  The already proved `splitLaplace_eq_det` theorem
lets numerical leaves use a two-row expansion ending in explicit `2 × 2` or
`3 × 3` determinants, while this module transports the result back to the
semantic `ReducedAtRow` predicate.
-/

namespace MainTheory.BinaryDetSmallCircuit

open scoped BigOperators
open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetLastRow

/-- Cofactor evaluation through a shallow Laplace circuit. -/
def circuitCoefficient (fuel n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) : ℤ :=
  splitLaplace
    ((zeroRowMatrix M i).updateRow i (integerBasisRow j))
    fuel n id id

theorem circuitCoefficient_eq_coefficient
    (fuel n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    circuitCoefficient fuel n M i j = coefficient M i j := by
  unfold circuitCoefficient coefficient
  exact splitLaplace_eq_det _ fuel n id id

def circuitNegativeSum (fuel n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ :=
  ∑ j : Fin n, min (circuitCoefficient fuel n M i j) 0

def circuitPositiveSum (fuel n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ :=
  ∑ j : Fin n, max (circuitCoefficient fuel n M i j) 0

/-- Closed numerical predicate used by generated small-size leaves. -/
def CircuitReducedAtRow (fuel n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (B : ℕ) : Prop :=
  (-(B : ℤ) ≤ circuitNegativeSum fuel n M i) ∧
    (circuitPositiveSum fuel n M i ≤ (B : ℤ))

instance (fuel n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin n) (B : ℕ) :
    Decidable (CircuitReducedAtRow fuel n M i B) := by
  unfold CircuitReducedAtRow
  infer_instance

/-- The shallow circuit is only a computational presentation; its checked
bound is the semantic generic last-row bound. -/
theorem CircuitReducedAtRow.toReducedAtRow
    {fuel n B : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {i : Fin n}
    (h : CircuitReducedAtRow fuel n M i B) : ReducedAtRow M i B := by
  unfold CircuitReducedAtRow circuitNegativeSum circuitPositiveSum at h
  unfold ReducedAtRow negativeCoefficientSum positiveCoefficientSum
  simpa only [circuitCoefficient_eq_coefficient] using h

end MainTheory.BinaryDetSmallCircuit
