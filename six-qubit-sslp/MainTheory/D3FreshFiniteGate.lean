import MainTheory.D3FreshSparseAssembly

/-!
# The finite gate carried by a fresh sparse rational phase

`D3FreshSparseAssembly` constructs a rational phase and bounds its own least
denominator.  This file starts the separate analytic/algebraic packaging step:
use the standard primitive root at that denominator and identify its modular
coordinate phases with the real exponential phases of the rational vector.
-/

namespace MainTheory.D3FreshFiniteGate

open MainTheory
open scoped BigOperators

noncomputable section

/-- Standard primitive root at the fresh least denominator. -/
def standardRoot {n r : ℕ} (P : D3SparseRationalization.Data n r) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I / (P.order : ℂ))

theorem standardRoot_primitive {n r : ℕ}
    (P : D3SparseRationalization.Data n r) :
    IsPrimitiveRoot (standardRoot P) P.order := by
  exact Complex.isPrimitiveRoot_exp P.order P.order_pos.ne'

/-- Reduction of an integral numerator modulo the fresh order does not change
the corresponding power of the standard root.  The integer numerator may be
negative; the proof therefore uses `zpow` and Euclidean remainder rather than
silently coercing it to a natural number. -/
theorem standardRoot_pow_angle_val_eq_zpow_numerator {n r : ℕ}
    (P : D3SparseRationalization.Data n r) (j : Fin n) :
    standardRoot P ^ (P.angle j).val =
      standardRoot P ^ (P.numerator j : ℤ) := by
  letI : NeZero P.order := ⟨P.order_pos.ne'⟩
  rw [← zpow_natCast]
  change standardRoot P ^ (((P.numerator j : ZMod P.order).val : ℕ) : ℤ) =
    standardRoot P ^ P.numerator j
  rw [ZMod.val_intCast]
  have hroot : standardRoot P ≠ 0 := by
    simp [standardRoot]
  symm
  calc
    standardRoot P ^ P.numerator j =
        standardRoot P ^
          (P.numerator j % (P.order : ℤ) +
            (P.order : ℤ) * (P.numerator j / (P.order : ℤ))) := by
      rw [Int.emod_add_mul_ediv]
    _ = standardRoot P ^ (P.numerator j % (P.order : ℤ)) *
          standardRoot P ^
            ((P.order : ℤ) * (P.numerator j / (P.order : ℤ))) := by
      rw [zpow_add₀ hroot]
    _ = standardRoot P ^ (P.numerator j % (P.order : ℤ)) := by
      rw [zpow_mul, zpow_natCast,
        (standardRoot_primitive P).pow_eq_one, one_zpow, mul_one]

/-- Each modular coordinate phase of the fresh finite gate is exactly the
real exponential phase of the corresponding rational coordinate. -/
theorem standardRoot_pow_angle_val {n r : ℕ}
    (P : D3SparseRationalization.Data n r) (j : Fin n) :
    standardRoot P ^ (P.angle j).val =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (P.fullSolutionReal j : ℂ)) := by
  rw [standardRoot_pow_angle_val_eq_zpow_numerator]
  rw [standardRoot, ← Complex.exp_int_mul]
  apply congrArg Complex.exp
  have hreal : (P.numerator j : ℝ) =
      (P.order : ℝ) * P.fullSolutionReal j := by
    change (P.numerator j : ℝ) =
      (P.order : ℝ) * ((P.fullSolution j : ℚ) : ℝ)
    exact_mod_cast (P.numerator_spec j).symm
  have hcomplex : (P.numerator j : ℂ) =
      (P.order : ℂ) * (P.fullSolutionReal j : ℂ) := by
    exact_mod_cast hreal
  rw [hcomplex]
  have hq : (P.order : ℂ) ≠ 0 := by
    exact_mod_cast P.order_pos.ne'
  field_simp [hq]

end

end MainTheory.D3FreshFiniteGate
