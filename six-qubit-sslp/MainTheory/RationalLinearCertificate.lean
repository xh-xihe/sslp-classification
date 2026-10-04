import Mathlib

/-! # Soundness of exact linear dual certificates

Rational coefficient identities imply real inequalities. The hypotheses name
the actual equality rows, positive rows and variables; realization of those
rows by an encoder is a separate obligation at the call site.
-/

namespace MainTheory.RationalLinearCertificate

noncomputable section

variable {n e p : ℕ}

def evaluate (r : Fin n → ℚ) (y : Fin n → ℝ) : ℝ := ∑ j, (r j : ℝ) * y j

structure Certificate (objective : Fin n → ℚ) (bound : ℚ)
    (equalities : Fin e → Fin n → ℚ) (rhs : Fin e → ℚ)
    (positive : Fin p → Fin n → ℚ) where
  equalityMultiplier : Fin e → ℚ
  positiveMultiplier : Fin p → ℚ
  remainder : Fin n → ℚ
  coefficients : ∀ j, objective j =
    (∑ i, equalityMultiplier i * equalities i j) +
    (∑ i, positiveMultiplier i * positive i j) + remainder j
  constant : bound = ∑ i, equalityMultiplier i * rhs i
  positiveMultiplier_nonneg : ∀ i, 0 ≤ positiveMultiplier i
  remainder_nonneg : ∀ j, 0 ≤ remainder j

theorem Certificate.bound {objective : Fin n → ℚ} {lowerBound : ℚ}
    {equalities : Fin e → Fin n → ℚ} {rhs : Fin e → ℚ}
    {positive : Fin p → Fin n → ℚ}
    (C : Certificate objective lowerBound equalities rhs positive)
    (y : Fin n → ℝ)
    (heq : ∀ i, evaluate (equalities i) y = (rhs i : ℝ))
    (hpos : ∀ i, 0 ≤ evaluate (positive i) y)
    (hy : ∀ j, 0 ≤ y j) :
    (lowerBound : ℝ) ≤ evaluate objective y := by
  have hcoeff (j : Fin n) : (objective j : ℝ) =
      (∑ i, (C.equalityMultiplier i : ℝ) * (equalities i j : ℝ)) +
      (∑ i, (C.positiveMultiplier i : ℝ) * (positive i j : ℝ)) +
      (C.remainder j : ℝ) := by
    exact_mod_cast C.coefficients j
  have hconst : (lowerBound : ℝ) = ∑ i, (C.equalityMultiplier i : ℝ) * (rhs i : ℝ) := by
    exact_mod_cast C.constant
  have expansion : evaluate objective y =
      (∑ i, (C.equalityMultiplier i : ℝ) * evaluate (equalities i) y) +
      (∑ i, (C.positiveMultiplier i : ℝ) * evaluate (positive i) y) +
      evaluate C.remainder y := by
    unfold evaluate
    simp_rw [hcoeff, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    simp only [Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm (f := fun j i => _ * (_ * y j)),
      Finset.sum_comm (f := fun j i => _ * (_ * y j))]
  rw [expansion]
  simp_rw [heq]
  rw [← hconst]
  have hp : 0 ≤ ∑ i, (C.positiveMultiplier i : ℝ) * evaluate (positive i) y :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Rat.cast_nonneg.mpr
      (C.positiveMultiplier_nonneg i)) (hpos i)
  have hr : 0 ≤ evaluate C.remainder y :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Rat.cast_nonneg.mpr
      (C.remainder_nonneg j)) (hy j)
  linarith

end
end MainTheory.RationalLinearCertificate
