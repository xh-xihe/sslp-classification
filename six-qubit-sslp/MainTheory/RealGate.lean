import Mathlib
import SS.Basic
import SS.Pauli
import SS.DiagonalAction
import MainTheory.Rationalize
import MainTheory.Denominator

/-!
# The diagonal gate with real angles

Everything in `MainTheory/Gate.lean` is about `D(a;q)`, the gate already
rationalized.  `main.tex` starts one step earlier, with `D(theta)` for an
arbitrary real angle vector, and Theorem 2.4 is what produces the finite lift
from it.

This file supplies the real gate and the step that makes the rationalization
possible: on the support of an eigenvector, the angle `theta . x` is determined
modulo one.  That is `eq:phase-sector-congruence`, and it is what turns the
physical phase conditions into a linear system with an *integer* right-hand
side -- the system `Ru = h` of `eq:Ru=h`, whose rationalization is
`MainTheory/Rationalize.lean`.

The proof is the only place in this development where an analytic fact is used:
`Complex.exp z = 1` exactly when `z` is an integer multiple of `2 pi i`.
Everything downstream is algebra.
-/

namespace MainTheory.RealGate

open SS

variable {n : ℕ}

/-! ## The real angle and the gate it generates -/

/-- `theta . x`, the physical phase accumulated on the basis string `x`. -/
def angle (theta : Fin n → ℝ) (s : BitString n) : ℝ :=
  ∑ j, theta j * (if s j then 1 else 0)

/-- The diagonal gate `D(theta)`, acting on amplitude vectors. -/
noncomputable def realGate (theta : Fin n → ℝ) (psi : SS.State n ℂ) :
    SS.State n ℂ :=
  fun s => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (angle theta s : ℂ)) * psi s

/-! ## The phase-sector congruence -/

/-- The gate's diagonal entry at a supported string is the eigenvalue. -/
theorem exp_eq_of_eigen (theta : Fin n → ℝ) (c : SS.State n ℂ) (lam : ℂ)
    (h : realGate theta c = fun s => lam * c s)
    (x : BitString n) (hx : c x ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (angle theta x : ℂ)) = lam := by
  have hxv := congrFun h x
  rw [realGate] at hxv
  exact mul_right_cancel₀ hx hxv

/-- **`main.tex` eq. `eq:phase-sector-congruence`.**

Two strings in the support of the same eigenvector have angles differing by an
integer.  This is what gives the system `Ru = h` an integral right-hand side. -/
theorem angle_sub_int_of_eigen (theta : Fin n → ℝ) (c : SS.State n ℂ)
    (lam : ℂ) (h : realGate theta c = fun s => lam * c s)
    (x y : BitString n) (hx : c x ≠ 0) (hy : c y ≠ 0) :
    ∃ k : ℤ, angle theta x - angle theta y = (k : ℝ) := by
  have hx' := exp_eq_of_eigen theta c lam h x hx
  have hy' := exp_eq_of_eigen theta c lam h y hy
  have hlam : lam ≠ 0 := by
    rw [← hx']
    exact Complex.exp_ne_zero _
  have hquot : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((angle theta x - angle theta y : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [mul_sub, Complex.exp_sub, hx', hy', div_self hlam]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hquot
  refine ⟨k, ?_⟩
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hk' : (2 : ℂ) * (Real.pi : ℂ) * Complex.I
        * ((angle theta x - angle theta y : ℝ) : ℂ)
      = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
    rw [hk]; ring
  exact_mod_cast mul_left_cancel₀ h2 hk'

/-! ## The rationalization of Theorem 2.4

The congruence above says the phase differences against a fixed base point are
integers.  Collecting them gives a linear system whose coefficient matrix is the
difference of two binary vectors -- rational, indeed integral -- and whose
right-hand side is integral.  `MainTheory/Rationalize.lean` then supplies a
rational solution, and every relative phase is preserved because the two
solutions solve the same system. -/

/-- The matrix whose `i`-th row is the support point `pt i` minus the base
point `x0`, over the rationals. -/
def diffMatrix {iota : Type*} (pt : iota → BitString n) (x0 : BitString n) :
    Matrix iota (Fin n) ℚ :=
  fun i j => (if pt i j then 1 else 0) - (if x0 j then 1 else 0)

/-- Applying the difference matrix to a real angle vector gives the phase
differences. -/
theorem diffMatrix_mulVec {iota : Type*} [Fintype iota]
    (pt : iota → BitString n) (x0 : BitString n)
    (theta : Fin n → ℝ) (i : iota) :
    ((diffMatrix pt x0).map (algebraMap ℚ ℝ)).mulVec theta i
      = angle theta (pt i) - angle theta x0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, diffMatrix, angle,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : pt i j <;> by_cases h2 : x0 j <;> simp [h1, h2]

/-- **Theorem 2.4 for a two-sector code, qualitatively.**

If the relative phases of `theta` against a base point are integral -- which the
phase-sector congruence guarantees on the support of an eigenvector -- then
there is a *rational* angle vector with exactly the same relative phases.  It
therefore induces the same projective logical action.

The denominator bound of the paper is not part of this: it needs the sharp
invariant factor and hence Smith theory Mathlib lacks.  What is proved is that a
rational representative exists, which is what makes the lift finite. -/
theorem exists_rational_angle {iota : Type*} [Fintype iota]
    (pt : iota → BitString n) (x0 : BitString n)
    (theta : Fin n → ℝ) (h : iota → ℤ)
    (hint : ∀ i, angle theta (pt i) - angle theta x0 = (h i : ℝ)) :
    ∃ theta' : Fin n → ℚ,
      ∀ i, (∑ j, theta' j * ((if pt i j then 1 else 0) - (if x0 j then 1 else 0)))
        = (h i : ℚ) := by
  have hsol : ∃ u : Fin n → ℝ,
      ((diffMatrix pt x0).map (algebraMap ℚ ℝ)).mulVec u
        = fun i => algebraMap ℚ ℝ ((h i : ℚ)) := by
    refine ⟨ theta, ?_ ⟩
    funext i
    rw [diffMatrix_mulVec, hint i]
    simp
  obtain ⟨ theta', hth ⟩ :=
    Rationalize.exists_solution_of_exists_solution_ext (L := ℝ)
      (diffMatrix pt x0) (fun i => (h i : ℚ)) hsol
  refine ⟨ theta', fun i => ?_ ⟩
  have := congrFun hth i
  simpa [Matrix.mulVec, dotProduct, diffMatrix, mul_comm] using this

end MainTheory.RealGate
