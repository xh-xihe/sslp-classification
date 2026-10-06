import Mathlib
import MainTheory.Rationalize
import MainTheory.Denominator

/-!
# The distance-three rationalization

Theorem 5.3 of `main.tex` produces, from a real phase vector preserving the
code, a rational one inducing the same projective logical action, and bounds its
denominator by the binary Smith constant `beta_n`.

Its proof selects `r` linearly independent support points as the rows of a
binary matrix `B`, picks `r` coordinates on which the square submatrix `C` is
nonsingular, solves `C theta'_I = h` and extends by zero.  The pivot
construction is there to make the bound *sharp*: it is what produces
`q | d_r(C) <= beta_r <= beta_n`.

For the qualitative conclusion -- that a rational representative exists at all,
which is what makes the lift finite -- the pivot is unnecessary.  `B` is a binary
matrix and `h` is integral, so `MainTheory/Rationalize.lean` yields a rational
solution directly, and `MainTheory/Denominator.lean` gives it a least denominator
and primitivity.  What this file adds is the step that makes the new vector
*equivalent* to the old one:

    B (theta' - theta) = 0  implies  theta' and theta agree on the row span of B,

which is `eq:phase-agreement-on-support`.  Since the common affine-span lemma
puts both logical supports inside that span, the two phase vectors act with the
same phase on every supported basis string.

So the chain is complete except for the numerical bound, and the numerical bound
is exactly the part that needs the sharp invariant factor `d_r(C)` and hence the
Smith theory Mathlib lacks.  That is stated, not hidden.
-/

namespace MainTheory.D3Bound

variable {r n : Type*}

/-! ## Agreement on the row span -/

/-- **Two solutions of `B u = B v` agree on every row combination.**

This is `main.tex` eq. `eq:phase-agreement-on-support`: the rationalized phase
vector differs from the original by something orthogonal to the row span, and
the supports lie in that span. -/
theorem dot_eq_of_mulVec_eq [Fintype r] [Fintype n]
    (B : Matrix r n ℝ) (u v : n → ℝ)
    (hB : B.mulVec u = B.mulVec v)
    (x : n → ℝ) (w : r → ℝ)
    (hx : x = fun j => ∑ i, w i * B i j) :
    (∑ j, u j * x j) = ∑ j, v j * x j := by
  have key : ∀ z : n → ℝ,
      (∑ j, z j * (∑ i, w i * B i j)) = ∑ i, w i * B.mulVec z i := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hx, key u, key v, hB]

/-! ## The rationalization, end to end -/

/-- **A rational phase vector inducing the same action.**

If the support-row system `B theta = h` has integral right-hand side and binary
(indeed, any rational) coefficients, then there is a rational `theta'` solving
the same system.  By `dot_eq_of_mulVec_eq` it then agrees with `theta` on the
whole row span, hence on both logical supports.

The denominator bound `q <= beta_n` is *not* proved: it needs the sharp
invariant factor `d_r(C)`, and Mathlib's Smith normal form carries no
divisibility chain.  What is proved is that a finite denominator exists, which
is what makes the lift finite. -/
theorem exists_rational_agreeing [Fintype r] [Fintype n]
    (B : Matrix r n ℚ) (h : r → ℚ)
    (theta : n → ℝ)
    (hBt : (B.map (algebraMap ℚ ℝ)).mulVec theta
      = fun i => algebraMap ℚ ℝ (h i)) :
    ∃ theta' : n → ℚ, B.mulVec theta' = h :=
  Rationalize.exists_solution_of_exists_solution_ext (L := ℝ) B h ⟨ theta, hBt ⟩

/-- The rational representative has a least denominator, and the resulting lift
is primitive.  This is the composition with `MainTheory/Denominator.lean`. -/
theorem exists_primitive_lift [Fintype r] [Fintype n] [DecidableEq n]
    (B : Matrix r n ℚ) (h : r → ℚ)
    (theta : n → ℝ)
    (hBt : (B.map (algebraMap ℚ ℝ)).mulVec theta
      = fun i => algebraMap ℚ ℝ (h i)) :
    ∃ (theta' : n → ℚ) (q : ℕ), B.mulVec theta' = h ∧ 0 < q ∧
      (∀ j, ((q : ℚ)) * theta' j = (Denominator.liftNum theta' j : ℚ)) ∧
      (∀ d : ℕ, d ∣ q → (∀ j, d ∣ (Denominator.liftNum theta' j).natAbs)
        → d = 1) := by
  obtain ⟨ theta', hth ⟩ := exists_rational_agreeing B h theta hBt
  refine ⟨ theta', Denominator.lcmDen theta', hth,
    Denominator.lcmDen_pos theta', Denominator.liftNum_spec theta', ?_ ⟩
  intro d hdq hdj
  refine Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum theta' d hdq (fun j => ?_)
  exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 (hdj j))

end MainTheory.D3Bound
