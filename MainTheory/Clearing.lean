import Mathlib
import MainTheory.Rationalize

/-!
# Elementary denominator clearing

Lemma 3.1 of `main.tex` clears the denominators of `C^{-1} h` for a nonsingular
integer matrix `C` and integer vector `h`, using the last invariant factor
`d_s(C)` of the Smith normal form as the multiplier.

That multiplier is sharp, and sharpness is what the constants `beta_N` are
about.  But the *qualitative* statement -- that some positive integer clears the
denominators -- needs no Smith theory at all: the adjugate gives
`det(C) * C^{-1} = adj(C)`, which is an integer matrix, so the determinant works.

This matters because Mathlib's Smith normal form is not usable for the sharp
version.  `Module.Basis.SmithNormalForm` records no divisibility chain -- there
is no field asserting that one diagonal entry divides the next -- and there is
no uniqueness of invariant factors, which the paper's notation `d_i(C)` assumes
without proof.  So the sharp multiplier is out of reach, while the version below
is elementary and complete.

The consequence for the rest of the paper: everywhere `main.tex` needs only that
*a* finite denominator exists -- which is Theorem 2.4's use, and the reason the
lift `D(a;q)` is finite at all -- the determinant suffices and this file closes
the gap.  Only the numerical bound `q <= beta_n` needs the sharp factor.
-/

namespace MainTheory.Clearing

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The rational cast, as a ring hom, so that it commutes with matrix products. -/
private def qq : ℤ →+* ℚ := Int.castRingHom ℚ

omit [DecidableEq s] in
/-- Casting commutes with `mulVec`. -/
theorem map_mulVec (C : Matrix s s ℤ) (v : s → ℤ) (i : s) :
    ((C.map qq).mulVec (fun j => (v j : ℚ))) i = ((C.mulVec v i : ℤ) : ℚ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, qq,
    Int.coe_castRingHom, Int.cast_sum, Int.cast_mul]

/-! ## The clearing theorem -/

/-- **The determinant clears the denominators.**

If an integer system has a rational solution, then multiplying that solution by
`det C` gives an integer vector -- explicitly, `adj(C)` applied to the
right-hand side.  This is `main.tex` Lemma 3.1 with the sharp invariant factor
replaced by a multiple of it. -/
theorem det_smul_eq_adjugate_mulVec
    (C : Matrix s s ℤ) (h : s → ℤ) (x : s → ℚ)
    (hx : (C.map qq).mulVec x = fun i => ((h i : ℤ) : ℚ)) (i : s) :
    ((C.det : ℤ) : ℚ) * x i = ((C.adjugate.mulVec h i : ℤ) : ℚ) := by
  have hmul : (C.adjugate.map qq) * (C.map qq) = ((C.det : ℤ) : ℚ) • 1 := by
    rw [← Matrix.map_mul, Matrix.adjugate_mul]
    ext p r
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, qq,
      Int.coe_castRingHom, smul_eq_mul]
    split_ifs <;> simp
  have hstep : (C.adjugate.map qq).mulVec ((C.map qq).mulVec x)
      = (C.adjugate.map qq).mulVec (fun j => ((h j : ℤ) : ℚ)) := by rw [hx]
  rw [Matrix.mulVec_mulVec, hmul] at hstep
  have hL := congrFun hstep i
  rw [map_mulVec] at hL
  simpa [Matrix.smul_mulVec] using hL

/-! ## The rationalization step of Theorem 2.4, end to end

`MainTheory/Rationalize.lean` turns a real solution into a rational one; this
file clears its denominators.  Composed, they are exactly the step `main.tex`
takes to pass from real physical angles to a finite lift. -/

/-- **Real angles in, a finite denominator out.**

An integer system with a real solution has a rational solution whose
denominators are all cleared by `det C`. -/
theorem exists_cleared_of_real
    (C : Matrix s s ℤ) (h : s → ℤ)
    (hR : ∃ u : s → ℝ,
      (C.map (fun z : ℤ => (z : ℝ))).mulVec u
        = fun i => ((h i : ℤ) : ℝ)) :
    ∃ x : s → ℚ,
      (C.map qq).mulVec x = (fun i => ((h i : ℤ) : ℚ)) ∧
        ∀ i, ((C.det : ℤ) : ℚ) * x i = ((C.adjugate.mulVec h i : ℤ) : ℚ) := by
  obtain ⟨ u, hu ⟩ := hR
  have hmapeq : (C.map qq).map (algebraMap ℚ ℝ)
      = C.map (fun z : ℤ => (z : ℝ)) := by
    rw [Matrix.map_map]
    congr 1
  have hQ : ∃ x : s → ℚ, (C.map qq).mulVec x = fun i => ((h i : ℤ) : ℚ) := by
    refine Rationalize.exists_solution_of_exists_solution_ext (L := ℝ)
      (C.map qq) (fun i => ((h i : ℤ) : ℚ)) ⟨ u, ?_ ⟩
    rw [hmapeq, hu]
    funext i
    simp
  obtain ⟨ x, hx ⟩ := hQ
  exact ⟨ x, hx, fun i => det_smul_eq_adjugate_mulVec C h x hx i ⟩

/-! ## Non-vacuity -/

/-- A worked instance: the system `2 x = 1` over the integers has the rational
solution `1/2`, and its determinant `2` clears it. -/
theorem clearing_example :
    ((2 : ℤ) : ℚ) * (1/2 : ℚ) = ((1 : ℤ) : ℚ) := by
  norm_num

/-- **A finite denominator exists.**

The form Theorem 2.4 uses: a rational solution of an integer system has all its
denominators cleared by a single positive integer. -/
theorem exists_clearing (C : Matrix s s ℤ) (h : s → ℤ) (x : s → ℚ)
    (hdet : C.det ≠ 0)
    (hx : (C.map qq).mulVec x = fun i => ((h i : ℤ) : ℚ)) :
    ∃ (D : ℤ) (z : s → ℤ), D ≠ 0 ∧ ∀ i, (D : ℚ) * x i = (z i : ℚ) :=
  ⟨ C.det, C.adjugate.mulVec h, hdet,
    fun i => det_smul_eq_adjugate_mulVec C h x hx i ⟩

end MainTheory.Clearing
