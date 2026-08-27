import Mathlib

/-!
# Rationalization of a consistent linear system

The qualitative finite-lift theorem of `main.tex` (Theorem 2.4) turns a real
physical phase vector into a rational one.  Stripped of the quantum setting, the
step it rests on is this: a linear system whose coefficients and whose
right-hand side are rational, and which has a *real* solution, already has a
*rational* solution.

The paper proves it by selecting a nonsingular square submatrix and inverting
it.  That route needs determinantal rank, and tacitly needs the rank of a
rational matrix not to change when the field is enlarged -- neither of which is
available in Mathlib.  The argument here avoids both.  A field extension `L / K`
is in particular a `K`-vector space, so the structure map `K → L` admits a
`K`-linear retraction.  Applying it coordinatewise to a solution over `L`
produces a solution over `K`, because the coefficients already lie in `K` and the
retraction is `K`-linear.

The proof is shorter than the paper's, works for an arbitrary field extension
rather than for the rationals inside the reals, and uses no rank theory at all.

The second ingredient is `eq_of_ker_eq_zero`: a coordinate at which the kernel
vanishes takes the same value in every solution, so rationalizing does not
disturb it.  In `main.tex` those are the colour coordinates, protected by the
common first moment of Lemma 2.3.
-/

namespace MainTheory.Rationalize

variable {K L : Type*} [Field K] [Ring L] [Nontrivial L] [Algebra K L]
variable {m n : Type*} [Fintype n]

/-! ## A retraction of the structure map -/

/-- A `K`-linear retraction of `algebraMap K L`.

It exists because `L` is a `K`-vector space and the structure map is injective,
`K` being a field.  It is *not* a ring map, and nothing below needs it to be. -/
noncomputable def retract (K L : Type*) [Field K] [Ring L] [Nontrivial L]
    [Algebra K L] : L →ₗ[K] K :=
  (Algebra.linearMap K L).leftInverse

theorem algebraMap_ker_eq_bot :
    LinearMap.ker (Algebra.linearMap K L) = ⊥ :=
  LinearMap.ker_eq_bot.2 (fun _ _ h => (algebraMap K L).injective h)

@[simp] theorem retract_algebraMap (a : K) :
    retract K L (algebraMap K L a) = a :=
  LinearMap.leftInverse_apply_of_inj algebraMap_ker_eq_bot a

/-- Being `K`-linear, the retraction pulls a scalar of `K` out of a product
taken in `L`. -/
theorem retract_algebraMap_mul (a : K) (x : L) :
    retract K L (algebraMap K L a * x) = a * retract K L x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-! ## The rationalization theorem -/

/-- **A system with coefficients in `K` that is solvable over an extension is
solvable over `K`.**

For `main.tex` this is `K` the rationals, `L` the reals, `R` the binary matrix
of augmented support rows, and `h` the integer right-hand side: a real phase
vector solving the sector equations forces a rational one to exist. -/
theorem exists_solution_of_exists_solution_ext
    (R : Matrix m n K) (h : m → K)
    (hL : ∃ u : n → L,
      (R.map (algebraMap K L)).mulVec u = fun i => algebraMap K L (h i)) :
    ∃ u' : n → K, R.mulVec u' = h := by
  obtain ⟨ u, hu ⟩ := hL
  refine ⟨ fun j => retract K L (u j), ?_ ⟩
  funext i
  have hi : (R.map (algebraMap K L)).mulVec u i = algebraMap K L (h i) :=
    congrFun hu i
  have hpush : R.mulVec (fun j => retract K L (u j)) i
      = retract K L ((R.map (algebraMap K L)).mulVec u i) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => (retract_algebraMap_mul (R i j) (u j)).symm
  rw [hpush, hi, retract_algebraMap]

/-! ## Coordinates protected by the kernel

In `main.tex` the rationalized vector must keep the colour coordinates of the
original.  They are protected because every kernel vector vanishes on them,
which is exactly the hypothesis here. -/

/-- Two solutions of the same system agree at every coordinate where the kernel
vanishes. -/
theorem eq_of_ker_eq_zero
    (R : Matrix m n K) (h : m → K) (j : n)
    (hker : ∀ v : n → K, R.mulVec v = 0 → v j = 0)
    (u u' : n → K) (hu : R.mulVec u = h) (hu' : R.mulVec u' = h) :
    u j = u' j := by
  have hz : R.mulVec (u - u') = 0 := by
    rw [Matrix.mulVec_sub, hu, hu', sub_self]
  have := hker _ hz
  simpa [sub_eq_zero] using this

/-! ## Non-vacuity

The kernel checks the proof, not the statement, so the hypothesis is exhibited
as satisfiable rather than merely unrefuted.  The system below has an irrational
solution over the reals -- and the theorem hands back a rational one. -/

/-- A real solution of a rational system, with irrational coordinates. -/
theorem pi_solution :
    (((Matrix.of !![(1 : ℚ), 1]).map (algebraMap ℚ ℝ)).mulVec
        ![ Real.pi, 1 - Real.pi ])
      = fun i => algebraMap ℚ ℝ ((![ (1 : ℚ) ]) i) := by
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

/-- The theorem applies to it, so the hypothesis is not vacuous. -/
theorem rationalized_pi_solution :
    ∃ u : Fin 2 → ℚ, (Matrix.of !![(1 : ℚ), 1]).mulVec u = ![ 1 ] :=
  exists_solution_of_exists_solution_ext (L := ℝ) _ _ ⟨ _, pi_solution ⟩

end MainTheory.Rationalize
