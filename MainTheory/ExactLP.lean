import Mathlib

/-!
# Exact rational LP certificates

The six-qubit reductions use a numerical solver only to propose data.  This
module gives the kernel-facing semantics for the three certificate forms used
in `main.tex`: a rational feasible point, a Farkas infeasibility separator, and
a dual proof that one nonnegative variable is forced to zero.
-/

namespace MainTheory.ExactLP

open scoped BigOperators

variable {r c : Type*} [Fintype r] [Fintype c]
variable {A : Matrix r c ℚ} {b : r → ℚ} {i : c}

/-- Exact feasibility of `A p = b, p ≥ 0` over the rationals. -/
def Feasible (A : Matrix r c ℚ) (b : r → ℚ) (p : c → ℚ) : Prop :=
  A.mulVec p = b ∧ ∀ j, 0 ≤ p j

/-- A proof-carrying primal certificate is simply a rational vector together
with the equations the kernel must check. -/
structure PrimalCertificate (A : Matrix r c ℚ) (b : r → ℚ) where
  point : c → ℚ
  valid : Feasible A b point

omit [Fintype r] in
theorem feasible_of_primal (cert : PrimalCertificate A b) :
    ∃ p, Feasible A b p :=
  ⟨cert.point, cert.valid⟩

omit [Fintype c] in
/-- The transpose action is the row-vector action used in Farkas duality. -/
theorem vecMul_eq_transpose_mulVec (A : Matrix r c ℚ) (y : r → ℚ) :
    Matrix.vecMul y A = A.transpose.mulVec y := by
  simpa using (Matrix.vecMul_transpose (A := A.transpose) y)

/-- A Farkas certificate: the dual is nonpositive on every primal column but
strictly positive on the right-hand side. -/
structure InfeasibleCertificate (A : Matrix r c ℚ) (b : r → ℚ) where
  dual : r → ℚ
  columns_nonpos : ∀ j, (A.transpose.mulVec dual) j ≤ 0
  rhs_pos : 0 < dotProduct dual b

/-- **Kernel-checked Farkas contradiction.** -/
theorem not_feasible_of_infeasible
    (cert : InfeasibleCertificate A b) :
    ¬ ∃ p, Feasible A b p := by
  rintro ⟨p, hp, hnonneg⟩
  have hdot : dotProduct cert.dual b =
      dotProduct (A.transpose.mulVec cert.dual) p := by
    calc
      dotProduct cert.dual b = dotProduct cert.dual (A.mulVec p) := by
        exact congrArg (dotProduct cert.dual) hp.symm
      _ = dotProduct (A.transpose.mulVec cert.dual) p := by
        rw [Matrix.dotProduct_mulVec, vecMul_eq_transpose_mulVec]
  have hnonpos : dotProduct (A.transpose.mulVec cert.dual) p ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonpos_of_nonneg
      (cert.columns_nonpos j) (hnonneg j)
  have hrhs := cert.rhs_pos
  rw [hdot] at hrhs
  exact (not_lt_of_ge hnonpos) hrhs

/-- The standard basis vector, kept rational so certificate files need no
coercion convention. -/
def basisVector [DecidableEq c] (i : c) : c → ℚ :=
  fun j => if j = i then 1 else 0

/-- A dual certificate for the assertion that coordinate `i` is identically
zero on the feasible polytope.  This is equation (7.21) of `main.tex`. -/
structure ForcedZeroCertificate [DecidableEq c]
    (A : Matrix r c ℚ) (b : r → ℚ) (i : c) where
  dual : r → ℚ
  column_bound : ∀ j,
    (A.transpose.mulVec dual) j ≤ -(basisVector i j)
  rhs_zero : dotProduct dual b = 0

/-- **A valid forced-zero dual really forces the chosen coordinate to zero.** -/
theorem coordinate_eq_zero_of_certificate [DecidableEq c]
    {i : c} (cert : ForcedZeroCertificate A b i)
    {p : c → ℚ} (hp : Feasible A b p) :
    p i = 0 := by
  rcases hp with ⟨heq, hnonneg⟩
  have hdot : dotProduct cert.dual b =
      dotProduct (A.transpose.mulVec cert.dual) p := by
    calc
      dotProduct cert.dual b = dotProduct cert.dual (A.mulVec p) := by
        exact congrArg (dotProduct cert.dual) heq.symm
      _ = dotProduct (A.transpose.mulVec cert.dual) p := by
        rw [Matrix.dotProduct_mulVec, vecMul_eq_transpose_mulVec]
  have hle : dotProduct (A.transpose.mulVec cert.dual) p ≤ -p i := by
    calc
      dotProduct (A.transpose.mulVec cert.dual) p ≤
          dotProduct (fun j => -(basisVector i j)) p := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (cert.column_bound j) (hnonneg j)
      _ = -p i := by
        classical
        simp [dotProduct, basisVector]
  have hzeroDual : dotProduct (A.transpose.mulVec cert.dual) p = 0 := by
    rw [← hdot, cert.rhs_zero]
  have hpi_le : p i ≤ 0 := by
    rw [hzeroDual] at hle
    linarith
  exact le_antisymm hpi_le (hnonneg i)

/-- An exact positive primal witness proves that a variable is active. -/
structure ActiveCertificate (A : Matrix r c ℚ) (b : r → ℚ) (i : c) where
  point : c → ℚ
  feasible : Feasible A b point
  positive : 0 < point i

omit [Fintype r] in
theorem active_of_certificate (cert : ActiveCertificate A b i) :
    ∃ p, Feasible A b p ∧ 0 < p i :=
  ⟨cert.point, cert.feasible, cert.positive⟩

/-- Primal positivity and a forced-zero dual are mutually incompatible.  This
is a useful self-test target for generated certificate bundles. -/
theorem active_not_forced_zero [DecidableEq c]
    (ha : ActiveCertificate A b i)
    (hz : ForcedZeroCertificate A b i) : False := by
  have := coordinate_eq_zero_of_certificate hz ha.feasible
  have hpos := ha.positive
  rw [this] at hpos
  exact lt_irrefl 0 hpos

end MainTheory.ExactLP
