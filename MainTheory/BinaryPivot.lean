import MainTheory.PivotSize
import MainTheory.BinaryBeta

/-!
# The coloured pivot is a binary pivot, up to a sign diagonal

`beta_N` (`eq:beta`) is a maximum over **zero--one** matrices, and
`BinaryBeta.BetaBound` requires `IsZeroOne`.  The coloured pivot of
`MainTheory.FiniteLift` is not zero--one: its physical rows are
`x_j - (base)_j`, which is `-1` wherever the base point has a one and the
support point a zero.

The paper does not meet this problem because it normalizes first: local `X`
conjugation sends the base support string to `0^n`, after which the rows are
literally `x in {0,1}^n` (`eq:augmented-row`).  Rather than transport a whole
sector decomposition through that conjugation, this file records its algebraic
residue.  Flipping a coordinate is right multiplication by a `+-1` diagonal:

  `physicalRowZ D alpha x j = signVector D j * binaryRowZ D alpha x j`,

with `binaryRowZ` the zero--one row `x_j XOR (base)_j`.  A `+-1` diagonal is
its own inverse, so it changes no denominator: `inverseDenominator` agrees for
the coloured pivot and its zero--one partner, and the latter is what
`BetaBound` accepts.

This is the paper's normalization performed on the matrix instead of on the
code.
-/

namespace MainTheory.BinaryPivot

open MainTheory.FiniteLift
open MainTheory.PhaseSectorFull
open MainTheory.SharpClearing

variable {n t : ℕ} {theta : Fin n → ℝ}

/-! ## A `+-1` diagonal changes no denominator -/

section SignDiagonal

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- A sign vector: every entry is `1` or `-1`. -/
def IsSign (e : s → ℤ) : Prop := ∀ i, e i = 1 ∨ e i = -1

omit [Fintype s] [DecidableEq s] in
theorem IsSign.mul_self {e : s → ℤ} (he : IsSign e) (i : s) :
    e i * e i = 1 := by
  rcases he i with h | h <;> rw [h] <;> ring

private theorem den_sign_mul {z : ℤ} (hz : z = 1 ∨ z = -1) (r : ℚ) :
    ((z : ℚ) * r).den = r.den := by
  rcases hz with h | h <;> subst h <;> simp

/-- Denominators, hence their lcm, are blind to a sign. -/
theorem lcmDen_sign_mul {ι : Type*} [Fintype ι] (f g : ι → ℚ) (e : ι → ℤ)
    (he : IsSign e) (h : ∀ i, f i = (e i : ℚ) * g i) :
    Denominator.lcmDen f = Denominator.lcmDen g := by
  unfold Denominator.lcmDen
  congr 1
  funext i
  rw [h i, den_sign_mul (he i)]

private theorem diagonal_sign_mul_self {e : s → ℤ} (he : IsSign e) :
    (Matrix.diagonal (fun i => (e i : ℚ)))
        * (Matrix.diagonal (fun i => (e i : ℚ))) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (e i : ℚ) * (e i : ℚ)) = fun _ : s => (1 : ℚ) := by
    funext i
    have := he.mul_self i
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
  rw [h, Matrix.diagonal_one]

private theorem ratMatrix_mul_diagonal (A : Matrix s s ℤ) (e : s → ℤ) :
    ratMatrix (A * Matrix.diagonal e)
      = ratMatrix A * Matrix.diagonal (fun i => (e i : ℚ)) := by
  ext i j
  simp [ratMatrix, Matrix.mul_diagonal]

/-- **A sign diagonal does not change the inverse denominator.**

`(A E)⁻¹ = E⁻¹ A⁻¹ = E A⁻¹`, whose entries are those of `A⁻¹` up to sign. -/
theorem inverseDenominator_mul_diagonal (A : Matrix s s ℤ) {e : s → ℤ}
    (he : IsSign e) :
    inverseDenominator (A * Matrix.diagonal e) = inverseDenominator A := by
  set E : Matrix s s ℚ := Matrix.diagonal (fun i => (e i : ℚ)) with hE
  have hEE : E * E = 1 := diagonal_sign_mul_self he
  have hEinv : E⁻¹ = E := Matrix.inv_eq_right_inv hEE
  have hentry : ∀ p : s × s,
      inverseEntries (A * Matrix.diagonal e) p
        = (e p.1 : ℚ) * inverseEntries A p := by
    intro p
    show (ratMatrix (A * Matrix.diagonal e))⁻¹ p.1 p.2
      = (e p.1 : ℚ) * (ratMatrix A)⁻¹ p.1 p.2
    rw [ratMatrix_mul_diagonal, ← hE, Matrix.mul_inv_rev, hEinv, hE,
      Matrix.diagonal_mul]
  exact lcmDen_sign_mul _ _ (fun p : s × s => e p.1)
    (fun p => he p.1) hentry

end SignDiagonal

/-! ## The zero--one partner of the coloured matrix -/

/-- The sign introduced by the base point at each physical coordinate. -/
noncomputable def signVector (D : SectorDecomposition n t theta) : Fin n → ℤ :=
  fun j => if basePoint D j then -1 else 1

/-- The sign vector on the augmented column index: physical coordinates carry
the base-point sign, colour coordinates carry `1`. -/
noncomputable def signColumn (D : SectorDecomposition n t theta) :
    Sum (Fin n) (Color D) → ℤ :=
  fun c => match c with
    | Sum.inl j => signVector D j
    | Sum.inr _ => 1

theorem isSign_signColumn (D : SectorDecomposition n t theta) :
    IsSign (signColumn D) := by
  intro c
  cases c with
  | inl j =>
      by_cases h : basePoint D j <;> simp [signColumn, signVector, h]
  | inr g => simp [signColumn]

/-- The zero--one physical row: `x` after the local `X` flip that sends the
base point to `0^n`. -/
noncomputable def binaryRowZ (D : SectorDecomposition n t theta) (alpha : Fin t)
    (x : SupportIndex D alpha) (j : Fin n) : ℤ :=
  if (xor (x.1 j) (basePoint D j)) then 1 else 0

/-- The zero--one augmented matrix. -/
noncomputable def binaryColoredMatrixZ (D : SectorDecomposition n t theta) :
    Matrix (Sigma (SupportIndex D)) (Sum (Fin n) (Color D)) ℤ :=
  ColoredSystem.augmentedMatrix (binaryRowZ D) (colorRowZ D)

theorem isZeroOne_binaryColoredMatrixZ (D : SectorDecomposition n t theta)
    (r : Sigma (SupportIndex D)) (c : Sum (Fin n) (Color D)) :
    binaryColoredMatrixZ D r c = 0 ∨ binaryColoredMatrixZ D r c = 1 := by
  rcases r with ⟨alpha, x⟩
  cases c with
  | inl j =>
      by_cases h : xor (x.1 j) (basePoint D j) <;>
        simp [binaryColoredMatrixZ, ColoredSystem.augmentedMatrix,
          ColoredSystem.augmentedRow, binaryRowZ, h]
  | inr g =>
      by_cases h : alpha = g.1 <;>
        simp [binaryColoredMatrixZ, ColoredSystem.augmentedMatrix,
          ColoredSystem.augmentedRow, colorRowZ, h]

/-- **The coloured matrix is the zero--one matrix times the sign diagonal.**

Checked coordinatewise on the four base/support bit patterns. -/
theorem coloredMatrixZ_eq (D : SectorDecomposition n t theta)
    (r : Sigma (SupportIndex D)) (c : Sum (Fin n) (Color D)) :
    coloredMatrixZ D r c = binaryColoredMatrixZ D r c * signColumn D c := by
  rcases r with ⟨alpha, x⟩
  cases c with
  | inl j =>
      show physicalRowZ D alpha x j
        = binaryRowZ D alpha x j * signVector D j
      by_cases hx : x.1 j <;> by_cases hb : basePoint D j <;>
        simp [physicalRowZ, binaryRowZ, signVector, hx, hb]
  | inr g =>
      show colorRowZ D alpha g = colorRowZ D alpha g * 1
      rw [mul_one]

/-! ## The pivot, and the bound it inherits -/

section Pivot

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- The zero--one square pivot: the same rows and columns, cut out of the
zero--one matrix instead of the signed one. -/
noncomputable def binMatrix {D : SectorDecomposition n t theta}
    (P : PivotData D s) : Matrix s s ℤ :=
  fun i j => binaryColoredMatrixZ D (P.row i) (P.column j)

theorem matrix_eq {D : SectorDecomposition n t theta}
    (P : PivotData D s) :
    P.matrix
      = (binMatrix P) * Matrix.diagonal (fun j => signColumn D (P.column j)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  exact coloredMatrixZ_eq D (P.row i) (P.column j)

omit [DecidableEq s] in
theorem binMatrix_isZeroOne {D : SectorDecomposition n t theta}
    (P : PivotData D s) : MainTheory.BinaryBeta.IsZeroOne (binMatrix P) :=
  fun i j => isZeroOne_binaryColoredMatrixZ D (P.row i) (P.column j)

/-- **The signed pivot and its zero--one partner have the same inverse
denominator.** -/
theorem inverseDenominator_eq {D : SectorDecomposition n t theta}
    (P : PivotData D s) :
    inverseDenominator P.matrix = inverseDenominator (binMatrix P) := by
  rw [matrix_eq P]
  exact inverseDenominator_mul_diagonal _
    (fun j => isSign_signColumn D (P.column j))

theorem binMatrix_det_ne_zero {D : SectorDecomposition n t theta}
    (P : PivotData D s) (hdet : P.matrix.det ≠ 0) : (binMatrix P).det ≠ 0 := by
  intro h0
  apply hdet
  rw [matrix_eq P, Matrix.det_mul, h0, zero_mul]

end Pivot

end MainTheory.BinaryPivot
