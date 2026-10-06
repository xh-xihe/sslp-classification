import MainTheory.BinaryDetCircuit

/-!
# A last-row cofactor reduction for binary `6 x 6` determinants

For a fixed top `3 x 6` block and fixed first two rows of the bottom block,
the determinant is a linear function of the six bits in the last row.  This
module proves that statement over `Int`, then bounds the linear form between
the sum of its negative coefficients and the sum of its positive
coefficients.

The resulting `ReducedBound` is the interface for finite certificates: it
quantifies over only two six-bit rows.  The third row is discharged by the
generic order proof below.  No determinant bound for any numerical pattern is
asserted in this file.
-/

namespace MainTheory.BinaryDetCofactor

open scoped BigOperators
open MainTheory.BinaryDetCircuit

abbrev F3 := Fin 3
abbrev F6 := Fin 6
abbrev BinaryRow := F6 → Bool

/-- Embed one Boolean matrix entry into the integers. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- Assemble the three rows of a binary bottom block. -/
def bottomOfRows (u v w : BinaryRow) : Matrix F3 F6 ℤ :=
  fun i j ↦ ![bitZ (u j), bitZ (v j), bitZ (w j)] i

/-- A binary standard basis row. -/
def basisRow (j : F6) : BinaryRow := fun k ↦ k == j

/-- The coefficient of the last-row bit in column `j`.  Evaluating the
determinant on the standard basis row avoids introducing a separately trusted
cofactor formula. -/
def lastRowCoefficient (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (j : F6) : ℤ :=
  laplace33Grouped top (bottomOfRows u v (basisRow j))

/-- The last-row linear form. -/
def lastRowLinearForm (top : Matrix F3 F6 ℤ)
    (u v w : BinaryRow) : ℤ :=
  ∑ j : F6, bitZ (w j) * lastRowCoefficient top u v j

/-- The matrix with the same first five rows and a zero sixth row. -/
def zeroLastRowMatrix (top : Matrix F3 F6 ℤ) (u v : BinaryRow) :
    Matrix F6 F6 ℤ :=
  stack3x3 top (bottomOfRows u v (fun _ ↦ false))

/-- Integer standard basis row. -/
def integerBasisRow (j : F6) : F6 → ℤ :=
  fun k ↦ if k = j then 1 else 0

/-- Every integer row is its finite standard-basis expansion. -/
theorem row_eq_sum_basis (r : F6 → ℤ) :
    r = ∑ j : F6, r j • integerBasisRow j := by
  funext k
  simp [integerBasisRow]

/-- Replacing the zero sixth row recovers the binary bottom row. -/
theorem updateRow_zeroLastRowMatrix (top : Matrix F3 F6 ℤ)
    (u v w : BinaryRow) :
    (zeroLastRowMatrix top u v).updateRow (5 : F6) (fun j ↦ bitZ (w j)) =
      stack3x3 top (bottomOfRows u v w) := by
  ext i j
  fin_cases i <;>
    simp [zeroLastRowMatrix, Matrix.updateRow, stack3x3, bottomOfRows, bitZ]

/-- A basis-row update is the matrix used to define the corresponding
cofactor. -/
theorem updateRow_zeroLastRowMatrix_basis (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (j : F6) :
    (zeroLastRowMatrix top u v).updateRow (5 : F6) (integerBasisRow j) =
      stack3x3 top (bottomOfRows u v (basisRow j)) := by
  rw [show integerBasisRow j = fun k => bitZ (basisRow j k) by
    funext k
    simp [integerBasisRow, basisRow, bitZ]]
  exact updateRow_zeroLastRowMatrix top u v (basisRow j)

/-- Determinant linearity for a finite sum in one row.  The elementary
finite-set induction keeps elaboration local; unfolding the alternating-map
implementation of `det` here is substantially more expensive. -/
private theorem det_updateRow_sum_finset (M : Matrix F6 F6 ℤ) (i : F6)
    (g : F6 → F6 → ℤ) (s : Finset F6) :
    (M.updateRow i (∑ j ∈ s, g j)).det =
      ∑ j ∈ s, (M.updateRow i (g j)).det := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Matrix.updateRow]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.det_updateRow_add,
        Finset.sum_insert ha, ih]

private theorem det_updateRow_sum_univ (M : Matrix F6 F6 ℤ) (i : F6)
    (g : F6 → F6 → ℤ) :
    (M.updateRow i (∑ j : F6, g j)).det =
      ∑ j : F6, (M.updateRow i (g j)).det :=
  det_updateRow_sum_finset M i g Finset.univ

/-- The grouped determinant circuit is exactly linear in the third bottom
row, with coefficients obtained by evaluating it on the six basis rows. -/
theorem laplace33Grouped_eq_lastRowLinearForm
    (top : Matrix F3 F6 ℤ) (u v w : BinaryRow) :
    laplace33Grouped top (bottomOfRows u v w) =
      lastRowLinearForm top u v w := by
  rw [laplace33Grouped_eq_det, ← updateRow_zeroLastRowMatrix]
  unfold lastRowLinearForm
  rw [row_eq_sum_basis (fun j ↦ bitZ (w j))]
  rw [det_updateRow_sum_univ]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_updateRow_smul]
  rw [updateRow_zeroLastRowMatrix_basis]
  rw [← laplace33Grouped_eq_det]
  rfl

/-- Sum of all negative coefficients. -/
def negativeCoefficientSum (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) : ℤ :=
  ∑ j : F6, min (lastRowCoefficient top u v j) 0

/-- Sum of all positive coefficients. -/
def positiveCoefficientSum (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) : ℤ :=
  ∑ j : F6, max (lastRowCoefficient top u v j) 0

/-! ## Antisymmetry of the two enumerated bottom rows -/

/-- Swapping the first two bottom rows is the concrete transposition of full
matrix rows three and four. -/
theorem stack3x3_bottom_swap (top : Matrix F3 F6 ℤ)
    (u v w : BinaryRow) :
    stack3x3 top (bottomOfRows v u w) =
      (stack3x3 top (bottomOfRows u v w)).submatrix
        (Equiv.swap (3 : F6) (4 : F6)) id := by
  ext i j
  fin_cases i <;>
    simp [stack3x3, bottomOfRows, Equiv.swap_apply_def]

/-- Each last-row cofactor changes sign when the first two free bottom rows
are exchanged. -/
theorem lastRowCoefficient_swap (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (j : F6) :
    lastRowCoefficient top v u j = -lastRowCoefficient top u v j := by
  unfold lastRowCoefficient
  rw [laplace33Grouped_eq_det, laplace33Grouped_eq_det,
    stack3x3_bottom_swap,
    Matrix.det_permute, Equiv.Perm.sign_swap (by decide)]
  norm_num

/-- The pairwise form of `ReducedBound`, useful for generated triangular
tables. -/
def PairReducedBound (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (B : ℕ) : Prop :=
  (-(B : ℤ) ≤ negativeCoefficientSum top u v) ∧
    (positiveCoefficientSum top u v ≤ (B : ℤ))

instance pairReducedBoundDecidable (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (B : ℕ) :
    Decidable (PairReducedBound top u v B) := by
  unfold PairReducedBound
  infer_instance

private theorem min_neg_zero (z : ℤ) : min (-z) 0 = -max z 0 := by
  omega

private theorem max_neg_zero (z : ℤ) : max (-z) 0 = -min z 0 := by
  omega

theorem negativeCoefficientSum_swap (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) :
    negativeCoefficientSum top v u = -positiveCoefficientSum top u v := by
  unfold negativeCoefficientSum positiveCoefficientSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [lastRowCoefficient_swap, min_neg_zero]

theorem positiveCoefficientSum_swap (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) :
    positiveCoefficientSum top v u = -negativeCoefficientSum top u v := by
  unfold positiveCoefficientSum negativeCoefficientSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [lastRowCoefficient_swap, max_neg_zero]

/-- Consequently a checked unordered pair covers the opposite order for
free.  Generated certificates only need the 2080 pairs with `code u ≤ code v`.
-/
theorem PairReducedBound.swap {top : Matrix F3 F6 ℤ}
    {u v : BinaryRow} {B : ℕ}
    (h : PairReducedBound top u v B) : PairReducedBound top v u B := by
  rcases h with ⟨hneg, hpos⟩
  constructor
  · rw [negativeCoefficientSum_swap]
    omega
  · rw [positiveCoefficientSum_swap]
    omega

/-! ## Canonical row codes and triangular finite certificates -/

/-- Six row bits in the same least-significant-bit convention as the existing
18-bit tail decoder. -/
def rowOfBits (b : BitVec 6) : BinaryRow := fun j ↦ b.getLsb j

@[simp] theorem rowOfBits_ofFnLE (u : BinaryRow) :
    rowOfBits (BitVec.ofFnLE u) = u := by
  funext j
  simp [rowOfBits]

/-- A triangular certificate checks row-code pairs only in nondecreasing
order. -/
def TriangularCertificate (top : Matrix F3 F6 ℤ) (B : ℕ) : Prop :=
  ∀ a b : BitVec 6, a.toNat ≤ b.toNat →
    PairReducedBound top (rowOfBits a) (rowOfBits b) B

private theorem min_le_bitZ_mul (b : Bool) (z : ℤ) :
    min z 0 ≤ bitZ b * z := by
  cases b
  · simp [bitZ]
  · simp [bitZ]

private theorem bitZ_mul_le_max (b : Bool) (z : ℤ) :
    bitZ b * z ≤ max z 0 := by
  cases b
  · simp [bitZ]
  · simp [bitZ]

/-- Every Boolean last row lies between the negative- and
positive-coefficient envelopes. -/
theorem lastRowLinearForm_bounds (top : Matrix F3 F6 ℤ)
    (u v w : BinaryRow) :
    negativeCoefficientSum top u v ≤ lastRowLinearForm top u v w ∧
      lastRowLinearForm top u v w ≤ positiveCoefficientSum top u v := by
  constructor
  · apply Finset.sum_le_sum
    intro j _
    exact min_le_bitZ_mul (w j) (lastRowCoefficient top u v j)
  · apply Finset.sum_le_sum
    intro j _
    exact bitZ_mul_le_max (w j) (lastRowCoefficient top u v j)

/-- A reduced numerical certificate.  It checks only the first two bottom
rows; the third row is handled uniformly by `lastRowLinearForm_bounds`. -/
def ReducedBound (top : Matrix F3 F6 ℤ) (B : ℕ) : Prop :=
  ∀ u v : BinaryRow,
    (-(B : ℤ) ≤ negativeCoefficientSum top u v) ∧
    (positiveCoefficientSum top u v ≤ (B : ℤ))

instance reducedBoundDecidable (top : Matrix F3 F6 ℤ) (B : ℕ) :
    Decidable (ReducedBound top B) := by
  unfold ReducedBound
  infer_instance

/-- Antisymmetry turns a triangular certificate into the complete reduced
bound quantified over all two-row functions. -/
theorem TriangularCertificate.reducedBound
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : TriangularCertificate top B) : ReducedBound top B := by
  intro u v
  let a : BitVec 6 := BitVec.ofFnLE u
  let b : BitVec 6 := BitVec.ofFnLE v
  by_cases hab : a.toNat ≤ b.toNat
  · simpa [PairReducedBound, a, b] using h a b hab
  · have hba : b.toNat ≤ a.toNat := by omega
    have hs := (h b a hba).swap
    simpa [PairReducedBound, a, b] using hs

private theorem natAbs_le_of_bounds {x : ℤ} {B : ℕ}
    (hlower : -(B : ℤ) ≤ x) (hupper : x ≤ (B : ℤ)) :
    x.natAbs ≤ B := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact (abs_le).2 ⟨hlower, hupper⟩

/-- A reduced certificate bounds the determinant for all three binary bottom
rows. -/
theorem ReducedBound.detNatAbs_bottomRows
    {top : Matrix F3 F6 ℤ} {B : ℕ} (h : ReducedBound top B)
    (u v w : BinaryRow) :
    (stack3x3 top (bottomOfRows u v w)).det.natAbs ≤ B := by
  have henvelope := lastRowLinearForm_bounds top u v w
  have hcertificate := h u v
  apply natAbs_le_of_bounds
  · calc
      -(B : ℤ) ≤ negativeCoefficientSum top u v := hcertificate.1
      _ ≤ lastRowLinearForm top u v w := henvelope.1
      _ = (stack3x3 top (bottomOfRows u v w)).det := by
        rw [← laplace33Grouped_eq_det]
        exact (laplace33Grouped_eq_lastRowLinearForm top u v w).symm
  · calc
      (stack3x3 top (bottomOfRows u v w)).det =
          lastRowLinearForm top u v w := by
        rw [← laplace33Grouped_eq_det]
        exact laplace33Grouped_eq_lastRowLinearForm top u v w
      _ ≤ positiveCoefficientSum top u v := henvelope.2
      _ ≤ (B : ℤ) := hcertificate.2

/-! ## Connection to the existing 18-bit tail encoding -/

/-- Extract one of the three six-bit rows from the existing row-major tail
encoding. -/
def tailRow (bits : BitVec 18) (i : F3) : BinaryRow :=
  fun j ↦ bits.getLsbD (6 * (i : ℕ) + (j : ℕ))

/-- The row view reconstructs exactly the existing bottom-block decoder. -/
theorem bottomOfRows_tailRows (bits : BitVec 18) :
    bottomOfRows (tailRow bits 0) (tailRow bits 1) (tailRow bits 2) =
      tailOfBits (R := ℤ) bits := by
  ext i j
  fin_cases i <;> rfl

/-- Hence a reduced certificate covers every one of the `2^18` tails without
enumerating the third row. -/
theorem ReducedBound.detNatAbs_tail
    {top : Matrix F3 F6 ℤ} {B : ℕ} (h : ReducedBound top B)
    (bits : BitVec 18) :
    (stack3x3 top (tailOfBits (R := ℤ) bits)).det.natAbs ≤ B := by
  rw [← bottomOfRows_tailRows]
  exact h.detNatAbs_bottomRows
    (tailRow bits 0) (tailRow bits 1) (tailRow bits 2)

/-! ## Kernel-facing pattern-certificate interface -/

/-- The reduced predicate attached to one authoritative top-pattern index. -/
def PatternReducedBound (i : PatternIndex) (B : ℕ) : Prop :=
  ReducedBound (topOfPattern (R := ℤ) (patternAt i)) B

instance patternReducedBoundDecidable (i : PatternIndex) (B : ℕ) :
    Decidable (PatternReducedBound i B) := by
  unfold PatternReducedBound
  infer_instance

/-- This is the exact endpoint expected from each future numerical shard. -/
theorem PatternReducedBound.detNatAbs_matrixOfPatternTail
    {i : PatternIndex} {B : ℕ} (h : PatternReducedBound i B)
    (bits : BitVec 18) :
    (matrixOfPatternTail (R := ℤ) (patternAt i) bits).det.natAbs ≤ B := by
  exact h.detNatAbs_tail bits

end MainTheory.BinaryDetCofactor
