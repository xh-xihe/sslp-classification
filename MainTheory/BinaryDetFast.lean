import MainTheory.BinaryDetCofactor

/-!
# Low-overhead arithmetic presentation of the six-by-six cofactor envelope

The semantic certificate remains `PairReducedBound`, over `Int` matrices.
Generated numerical leaves should not repeatedly reduce twenty opaque
`Matrix.det` nodes, however.  This file replaces every bottom `3 x 3`
determinant in `laplace33Grouped` by the already proved six-monomial
polynomial `minor3Poly`, and proves once that the result is unchanged.

Thus the executable predicate below is merely a cheaper presentation of the
same integer theorem.  It is not a second, externally trusted determinant
implementation.
-/

namespace MainTheory.BinaryDetFast

open scoped BigOperators
open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor

abbrev F3 := Fin 3
abbrev F6 := Fin 6

/-- The grouped `3+3` circuit with both minors in explicit polynomial form. -/
def laplace33Polynomial {R : Type*} [CommRing R]
    (top bottom : Matrix F3 F6 R) : R :=
    minor3Poly top 0 1 2 * minor3Poly bottom 3 4 5
  - minor3Poly top 0 1 3 * minor3Poly bottom 2 4 5
  + minor3Poly top 0 1 4 * minor3Poly bottom 2 3 5
  - minor3Poly top 0 1 5 * minor3Poly bottom 2 3 4
  + minor3Poly top 0 2 3 * minor3Poly bottom 1 4 5
  - minor3Poly top 0 2 4 * minor3Poly bottom 1 3 5
  + minor3Poly top 0 2 5 * minor3Poly bottom 1 3 4
  + minor3Poly top 0 3 4 * minor3Poly bottom 1 2 5
  - minor3Poly top 0 3 5 * minor3Poly bottom 1 2 4
  + minor3Poly top 0 4 5 * minor3Poly bottom 1 2 3
  - minor3Poly top 1 2 3 * minor3Poly bottom 0 4 5
  + minor3Poly top 1 2 4 * minor3Poly bottom 0 3 5
  - minor3Poly top 1 2 5 * minor3Poly bottom 0 3 4
  - minor3Poly top 1 3 4 * minor3Poly bottom 0 2 5
  + minor3Poly top 1 3 5 * minor3Poly bottom 0 2 4
  - minor3Poly top 1 4 5 * minor3Poly bottom 0 2 3
  + minor3Poly top 2 3 4 * minor3Poly bottom 0 1 5
  - minor3Poly top 2 3 5 * minor3Poly bottom 0 1 4
  + minor3Poly top 2 4 5 * minor3Poly bottom 0 1 3
  - minor3Poly top 3 4 5 * minor3Poly bottom 0 1 2

theorem laplace33Polynomial_eq_grouped {R : Type*} [CommRing R]
    (top bottom : Matrix F3 F6 R) :
    laplace33Polynomial top bottom = laplace33Grouped top bottom := by
  simp only [laplace33Polynomial, laplace33Grouped,
    minor3Poly_eq_minor3]

/-- Computational presentation of one last-row coefficient. -/
def fastLastRowCoefficient (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (j : F6) : ℤ :=
  laplace33Polynomial top (bottomOfRows u v (basisRow j))

theorem fastLastRowCoefficient_eq (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) (j : F6) :
    fastLastRowCoefficient top u v j =
      lastRowCoefficient top u v j := by
  unfold fastLastRowCoefficient lastRowCoefficient
  exact laplace33Polynomial_eq_grouped _ _

def fastNegativeCoefficientSum (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) : ℤ :=
  ∑ j : F6, min (fastLastRowCoefficient top u v j) 0

def fastPositiveCoefficientSum (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) : ℤ :=
  ∑ j : F6, max (fastLastRowCoefficient top u v j) 0

theorem fastNegativeCoefficientSum_eq (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) :
    fastNegativeCoefficientSum top u v =
      negativeCoefficientSum top u v := by
  unfold fastNegativeCoefficientSum negativeCoefficientSum
  simp only [fastLastRowCoefficient_eq]

theorem fastPositiveCoefficientSum_eq (top : Matrix F3 F6 ℤ)
    (u v : BinaryRow) :
    fastPositiveCoefficientSum top u v =
      positiveCoefficientSum top u v := by
  unfold fastPositiveCoefficientSum positiveCoefficientSum
  simp only [fastLastRowCoefficient_eq]

/-- A natural row code, used only for low-overhead closed computation. -/
def rowOfNat (code : ℕ) : BinaryRow := fun j => code.testBit j

@[simp] theorem rowOfBits_eq_rowOfNat (b : BitVec 6) :
    rowOfBits b = rowOfNat b.toNat := by
  rfl

/-- Cheap numerical form of `PairReducedBound`. -/
def FastPairBound (top : Matrix F3 F6 ℤ)
    (a b B : ℕ) : Prop :=
  (-(B : ℤ) ≤ fastNegativeCoefficientSum top (rowOfNat a) (rowOfNat b)) ∧
    (fastPositiveCoefficientSum top (rowOfNat a) (rowOfNat b) ≤ (B : ℤ))

instance (top : Matrix F3 F6 ℤ) (a b B : ℕ) :
    Decidable (FastPairBound top a b B) := by
  unfold FastPairBound
  infer_instance

/-- The fast predicate proves the original semantic pair certificate. -/
theorem FastPairBound.toPairReducedBound
    {top : Matrix F3 F6 ℤ} {a b B : ℕ}
    (h : FastPairBound top a b B) :
    PairReducedBound top (rowOfNat a) (rowOfNat b) B := by
  unfold FastPairBound at h
  unfold PairReducedBound
  simpa only [fastNegativeCoefficientSum_eq,
    fastPositiveCoefficientSum_eq] using h

/-- A bounded contiguous batch of closed pair calculations.  Numerical
modules use batches of at most sixteen, which stay below the default kernel
recursion limit even for dense top blocks. -/
def FastPairChunk (top : Matrix F3 F6 ℤ)
    (a start count B : ℕ) : Prop :=
  (List.range' start count).Forall fun b => FastPairBound top a b B

instance (top : Matrix F3 F6 ℤ) (a start count B : ℕ) :
    Decidable (FastPairChunk top a start count B) := by
  unfold FastPairChunk
  infer_instance

/-- One triangular row-code slice.  Sharding at this boundary makes resource
usage explicit: a slice contains at most 64 closed pair calculations. -/
def FastRowSlice (top : Matrix F3 F6 ℤ) (a B : ℕ) : Prop :=
  (List.range' a (64 - a)).Forall fun b => FastPairBound top a b B

instance (top : Matrix F3 F6 ℤ) (a B : ℕ) :
    Decidable (FastRowSlice top a B) := by
  unfold FastRowSlice
  infer_instance

/-- All 64 triangular slices, still expressed as a compact executable list. -/
def FastTriangularTable (top : Matrix F3 F6 ℤ) (B : ℕ) : Prop :=
  (List.range 64).Forall fun a => FastRowSlice top a B

instance (top : Matrix F3 F6 ℤ) (B : ℕ) :
    Decidable (FastTriangularTable top B) := by
  unfold FastTriangularTable
  infer_instance

/-- A checked fast table covers every ordered pair of six-bit rows.  The only
index reasoning here is membership in `range 64` and `range' a (64-a)`; all
determinant content has already crossed through `FastPairBound.toPairReducedBound`. -/
theorem FastTriangularTable.toTriangularCertificate
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : FastTriangularTable top B) : TriangularCertificate top B := by
  intro a b hab
  have haLt : a.toNat < 64 := by
    simpa using a.isLt
  have hbLt : b.toNat < 64 := by
    simpa using b.isLt
  have haMem : a.toNat ∈ List.range 64 := List.mem_range.mpr haLt
  have hslice : FastRowSlice top a.toNat B :=
    (List.forall_iff_forall_mem.mp h) a.toNat haMem
  have hbMem : b.toNat ∈ List.range' a.toNat (64 - a.toNat) := by
    rw [MainTheory.OuterCompleteness.mem_range'_one_iff]
    omega
  have hfast : FastPairBound top a.toNat b.toNat B :=
    (List.forall_iff_forall_mem.mp hslice) b.toNat hbMem
  simpa only [rowOfBits_eq_rowOfNat] using hfast.toPairReducedBound

/-- Semantic reduced bound obtained from the compact executable table. -/
theorem FastTriangularTable.reducedBound
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : FastTriangularTable top B) : ReducedBound top B :=
  h.toTriangularCertificate.reducedBound

end MainTheory.BinaryDetFast
