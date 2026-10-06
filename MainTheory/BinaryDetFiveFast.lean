import MainTheory.BinaryBetaSmallSemantic

/-!
# Low-overhead integer certificates for the five-by-five beta bound

The semantic endpoint for size five is still
`BinaryDetLastRow.ReducedAtRow`.  Reducing its five generic `Matrix.det`
cofactors separately in each of the 52,360 sorted prefixes is needlessly
expensive, however.  This file gives the same cofactors a small executable
presentation:

* the four fixed rows are represented by natural row codes;
* a cofactor is the signed determinant of the corresponding `4 x 4` minor;
* that minor is evaluated by one explicit Laplace row and four explicit
  six-monomial `3 x 3` polynomials.

All arithmetic remains in `Int`.  The polynomial is proved equal to
`Matrix.det` once, and `FastPrefixBound.toReducedAtRow` transports every
checked numerical result back to the original determinant semantics.  Thus
neither the row-code presentation nor the fast polynomial is trusted.
-/

namespace MainTheory.BinaryDetFiveFast

open scoped BigOperators
open MainTheory.BinaryDetLastRow
open MainTheory.BinaryBetaSmallSemantic

abbrev F3 := Fin 3
abbrev F4 := Fin 4
abbrev F5 := Fin 5

/-! ## Explicit small determinant polynomials -/

/-- The ordinary six-monomial determinant polynomial for a `3 x 3` matrix. -/
def det3Poly {R : Type*} [CommRing R] (A : Matrix F3 F3 R) : R :=
    A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
  - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
  + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

theorem det3Poly_eq_det {R : Type*} [CommRing R]
    (A : Matrix F3 F3 R) : det3Poly A = A.det := by
  rw [Matrix.det_fin_three]
  rfl

/-- A `4 x 4` determinant evaluated by one Laplace row whose four minors use
`det3Poly`.  This is the complete arithmetic circuit used by the leaves. -/
def det4Poly {R : Type*} [CommRing R] (A : Matrix F4 F4 R) : R :=
    A 0 0 * det3Poly (A.submatrix Fin.succ (0 : F4).succAbove)
  - A 0 1 * det3Poly (A.submatrix Fin.succ (1 : F4).succAbove)
  + A 0 2 * det3Poly (A.submatrix Fin.succ (2 : F4).succAbove)
  - A 0 3 * det3Poly (A.submatrix Fin.succ (3 : F4).succAbove)

/-- The cheap circuit is exactly the ordinary determinant. -/
theorem det4Poly_eq_det {R : Type*} [CommRing R]
    (A : Matrix F4 F4 R) : det4Poly A = A.det := by
  rw [Matrix.det_succ_row_zero]
  simp [det4Poly, det3Poly_eq_det, Fin.sum_univ_succ]; ring

/-! ## Natural row codes and the semantic cofactor bridge -/

/-- Five low bits of a natural number, in the same least-significant-bit
convention as `BinaryDetLastRow.rowOfBits`. -/
def rowOfNat (code : Nat) : F5 -> Bool := fun j => code.testBit j

@[simp] theorem rowOfBits_eq_rowOfNat (b : BitVec 5) :
    MainTheory.BinaryDetLastRow.rowOfBits b = rowOfNat b.toNat := by
  rfl

/-- The four fixed binary rows decoded directly from natural row codes. -/
def topOfCodes (codes : F4 -> Nat) : Matrix F4 F5 Int :=
  fun i j => bitZ (rowOfNat (codes i) j)

/-- The corresponding five-row prefix matrix, with its distinguished final
row zeroed exactly as in `prefixRowsMatrix`. -/
def natPrefixMatrix (codes : F4 -> Nat) : Matrix F5 F5 Int :=
  fun i j => Fin.lastCases 0 (fun k => topOfCodes codes k j) i

/-- The `4 x 4` minor obtained by deleting column `j`. -/
def cofactorMinor (codes : F4 -> Nat) (j : F5) : Matrix F4 F4 Int :=
  fun r c => topOfCodes codes r (j.succAbove c)

/-- Computational presentation of the final-row coefficient. -/
def fastCoefficient (codes : F4 -> Nat) (j : F5) : Int :=
  (-1 : Int) ^ (4 + (j : Nat)) * det4Poly (cofactorMinor codes j)

private theorem basisSubmatrix_eq_cofactorMinor
    (codes : F4 -> Nat) (j : F5) :
    (((zeroRowMatrix (natPrefixMatrix codes) (Fin.last 4)).updateRow
          (Fin.last 4) (integerBasisRow j)).submatrix
        (Fin.last 4).succAbove j.succAbove) =
      cofactorMinor codes j := by
  ext r c
  simp [zeroRowMatrix, Matrix.updateRow, natPrefixMatrix,
    cofactorMinor, topOfCodes]
  change Fin.lastCases 0
      (fun k => bitZ (rowOfNat (codes k) (j.succAbove c)))
      ((Fin.last 4).succAbove r) =
    bitZ (rowOfNat (codes r) (j.succAbove c))
  rw [Fin.succAbove_last_apply, Fin.lastCases_castSucc]

/-- The explicit polynomial computes the coefficient used by the generic
last-row theorem, not merely a parallel unchecked formula. -/
theorem fastCoefficient_eq_coefficient (codes : F4 -> Nat) (j : F5) :
    fastCoefficient codes j =
      coefficient (natPrefixMatrix codes) (Fin.last 4) j := by
  classical
  unfold coefficient
  rw [Matrix.det_succ_row _ (Fin.last 4)]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (by
    intro k _ hkj
    simp [Matrix.updateRow, integerBasisRow, hkj])]
  rw [basisSubmatrix_eq_cofactorMinor]
  simp [fastCoefficient, det4Poly_eq_det, Matrix.updateRow, integerBasisRow]

def fastNegativeSum (codes : F4 -> Nat) : Int :=
  ∑ j : F5, min (fastCoefficient codes j) 0

def fastPositiveSum (codes : F4 -> Nat) : Int :=
  ∑ j : F5, max (fastCoefficient codes j) 0

/-- Low-overhead numerical form of one size-five prefix envelope. -/
def FastPrefixBound (codes : F4 -> Nat) (B : Nat) : Prop :=
  (-(B : Int) <= fastNegativeSum codes) /\
    (fastPositiveSum codes <= (B : Int))

instance (codes : F4 -> Nat) (B : Nat) :
    Decidable (FastPrefixBound codes B) := by
  unfold FastPrefixBound
  infer_instance

/-- A checked fast prefix is the original semantic `ReducedAtRow` statement
for the direct natural-code matrix. -/
theorem FastPrefixBound.toReducedAtRow
    {codes : F4 -> Nat} {B : Nat} (h : FastPrefixBound codes B) :
    ReducedAtRow (natPrefixMatrix codes) (Fin.last 4) B := by
  unfold FastPrefixBound fastNegativeSum fastPositiveSum at h
  unfold ReducedAtRow negativeCoefficientSum positiveCoefficientSum
  simpa only [fastCoefficient_eq_coefficient] using h

/-- Bit-vector prefixes and natural-code prefixes denote the same integer
matrix.  This prevents the fast leaves from bypassing the authoritative row
decoder used by `BinaryBetaSmallSemantic`. -/
theorem prefixRowsMatrix_eq_natPrefixMatrix (f : F4 -> BitVec 5) :
    prefixRowsMatrix f = natPrefixMatrix (fun i => (f i).toNat) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · change bitZ (MainTheory.BinaryDetLastRow.rowOfBits (0#5) j) = 0
    simp [MainTheory.BinaryDetLastRow.rowOfBits, bitZ]
  · simp only [prefixRowsMatrix, intMatrixOfRowBits, Fin.lastCases_castSucc,
      natPrefixMatrix, topOfCodes]
    rw [rowOfBits_eq_rowOfNat]

/-- Kernel-checked natural-code arithmetic reaches the exact sorted-prefix
endpoint consumed by `betaBound_of_monotonePrefixCertificate`. -/
theorem FastPrefixBound.toReducedAtRowBits
    {f : F4 -> BitVec 5} {B : Nat}
    (h : FastPrefixBound (fun i => (f i).toNat) B) :
    ReducedAtRow (prefixRowsMatrix f) (Fin.last 4) B := by
  rw [prefixRowsMatrix_eq_natPrefixMatrix]
  exact h.toReducedAtRow

/-! ## Resource-bounded slices -/

/-- Fix the first three monotone row codes and check every possible final
code from `c` through `31`.  One slice contains at most 32 cheap integer
calculations, so generated modules can stay small without returning to a
matrix-heavy certificate for every tuple. -/
def FastLastCodeSlice (a b c B : Nat) : Prop :=
  (List.range' c (32 - c)).Forall fun d =>
    FastPrefixBound ![a, b, c, d] B

instance (a b c B : Nat) : Decidable (FastLastCodeSlice a b c B) := by
  unfold FastLastCodeSlice
  infer_instance

/-- Extract one semantic-free numerical prefix from a checked slice. -/
theorem FastLastCodeSlice.lookup
    {a b c B d : Nat} (h : FastLastCodeSlice a b c B)
    (hcd : c <= d) (hd : d < 32) :
    FastPrefixBound ![a, b, c, d] B := by
  apply (List.forall_iff_forall_mem.mp h) d
  rw [MainTheory.OuterCompleteness.mem_range'_one_iff]
  omega

end MainTheory.BinaryDetFiveFast
