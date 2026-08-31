import MainTheory.BinaryBeta
import MainTheory.OuterCompleteness

/-!
# A resource-bounded determinant circuit for binary `6 x 6` matrices

The first three rows of a binary matrix determine one of eight column
patterns.  Up to a column permutation, the six patterns form one of the 1716
weakly increasing six-tuples in `OuterEnumeration.weakAngles6 8`.  Once that
tuple is fixed, only the bottom 18 bits remain universally quantified.

This file contains no claimed `BetaExact 6 9` theorem.  It supplies the
kernel-facing reduction used by the future finite certificates:

* an executable Laplace expansion that stops after three rows;
* the corresponding 20-term, `3+3` grouped circuit;
* a proof that the grouped circuit is the ordinary determinant;
* the canonical 1716-index and its existing permutation-completeness bridge.

No external generator is trusted for the pattern values: `patternAt i` reads
the already verified Lean list at index `i`.
-/

namespace MainTheory.BinaryDetCircuit

open MainTheory
open MainTheory.OuterEnumeration

abbrev F3 := Fin 3
abbrev F6 := Fin 6

/-! ## A three-row-stopping Laplace expansion -/

/-- A recursive finite sum whose reduction behavior is predictable for bit
vector decision procedures. -/
def finSum {R : Type*} [AddMonoid R] : (n : ℕ) → (Fin n → R) → R
  | 0, _ => 0
  | n + 1, f => f 0 + finSum n (fun i => f i.succ)

theorem finSum_eq_sum {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : Fin n → R) : finSum n f = ∑ i, f i := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [finSum]
      rw [ih]

/-- Expand at most `fuel` leading rows, then leave the remaining determinant
as one circuit node.  Thus `splitLaplace A 3 6 id id` has three expanded rows
and a `3 x 3` determinant at every leaf. -/
def splitLaplace {i R : Type*} [CommRing R] (A : i → i → R) :
    (fuel n : ℕ) → (Fin n → i) → (Fin n → i) → R
  | 0, n, rows, cols =>
      Matrix.det
        ((fun r c => A (rows r) (cols c)) : Matrix (Fin n) (Fin n) R)
  | _ + 1, 0, _, _ => 1
  | fuel + 1, n + 1, rows, cols =>
      finSum (n + 1) fun j =>
        (-1) ^ (j : ℕ) * A (rows 0) (cols j) *
          splitLaplace A fuel n
            (fun r => rows r.succ)
            (fun c => cols (j.succAbove c))

/-- Stopping a Laplace expansion early does not change the determinant. -/
theorem splitLaplace_eq_det {i R : Type*} [CommRing R]
    (A : i → i → R) (fuel n : ℕ) (rows cols : Fin n → i) :
    splitLaplace A fuel n rows cols =
      Matrix.det
        ((fun r c => A (rows r) (cols c)) : Matrix (Fin n) (Fin n) R) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
      cases n with
      | zero => simp [splitLaplace]
      | succ n =>
          rw [Matrix.det_succ_row_zero, ← finSum_eq_sum]
          simp only [splitLaplace]
          congr 1
          funext j
          rw [ih]
          rfl

/-- The ungrouped `3+3` circuit.  It has `6 * 5 * 4 = 120` leaves, each a
`3 x 3` determinant, and is useful as a simple proof reference. -/
def laplace33Reference {R : Type*} [CommRing R]
    (A : Matrix F6 F6 R) : R :=
  splitLaplace A 3 6 id id

theorem laplace33Reference_eq_det {R : Type*} [CommRing R]
    (A : Matrix F6 F6 R) : laplace33Reference A = A.det := by
  simpa [laplace33Reference] using splitLaplace_eq_det A 3 6 id id

/-! ## The 20-term grouped circuit -/

/-- Stack a top and bottom `3 x 6` block in the natural row order. -/
def stack3x3 {R : Type*} (top bottom : Matrix F3 F6 R) : Matrix F6 F6 R :=
  fun i j =>
    if h : (i : ℕ) < 3 then
      top ⟨i, h⟩ j
    else
      bottom ⟨(i : ℕ) - 3, by omega⟩ j

/-- After the first three Laplace rows have been removed, the stacked matrix
reduces definitionally to the bottom block.  Isolating this reduction keeps
the fixed determinant normalization from carrying unresolved row conditionals. -/
@[simp] theorem stack3x3_bottom_rows {R : Type*}
    (top bottom : Matrix F3 F6 R) (i : F3) (j : F6) :
    stack3x3 top bottom i.succ.succ.succ j = bottom i j := by
  simp [stack3x3]

/-- A `3 x 3` minor of a `3 x 6` block, with columns in the displayed order. -/
def minor3 {R : Type*} [CommRing R] (A : Matrix F3 F6 R)
    (a b c : F6) : R :=
  Matrix.det ((fun i j => A i (![a, b, c] j)) : Matrix F3 F3 R)

/-- The six-monomial form of a `3 x 3` minor.  Keeping the top minor in this
form lets the generalized Laplace proof group six terms at a time while the
complementary bottom determinant remains an opaque atom. -/
def minor3Poly {R : Type*} [CommRing R] (A : Matrix F3 F6 R)
    (a b c : F6) : R :=
    A 0 a * A 1 b * A 2 c - A 0 a * A 1 c * A 2 b
  - A 0 b * A 1 a * A 2 c + A 0 b * A 1 c * A 2 a
  + A 0 c * A 1 a * A 2 b - A 0 c * A 1 b * A 2 a

theorem minor3Poly_eq_minor3 {R : Type*} [CommRing R]
    (A : Matrix F3 F6 R) (a b c : F6) :
    minor3Poly A a b c = minor3 A a b c := by
  rw [minor3, Matrix.det_fin_three]
  rfl

/-- The `3+3` generalized Laplace expansion, grouped by the 20 choices of
three top columns.  The signs are `(-1)^(3 + a + b + c)` for `a < b < c`.

For fixed top patterns, every top minor reduces to a small integer constant;
only the complementary bottom minor depends on the 18 tail bits. -/
def laplace33Grouped {R : Type*} [CommRing R]
    (top bottom : Matrix F3 F6 R) : R :=
    minor3Poly top 0 1 2 * minor3 bottom 3 4 5
  - minor3Poly top 0 1 3 * minor3 bottom 2 4 5
  + minor3Poly top 0 1 4 * minor3 bottom 2 3 5
  - minor3Poly top 0 1 5 * minor3 bottom 2 3 4
  + minor3Poly top 0 2 3 * minor3 bottom 1 4 5
  - minor3Poly top 0 2 4 * minor3 bottom 1 3 5
  + minor3Poly top 0 2 5 * minor3 bottom 1 3 4
  + minor3Poly top 0 3 4 * minor3 bottom 1 2 5
  - minor3Poly top 0 3 5 * minor3 bottom 1 2 4
  + minor3Poly top 0 4 5 * minor3 bottom 1 2 3
  - minor3Poly top 1 2 3 * minor3 bottom 0 4 5
  + minor3Poly top 1 2 4 * minor3 bottom 0 3 5
  - minor3Poly top 1 2 5 * minor3 bottom 0 3 4
  - minor3Poly top 1 3 4 * minor3 bottom 0 2 5
  + minor3Poly top 1 3 5 * minor3 bottom 0 2 4
  - minor3Poly top 1 4 5 * minor3 bottom 0 2 3
  + minor3Poly top 2 3 4 * minor3 bottom 0 1 5
  - minor3Poly top 2 3 5 * minor3 bottom 0 1 4
  + minor3Poly top 2 4 5 * minor3 bottom 0 1 3
  - minor3Poly top 3 4 5 * minor3 bottom 0 1 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- The grouped circuit is the ordinary determinant of the stacked matrix.

The proof is a fixed polynomial identity: the reference circuit expands only
three rows, while `minor3Poly` groups the six top permutations belonging to
each complementary bottom determinant.  Bottom determinants stay opaque, so
the normalizer sees 120 terms rather than expanding them to 720 monomials. -/
theorem laplace33Grouped_eq_det {R : Type*} [CommRing R]
    (top bottom : Matrix F3 F6 R) :
    laplace33Grouped top bottom = (stack3x3 top bottom).det := by
  rw [← laplace33Reference_eq_det]
  simp [laplace33Grouped, minor3Poly, minor3, Matrix.det_fin_three,
    laplace33Reference, splitLaplace, finSum, stack3x3, Fin.succAbove]
  ring

/-! ## Binary column patterns and the authoritative 1716-index -/

/-- The authoritative list of sorted six-tuples of three-bit column patterns.
It is defined in Lean rather than copied from an external generator. -/
def binaryPatterns : List Angle6 := weakAngles6 8

/-- There are `choose (8 + 6 - 1) 6 = 1716` canonical pattern tuples.  The
large list equality was already checked in `OuterEnumeration`; the remaining
closed arithmetic reduction is small. -/
theorem binaryPatterns_length : binaryPatterns.length = 1716 := by
  rw [binaryPatterns, sorted_eight_list_agrees]
  decide

/-- Stable certificate indices. -/
abbrev PatternIndex := Fin 1716

/-- Read a pattern from the verified Lean enumeration. -/
def patternAt (i : PatternIndex) : Angle6 :=
  binaryPatterns.get (Fin.cast binaryPatterns_length.symm i)

theorem patternAt_mem (i : PatternIndex) : patternAt i ∈ binaryPatterns := by
  exact List.get_mem _ _

/-- Conversely, every member of the authoritative list has one of the stable
1716 indices. -/
theorem exists_patternIndex_of_mem {p : Angle6} (hp : p ∈ binaryPatterns) :
    ∃ i : PatternIndex, patternAt i = p := by
  rcases List.mem_iff_get.mp hp with ⟨j, hj⟩
  refine ⟨Fin.cast binaryPatterns_length j, ?_⟩
  unfold patternAt
  rw [Fin.leftInverse_cast binaryPatterns_length j]
  exact hj

/-- Encode the top three Boolean entries of one column, least significant row
first. -/
def columnPattern (B : Matrix F6 F6 Bool) (j : F6) : ℕ :=
    (if B 0 j then 1 else 0)
  + 2 * (if B 1 j then 1 else 0)
  + 4 * (if B 2 j then 1 else 0)

theorem columnPattern_lt_eight (B : Matrix F6 F6 Bool) (j : F6) :
    columnPattern B j < 8 := by
  unfold columnPattern
  split <;> split <;> split <;> omega

/-- Every top three-row pattern is represented after an actual column
permutation.  This is the coverage theorem behind the 1716 shards. -/
theorem exists_column_permutation_mem_binaryPatterns
    (B : Matrix F6 F6 Bool) :
    ∃ σ : Equiv.Perm F6, (columnPattern B ∘ σ) ∈ binaryPatterns := by
  exact OuterCompleteness.exists_permutation_mem_weakAngles6
    (columnPattern B) (columnPattern_lt_eight B)

/-- Index-level form of column-pattern completeness, suitable for dispatching
to generated shards. -/
theorem exists_column_permutation_patternAt
    (B : Matrix F6 F6 Bool) :
    ∃ (σ : Equiv.Perm F6) (i : PatternIndex),
      columnPattern B ∘ σ = patternAt i := by
  rcases exists_column_permutation_mem_binaryPatterns B with ⟨σ, hσ⟩
  rcases exists_patternIndex_of_mem hσ with ⟨i, hi⟩
  exact ⟨σ, i, hi.symm⟩

/-- Decode the verified pattern tuple into its top `3 x 6` zero--one block. -/
def topOfPattern {R : Type*} [Zero R] [One R]
    (p : Angle6) : Matrix F3 F6 R :=
  fun i j => if (p j).testBit (i : ℕ) then 1 else 0

/-- Decode the 18 free tail bits in row-major order. -/
def tailOfBits {R : Type*} [Zero R] [One R]
    (bits : BitVec 18) : Matrix F3 F6 R :=
  fun i j => if bits.getLsbD (6 * (i : ℕ) + (j : ℕ)) then 1 else 0

/-- The matrix represented by one canonical top pattern and an 18-bit tail. -/
def matrixOfPatternTail {R : Type*} [Zero R] [One R]
    (p : Angle6) (bits : BitVec 18) : Matrix F6 F6 R :=
  stack3x3 (topOfPattern p) (tailOfBits bits)

/-- The small certificate circuit attached to one of the 1716 pattern
indices.  Future generated shards quantify only over `bits : BitVec 18`.
This definition itself makes no determinant-bound claim. -/
def indexedDetCircuit {R : Type*} [CommRing R]
    (i : PatternIndex) (bits : BitVec 18) : R :=
  laplace33Grouped (topOfPattern (patternAt i)) (tailOfBits bits)

theorem indexedDetCircuit_eq_det {R : Type*} [CommRing R]
    (i : PatternIndex) (bits : BitVec 18) :
    indexedDetCircuit (R := R) i bits =
      (matrixOfPatternTail (R := R) (patternAt i) bits).det := by
  exact laplace33Grouped_eq_det _ _

end MainTheory.BinaryDetCircuit
