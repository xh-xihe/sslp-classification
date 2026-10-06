import MainTheory.BinaryBeta

/-!
# Generic last-row reduction for binary determinant certificates

This is the size-independent version of the cofactor envelope used by the
six-by-six circuit.  A numerical leaf fixes every row except one and checks
only the sum of negative and positive cofactors.  The remaining binary row is
then discharged by ordinary determinant linearity.

The definitions remain over `Int`; there is no signed-bit-vector overflow
assumption in this bridge.
-/

namespace MainTheory.BinaryDetLastRow

open scoped BigOperators
open MainTheory.BinaryBeta

/-- Embed one Boolean entry in the integers. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- Integer standard basis row. -/
def integerBasisRow {n : Type*} [DecidableEq n] (j : n) : n → ℤ :=
  fun k ↦ if k = j then 1 else 0

theorem row_eq_sum_basis {n : Type*} [Fintype n] [DecidableEq n]
    (r : n → ℤ) :
    r = ∑ j : n, r j • integerBasisRow j := by
  funext k
  simp [integerBasisRow]

/-- Erase the distinguished row before taking its cofactors. -/
def zeroRowMatrix {n : Type*} [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) : Matrix n n ℤ :=
  M.updateRow i 0

theorem updateRow_zeroRowMatrix {n : Type*} [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (r : n → ℤ) :
    (zeroRowMatrix M i).updateRow i r = M.updateRow i r := by
  ext k j
  by_cases h : k = i
  · subst k
    simp [zeroRowMatrix, Matrix.updateRow]
  · simp [zeroRowMatrix, Matrix.updateRow, h]

/-- Cofactor of one entry in the distinguished row, defined by evaluation on
the corresponding standard basis vector. -/
def coefficient {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i j : n) : ℤ :=
  ((zeroRowMatrix M i).updateRow i (integerBasisRow j)).det

/-- The determinant's linear form in the distinguished row. -/
def rowLinearForm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (r : n → ℤ) : ℤ :=
  ∑ j : n, r j * coefficient M i j

private theorem det_updateRow_sum_finset
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (g : n → n → ℤ) (s : Finset n) :
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

private theorem det_updateRow_sum_univ
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (g : n → n → ℤ) :
    (M.updateRow i (∑ j : n, g j)).det =
      ∑ j : n, (M.updateRow i (g j)).det :=
  det_updateRow_sum_finset M i g Finset.univ

/-- Determinant linearity in one row, with no hypothesis on the old value of
that row. -/
theorem det_updateRow_eq_rowLinearForm
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (r : n → ℤ) :
    (M.updateRow i r).det = rowLinearForm M i r := by
  rw [← updateRow_zeroRowMatrix M i r]
  calc
    ((zeroRowMatrix M i).updateRow i r).det =
        ((zeroRowMatrix M i).updateRow i
          (∑ j : n, r j • integerBasisRow j)).det := by
      exact congrArg
        (fun row => ((zeroRowMatrix M i).updateRow i row).det)
        (row_eq_sum_basis r)
    _ = ∑ j : n,
        ((zeroRowMatrix M i).updateRow i
          (r j • integerBasisRow j)).det :=
      det_updateRow_sum_univ _ _ _
    _ = rowLinearForm M i r := by
      unfold rowLinearForm coefficient
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.det_updateRow_smul]

def negativeCoefficientSum
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) : ℤ :=
  ∑ j : n, min (coefficient M i j) 0

def positiveCoefficientSum
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) : ℤ :=
  ∑ j : n, max (coefficient M i j) 0

private theorem min_le_bitZ_mul (b : Bool) (z : ℤ) :
    min z 0 ≤ bitZ b * z := by
  cases b <;> simp [bitZ]

private theorem bitZ_mul_le_max (b : Bool) (z : ℤ) :
    bitZ b * z ≤ max z 0 := by
  cases b <;> simp [bitZ]

theorem rowLinearForm_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (r : n → Bool) :
    negativeCoefficientSum M i ≤
        rowLinearForm M i (fun j ↦ bitZ (r j)) ∧
      rowLinearForm M i (fun j ↦ bitZ (r j)) ≤
        positiveCoefficientSum M i := by
  constructor
  · apply Finset.sum_le_sum
    intro j _
    exact min_le_bitZ_mul (r j) (coefficient M i j)
  · apply Finset.sum_le_sum
    intro j _
    exact bitZ_mul_le_max (r j) (coefficient M i j)

/-- Closed certificate predicate after every row except `i` has been fixed. -/
def ReducedAtRow
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (B : ℕ) : Prop :=
  (-(B : ℤ) ≤ negativeCoefficientSum M i) ∧
    (positiveCoefficientSum M i ≤ (B : ℤ))

instance reducedAtRowDecidable
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) (i : n) (B : ℕ) :
    Decidable (ReducedAtRow M i B) := by
  unfold ReducedAtRow
  infer_instance

private theorem natAbs_le_of_bounds {x : ℤ} {B : ℕ}
    (hlower : -(B : ℤ) ≤ x) (hupper : x ≤ (B : ℤ)) :
    x.natAbs ≤ B := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact (abs_le).2 ⟨hlower, hupper⟩

/-- A closed cofactor-envelope certificate covers every Boolean value of the
distinguished row. -/
theorem ReducedAtRow.detNatAbs_updateRow
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℤ} {i : n} {B : ℕ}
    (h : ReducedAtRow M i B) (r : n → Bool) :
    (M.updateRow i (fun j ↦ bitZ (r j))).det.natAbs ≤ B := by
  have henvelope := rowLinearForm_bounds M i r
  apply natAbs_le_of_bounds
  · calc
      -(B : ℤ) ≤ negativeCoefficientSum M i := h.1
      _ ≤ rowLinearForm M i (fun j ↦ bitZ (r j)) := henvelope.1
      _ = (M.updateRow i (fun j ↦ bitZ (r j))).det :=
        (det_updateRow_eq_rowLinearForm M i _).symm
  · calc
      (M.updateRow i (fun j ↦ bitZ (r j))).det =
          rowLinearForm M i (fun j ↦ bitZ (r j)) :=
        det_updateRow_eq_rowLinearForm M i _
      _ ≤ positiveCoefficientSum M i := henvelope.2
      _ ≤ (B : ℤ) := h.2

/-! ## Boolean-matrix and semantic-beta bridges -/

def intMatrixOfBool {n : Type*} (A : Matrix n n Bool) : Matrix n n ℤ :=
  fun i j ↦ bitZ (A i j)

theorem intMatrixOfBool_isZeroOne {n : Type*} (A : Matrix n n Bool) :
    IsZeroOne (intMatrixOfBool A) := by
  intro i j
  cases A i j <;> simp [intMatrixOfBool, bitZ]

def boolMatrixOfZeroOne {n : Type*} (C : Matrix n n ℤ) :
    Matrix n n Bool :=
  fun i j ↦ C i j == 1

theorem intMatrixOfBool_boolMatrixOfZeroOne
    {n : Type*} (C : Matrix n n ℤ) (hC : IsZeroOne C) :
    intMatrixOfBool (boolMatrixOfZeroOne C) = C := by
  ext i j
  rcases hC i j with h | h <;> simp [intMatrixOfBool,
    boolMatrixOfZeroOne, bitZ, h]

/-- It is enough to bound the determinants of Boolean matrices at the single
top size.  This packages both the Boolean/Int transcription and identity
padding used by `BinaryBeta.betaBound_of_fixedSize_detNatAbs_bound`. -/
theorem betaBound_of_bool_detNatAbs_bound {N B : ℕ}
    (hbound : ∀ A : Matrix (Fin N) (Fin N) Bool,
      (intMatrixOfBool A).det.natAbs ≤ B) :
    BetaBound N B := by
  apply betaBound_of_fixedSize_detNatAbs_bound
  intro C hC _hdet
  rw [← intMatrixOfBool_boolMatrixOfZeroOne C hC]
  exact hbound (boolMatrixOfZeroOne C)

/-! ## Compact row codes used by generated finite certificates -/

def rowOfBits {n : ℕ} (b : BitVec n) : Fin n → Bool :=
  fun j ↦ b.getLsb j

@[simp] theorem rowOfBits_ofFnLE {n : ℕ} (r : Fin n → Bool) :
    rowOfBits (BitVec.ofFnLE r) = r := by
  funext j
  simp [rowOfBits]

def intMatrixOfRowBits {n : ℕ} (rows : Fin n → BitVec n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ bitZ (rowOfBits (rows i) j)

theorem intMatrixOfRowBits_ofFnLE {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Bool) :
    intMatrixOfRowBits (fun i ↦ BitVec.ofFnLE (A i)) = intMatrixOfBool A := by
  ext i j
  simp [intMatrixOfRowBits, intMatrixOfBool, rowOfBits]

/-! ## Prefix-certificate endpoint for a fixed matrix size -/

/-- Erase the last encoded row.  Generated arithmetic may leave the
corresponding entry of `rows` arbitrary; it cannot affect this matrix. -/
def prefixMatrix {n : ℕ} (rows : Fin (n + 1) → BitVec (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  intMatrixOfRowBits (Function.update rows (Fin.last n) 0)

/-- Complete finite-certificate endpoint at size `n+1`. -/
def AllPrefixReducedBound (n B : ℕ) : Prop :=
  ∀ rows : Fin (n + 1) → BitVec (n + 1),
    ReducedAtRow (prefixMatrix rows) (Fin.last n) B

private theorem prefixMatrix_update_last
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Bool) :
    (prefixMatrix (fun i ↦ BitVec.ofFnLE (A i))).updateRow (Fin.last n)
        (fun j ↦ bitZ (A (Fin.last n) j)) =
      intMatrixOfBool A := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst i
    simp [prefixMatrix, intMatrixOfBool, Matrix.updateRow]
  · simp [prefixMatrix, intMatrixOfRowBits, intMatrixOfBool, rowOfBits,
      Matrix.updateRow, hi]

/-- A complete collection of last-row prefix envelopes gives the universal
semantic beta bound at that size (and, by identity padding, all smaller
sizes). -/
theorem betaBound_of_allPrefixReducedBound {n B : ℕ}
    (h : AllPrefixReducedBound n B) : BetaBound (n + 1) B := by
  apply betaBound_of_bool_detNatAbs_bound
  intro A
  let rows : Fin (n + 1) → BitVec (n + 1) :=
    fun i ↦ BitVec.ofFnLE (A i)
  have hp := (h rows).detNatAbs_updateRow (fun j ↦ A (Fin.last n) j)
  rw [show prefixMatrix rows =
      prefixMatrix (fun i ↦ BitVec.ofFnLE (A i)) by rfl] at hp
  rw [prefixMatrix_update_last A] at hp
  exact hp

end MainTheory.BinaryDetLastRow
