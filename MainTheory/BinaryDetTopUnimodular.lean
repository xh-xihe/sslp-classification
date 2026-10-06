import MainTheory.BinaryDetSymmetry

/-!
# Unimodular operations on the fixed top block

The numerical determinant certificates fix the first three rows and quantify
over all binary choices for the last three rows.  This file transports such a
certificate through the two elementary integral row operations which, together
with the row swaps from `BinaryDetSymmetry`, generate the unimodular changes of
basis on the fixed top block:

* multiply one top row by `-1`;
* add an integral multiple of one top row to a different top row.

The proofs use the ordinary `Matrix.det` API.  No evaluator-specific reduction
or generated numerical table is involved.
-/

namespace MainTheory.BinaryDetSymmetry

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor

/-! ## Operations on the `3 x 6` top block -/

/-- Multiply one of the three fixed top rows by `-1`. -/
def negateTopRow (top : Matrix F3 F6 ℤ) (i : F3) : Matrix F3 F6 ℤ :=
  Matrix.updateRow top i ((-1 : ℤ) • top i)

/-- Replace `target` by `target + c * source` in the fixed top block.
The determinant transport theorem below assumes that the two rows differ. -/
def addTopRowMultiple (top : Matrix F3 F6 ℤ)
    (target source : F3) (c : ℤ) : Matrix F3 F6 ℤ :=
  Matrix.updateRow top target (top target + c • top source)

theorem includeTopRow_injective : Function.Injective includeTopRow := by
  intro i j hij
  apply Fin.ext
  simpa [includeTopRow] using congrArg Fin.val hij

/-! ## Compatibility with the full stacked matrix -/

theorem stack3x3_negateTopRow
    (top : Matrix F3 F6 ℤ) (i : F3) (u v w : BinaryRow) :
    stack3x3 (negateTopRow top i) (bottomOfRows u v w) =
      Matrix.updateRow (stack3x3 top (bottomOfRows u v w))
        (includeTopRow i)
        ((-1 : ℤ) •
          (stack3x3 top (bottomOfRows u v w)) (includeTopRow i)) := by
  ext r j
  fin_cases i <;> fin_cases r <;>
    simp [negateTopRow, stack3x3, bottomOfRows, includeTopRow,
      Matrix.updateRow_apply]

theorem stack3x3_addTopRowMultiple
    (top : Matrix F3 F6 ℤ) (target source : F3) (c : ℤ)
    (u v w : BinaryRow) :
    stack3x3 (addTopRowMultiple top target source c) (bottomOfRows u v w) =
      Matrix.updateRow (stack3x3 top (bottomOfRows u v w))
        (includeTopRow target)
        ((stack3x3 top (bottomOfRows u v w)) (includeTopRow target) +
          c • (stack3x3 top (bottomOfRows u v w)) (includeTopRow source)) := by
  ext r j
  fin_cases target <;> fin_cases source <;> fin_cases r <;>
    simp [addTopRowMultiple, stack3x3, bottomOfRows, includeTopRow,
      Matrix.updateRow_apply]

/-! ## Transport of universal determinant bounds -/

/-- Negating any fixed top row preserves an absolute determinant bound. -/
theorem BottomDetBound.negateTopRow
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : BottomDetBound top B) (i : F3) :
    BottomDetBound (negateTopRow top i) B := by
  intro u v w
  rw [stack3x3_negateTopRow]
  let M := stack3x3 top (bottomOfRows u v w)
  calc
    (Matrix.updateRow M (includeTopRow i)
        ((-1 : ℤ) • M (includeTopRow i))).det.natAbs =
        ((-1 : ℤ) * M.det).natAbs := by
      have hdet := Matrix.det_updateRow_smul M (includeTopRow i) (-1)
        (M (includeTopRow i))
      rw [Matrix.updateRow_eq_self] at hdet
      exact congrArg Int.natAbs hdet
    _ = M.det.natAbs := by simp
    _ ≤ B := h u v w

/-- Adding an integral multiple of one fixed top row to a different fixed top
row preserves an absolute determinant bound. -/
theorem BottomDetBound.addTopRowMultiple
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : BottomDetBound top B) (target source : F3)
    (hts : target ≠ source) (c : ℤ) :
    BottomDetBound (addTopRowMultiple top target source c) B := by
  intro u v w
  rw [stack3x3_addTopRowMultiple]
  let M := stack3x3 top (bottomOfRows u v w)
  have hfull : includeTopRow target ≠ includeTopRow source :=
    includeTopRow_injective.ne hts
  calc
    (Matrix.updateRow M (includeTopRow target)
        (M (includeTopRow target) +
          c • M (includeTopRow source))).det.natAbs = M.det.natAbs := by
      exact congrArg Int.natAbs
        (Matrix.det_updateRow_add_smul_self M hfull c)
    _ ≤ B := h u v w

/-! ## Direct unimodular changes of basis

For generated classification data it is substantially simpler to certify one
explicit `3 x 3` matrix than to record a decomposition into elementary row
operations.  The following interface packages that direct certificate. -/

/-- Left multiplication applies an integral change of basis to the three
fixed top rows. -/
def transformTopRows (U : Matrix F3 F3 ℤ) (top : Matrix F3 F6 ℤ) :
    Matrix F3 F6 ℤ :=
  U * top

/-- Extend a `3 x 3` top-row transformation by the identity on the three
universally quantified bottom rows. -/
def liftTopMatrix (U : Matrix F3 F3 ℤ) : Matrix F6 F6 ℤ :=
  Matrix.reindex
    (finSumFinEquiv : F3 ⊕ F3 ≃ F6)
    (finSumFinEquiv : F3 ⊕ F3 ≃ F6)
    (Matrix.fromBlocks U 0 0 1)

/-- Acting on the fixed top block is the same as left multiplying the full
stacked matrix by the block-diagonal lift of the action. -/
private theorem stack3x3_eq_reindex_fromRows
    (top bottom : Matrix F3 F6 ℤ) :
    stack3x3 top bottom =
      Matrix.reindex
        (finSumFinEquiv : F3 ⊕ F3 ≃ F6)
        (Equiv.refl F6)
        (Matrix.fromRows top bottom) := by
  apply (Matrix.reindex
    (finSumFinEquiv : F3 ⊕ F3 ≃ F6).symm
    (Equiv.refl F6)).injective
  ext i j
  rcases i with i | i
  · fin_cases i <;>
      simp [Matrix.reindex_apply, stack3x3, finSumFinEquiv, Fin.addCases]
  · fin_cases i <;>
      simp [Matrix.reindex_apply, stack3x3, finSumFinEquiv, Fin.addCases]

theorem stack3x3_transformTopRows
    (U : Matrix F3 F3 ℤ) (top : Matrix F3 F6 ℤ)
    (u v w : BinaryRow) :
    stack3x3 (transformTopRows U top) (bottomOfRows u v w) =
      liftTopMatrix U * stack3x3 top (bottomOfRows u v w) := by
  rw [stack3x3_eq_reindex_fromRows, stack3x3_eq_reindex_fromRows]
  let e : F3 ⊕ F3 ≃ F6 := finSumFinEquiv
  let D : Matrix (F3 ⊕ F3) (F3 ⊕ F3) ℤ :=
    Matrix.fromBlocks U 0 0 1
  let S : Matrix (F3 ⊕ F3) F6 ℤ :=
    Matrix.fromRows top (bottomOfRows u v w)
  change Matrix.reindex e (Equiv.refl F6)
      (Matrix.fromRows (U * top) (bottomOfRows u v w)) =
    Matrix.reindex e e D * Matrix.reindex e (Equiv.refl F6) S
  calc
    Matrix.reindex e (Equiv.refl F6)
        (Matrix.fromRows (U * top) (bottomOfRows u v w)) =
        Matrix.reindex e (Equiv.refl F6) (D * S) := by
      congr 1
      simp [D, S, Matrix.fromBlocks_mul_fromRows]
    _ = Matrix.reindex e e D * Matrix.reindex e (Equiv.refl F6) S := by
      exact (Matrix.reindexLinearEquiv_mul ℤ ℤ e e (Equiv.refl F6) D S).symm

/-- The block-diagonal lift has the same determinant as its top block. -/
theorem liftTopMatrix_det (U : Matrix F3 F3 ℤ) :
    (liftTopMatrix U).det = U.det := by
  unfold liftTopMatrix
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- A direct integral top-row transformation with determinant `±1`
preserves every universal absolute determinant bound. -/
theorem BottomDetBound.transformTopRows
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : BottomDetBound top B) (U : Matrix F3 F3 ℤ)
    (hU : U.det.natAbs = 1) :
    BottomDetBound (transformTopRows U top) B := by
  intro u v w
  rw [stack3x3_transformTopRows, Matrix.det_mul, liftTopMatrix_det,
    Int.natAbs_mul, hU, one_mul]
  exact h u v w

/-! ## Singular top blocks

If the three fixed rows already satisfy a nontrivial integral relation, every
completion by three bottom rows is singular.  Recording the relation itself is
a smaller and more transparent certificate than reducing it to a zero row by
a sequence of generated elementary operations. -/

/-- A concrete nontrivial integral linear relation among the fixed top rows. -/
def TopRowRelation (top : Matrix F3 F6 ℤ) (c : F3 → ℤ) : Prop :=
  (∑ i : F3, c i • top i) = 0 ∧ ∃ i, c i ≠ 0

/-- Extend the coefficients of a top-row relation by zero on the bottom
three rows. -/
def extendTopCoefficients (c : F3 → ℤ) (i : F6) : ℤ :=
  if h : (i : ℕ) < 3 then c ⟨i, h⟩ else 0

/-- A nontrivial relation among the fixed top rows forces all completed
determinants to vanish, and hence proves a bound by any natural number `B`. -/
theorem BottomDetBound.ofTopRowRelation
    {top : Matrix F3 F6 ℤ} {B : ℕ} {c : F3 → ℤ}
    (hrel : TopRowRelation top c) : BottomDetBound top B := by
  intro u v w
  let M := stack3x3 top (bottomOfRows u v w)
  have hsum :
      (∑ i : F6, extendTopCoefficients c i • M i) = 0 := by
    apply funext
    intro j
    have hj := congrFun hrel.1 j
    simpa [M, extendTopCoefficients, stack3x3, bottomOfRows,
      Fin.sum_univ_succ] using hj
  have hnonzero : ∃ i : F6, extendTopCoefficients c i ≠ 0 := by
    obtain ⟨i, hi⟩ := hrel.2
    refine ⟨includeTopRow i, ?_⟩
    simpa [extendTopCoefficients, includeTopRow] using hi
  have hdependent : ¬ LinearIndependent ℤ (fun i : F6 ↦ M i) := by
    exact Fintype.not_linearIndependent_iff.mpr
      ⟨extendTopCoefficients c, hsum, hnonzero⟩
  have hdet : M.det = 0 :=
    Matrix.det_eq_zero_of_not_linearIndependent_rows hdependent
  rw [show (stack3x3 top (bottomOfRows u v w)).det = 0 by simpa [M] using hdet]
  simp

/-- Convenient special case: a zero fixed top row makes every completion
singular. -/
theorem BottomDetBound.ofZeroTopRow
    {top : Matrix F3 F6 ℤ} {B : ℕ} (i : F3)
    (hi : ∀ j, top i j = 0) : BottomDetBound top B := by
  intro u v w
  have hdet : (stack3x3 top (bottomOfRows u v w)).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (includeTopRow i)
    intro j
    simpa [stack3x3, includeTopRow] using hi j
  rw [hdet]
  simp

end MainTheory.BinaryDetSymmetry
