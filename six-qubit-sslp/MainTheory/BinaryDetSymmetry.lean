import MainTheory.BinaryDetCofactor

/-!
# Row and column symmetry for the binary determinant certificates

The expensive numerical table is needed only for representatives under
permutations of the three fixed top rows.  After a top-row permutation, one
ordinary column permutation restores sorted column-pattern order.  This file
proves both determinant transports independently of generated orbit data.
-/

namespace MainTheory.BinaryDetSymmetry

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor

abbrev F3 := Fin 3
abbrev F6 := Fin 6

/-- The direct determinant-bound interface, after all three bottom rows have
been universally restored by the cofactor envelope. -/
def BottomDetBound (top : Matrix F3 F6 ℤ) (B : ℕ) : Prop :=
  ∀ u v w : BinaryRow,
    (stack3x3 top (bottomOfRows u v w)).det.natAbs ≤ B

theorem ReducedBound.bottomDetBound
    {top : Matrix F3 F6 ℤ} {B : ℕ} (h : ReducedBound top B) :
    BottomDetBound top B := by
  intro u v w
  exact h.detNatAbs_bottomRows u v w

private theorem natAbs_det_submatrix
    (M : Matrix F6 F6 ℤ) (r c : Equiv.Perm F6) :
    (M.submatrix r c).det.natAbs = M.det.natAbs := by
  have habs := Matrix.abs_det_submatrix_equiv_equiv r c M
  have hcast :
      ((M.submatrix r c).det.natAbs : ℤ) = (M.det.natAbs : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using habs
  exact Int.ofNat_inj.mp hcast

/-! ## Column permutations -/

def permuteTopColumns (top : Matrix F3 F6 ℤ) (c : Equiv.Perm F6) :
    Matrix F3 F6 ℤ :=
  fun i j ↦ top i (c j)

def pullbackRow (u : BinaryRow) (c : Equiv.Perm F6) : BinaryRow :=
  fun j ↦ u (c.symm j)

private theorem stack3x3_permuteColumns
    (top : Matrix F3 F6 ℤ) (c : Equiv.Perm F6)
    (u v w : BinaryRow) :
    stack3x3 (permuteTopColumns top c) (bottomOfRows u v w) =
      (stack3x3 top
        (bottomOfRows (pullbackRow u c) (pullbackRow v c)
          (pullbackRow w c))).submatrix id c := by
  ext i j
  fin_cases i <;>
    simp [stack3x3, bottomOfRows, permuteTopColumns, pullbackRow]

/-- Absolute determinant bounds are invariant under a column permutation. -/
theorem BottomDetBound.permuteColumns
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : BottomDetBound top B) (c : Equiv.Perm F6) :
    BottomDetBound (permuteTopColumns top c) B := by
  intro u v w
  rw [stack3x3_permuteColumns]
  let M := stack3x3 top
    (bottomOfRows (pullbackRow u c) (pullbackRow v c)
      (pullbackRow w c))
  calc
    (M.submatrix id c).det.natAbs = M.det.natAbs := by
      simpa using natAbs_det_submatrix M (Equiv.refl F6) c
    _ ≤ B := h (pullbackRow u c) (pullbackRow v c) (pullbackRow w c)

/-! ## Top-row transpositions -/

def includeTopRow (i : F3) : F6 := ⟨i, by omega⟩

def swapTopRows (top : Matrix F3 F6 ℤ) (a b : F3) :
    Matrix F3 F6 ℤ :=
  fun i j ↦ top (Equiv.swap a b i) j

def extendTopSwap (a b : F3) : Equiv.Perm F6 :=
  Equiv.swap (includeTopRow a) (includeTopRow b)

private theorem stack3x3_swapTopRows
    (top : Matrix F3 F6 ℤ) (a b : F3) (u v w : BinaryRow) :
    stack3x3 (swapTopRows top a b) (bottomOfRows u v w) =
      (stack3x3 top (bottomOfRows u v w)).submatrix
        (extendTopSwap a b) id := by
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [stack3x3, bottomOfRows, swapTopRows, extendTopSwap,
      includeTopRow, Equiv.swap_apply_def]

/-- Absolute determinant bounds are invariant under swapping any two of the
three fixed top rows.  Repeated use covers all six `S₃` actions. -/
theorem BottomDetBound.swapTopRows
    {top : Matrix F3 F6 ℤ} {B : ℕ}
    (h : BottomDetBound top B) (a b : F3) :
    BottomDetBound (swapTopRows top a b) B := by
  intro u v w
  rw [stack3x3_swapTopRows]
  let M := stack3x3 top (bottomOfRows u v w)
  calc
    (M.submatrix (extendTopSwap a b) id).det.natAbs = M.det.natAbs := by
      simpa using natAbs_det_submatrix M (extendTopSwap a b) (Equiv.refl F6)
    _ ≤ B := h u v w

end MainTheory.BinaryDetSymmetry
