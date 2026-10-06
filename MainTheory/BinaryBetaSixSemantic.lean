import MainTheory.BinaryDetSymmetry
import MainTheory.BinaryDetLastRow

/-!
# Semantic endpoint of the six-by-six determinant certificates

Generated arithmetic is indexed by the 1716 authoritative sorted top-three
row patterns.  This module proves, once and for all, that bounds for those
patterns cover every binary `6 × 6` matrix and hence imply `BetaBound 6 B`.
-/

namespace MainTheory.BinaryBetaSixSemantic

open MainTheory.BinaryBeta
open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetCofactor
open MainTheory.BinaryDetSymmetry
open MainTheory.BinaryDetLastRow

abbrev F3 := Fin 3
abbrev F6 := Fin 6

/-- The exact generated endpoint: one direct bottom-row bound for every
authoritative top-pattern index. -/
def AllPatternBottomBound (B : ℕ) : Prop :=
  ∀ i : PatternIndex,
    BottomDetBound (topOfPattern (R := ℤ) (patternAt i)) B

private theorem topEntry_eq_topOfPattern
    (A : Matrix F6 F6 Bool) (c : Equiv.Perm F6) (i : PatternIndex)
    (hc : columnPattern A ∘ c = patternAt i) (r : F3) (j : F6) :
    MainTheory.BinaryDetLastRow.bitZ
        (A (MainTheory.BinaryDetSymmetry.includeTopRow r) (c j)) =
      topOfPattern (R := ℤ) (patternAt i) r j := by
  have hj := congrFun hc j
  fin_cases r <;>
    cases h0 : A 0 (c j) <;>
    cases h1 : A 1 (c j) <;>
    cases h2 : A 2 (c j) <;>
    simp [MainTheory.BinaryDetSymmetry.includeTopRow,
      MainTheory.BinaryDetLastRow.bitZ, topOfPattern, columnPattern,
      h0, h1, h2] at hj ⊢
  all_goals simp [← hj]
  all_goals decide

/-- Read one of the bottom three rows after the canonicalizing column
permutation. -/
def permutedBottomRow (A : Matrix F6 F6 Bool) (c : Equiv.Perm F6)
    (r : F3) : BinaryRow :=
  fun j ↦ A r.succ.succ.succ (c j)

private theorem permutedMatrix_eq_stack
    (A : Matrix F6 F6 Bool) (c : Equiv.Perm F6) (i : PatternIndex)
    (hc : columnPattern A ∘ c = patternAt i) :
    (intMatrixOfBool A).submatrix id c =
      stack3x3 (topOfPattern (R := ℤ) (patternAt i))
        (bottomOfRows (permutedBottomRow A c 0)
          (permutedBottomRow A c 1) (permutedBottomRow A c 2)) := by
  ext r j
  fin_cases r
  · exact topEntry_eq_topOfPattern A c i hc 0 j
  · exact topEntry_eq_topOfPattern A c i hc 1 j
  · exact topEntry_eq_topOfPattern A c i hc 2 j
  · simp [intMatrixOfBool, stack3x3, bottomOfRows, permutedBottomRow,
      MainTheory.BinaryDetLastRow.bitZ, MainTheory.BinaryDetCofactor.bitZ]
  · simp [intMatrixOfBool, stack3x3, bottomOfRows, permutedBottomRow,
      MainTheory.BinaryDetLastRow.bitZ, MainTheory.BinaryDetCofactor.bitZ]
  · simp [intMatrixOfBool, stack3x3, bottomOfRows, permutedBottomRow,
      MainTheory.BinaryDetLastRow.bitZ, MainTheory.BinaryDetCofactor.bitZ]

private theorem natAbs_det_permuteColumns
    (M : Matrix F6 F6 ℤ) (c : Equiv.Perm F6) :
    (M.submatrix id c).det.natAbs = M.det.natAbs := by
  have habs : |(M.submatrix id c).det| = |M.det| := by
    simpa using Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl F6) c M
  have hcast :
      ((M.submatrix id c).det.natAbs : ℤ) = (M.det.natAbs : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using habs
  exact Int.ofNat_inj.mp hcast

/-- Ordinary-kernel pattern coverage plus the generated direct bounds imply
the semantic universal beta upper bound. -/
theorem betaSixBound_of_allPatternBottomBound {B : ℕ}
    (h : AllPatternBottomBound B) : BetaBound 6 B := by
  apply betaBound_of_bool_detNatAbs_bound
  intro A
  rcases exists_column_permutation_patternAt A with ⟨c, i, hc⟩
  have hpattern := h i (permutedBottomRow A c 0)
    (permutedBottomRow A c 1) (permutedBottomRow A c 2)
  rw [← permutedMatrix_eq_stack A c i hc] at hpattern
  rw [natAbs_det_permuteColumns] at hpattern
  exact hpattern

end MainTheory.BinaryBetaSixSemantic
