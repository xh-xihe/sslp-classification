-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R001.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 5, 6)`. -/
def targetTop_0080 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0080 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0080 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0080 : BottomDetBound targetTop_0080 9 := by
  have hU : rowTransform_0080.det.natAbs = 1 := by
    have hdet : rowTransform_0080.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0080 hU
  have hcols := hrows.permuteColumns columnPerm_0080
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0080 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0080 = targetTop_0080 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0080 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 5 6)) 9 := by
  have htop : targetTop_0080 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0080

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 5, 7)`. -/
def targetTop_0081 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0081 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0081 :
    TopRowRelation targetTop_0081 relationCoefficients_0081 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0081, relationCoefficients_0081, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0081 : BottomDetBound targetTop_0081 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0081

theorem canonicalBound_0081 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 5 7)) 9 := by
  have htop : targetTop_0081 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0081

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 6, 6)`. -/
def targetTop_0082 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0082 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0082 :
    TopRowRelation targetTop_0082 relationCoefficients_0082 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0082, relationCoefficients_0082, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0082 : BottomDetBound targetTop_0082 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0082

theorem canonicalBound_0082 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 6 6)) 9 := by
  have htop : targetTop_0082 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0082

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 6, 7)`. -/
def targetTop_0083 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0083 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0083 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0083 : BottomDetBound targetTop_0083 9 := by
  have hU : rowTransform_0083.det.natAbs = 1 := by
    have hdet : rowTransform_0083.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0083 hU
  have hcols := hrows.permuteColumns columnPerm_0083
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0083 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0083 = targetTop_0083 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0083 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 6 7)) 9 := by
  have htop : targetTop_0083 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0083

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 7, 7)`. -/
def targetTop_0084 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0084 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0084 :
    TopRowRelation targetTop_0084 relationCoefficients_0084 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0084, relationCoefficients_0084, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0084 : BottomDetBound targetTop_0084 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0084

theorem canonicalBound_0084 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 7 7)) 9 := by
  have htop : targetTop_0084 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0084

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 3, 3)`. -/
def targetTop_0085 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0085 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0085 :
    TopRowRelation targetTop_0085 relationCoefficients_0085 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0085, relationCoefficients_0085, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0085 : BottomDetBound targetTop_0085 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0085

theorem canonicalBound_0085 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 3)) 9 := by
  have htop : targetTop_0085 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0085

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 3, 4)`. -/
def targetTop_0086 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0086 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0086 :
    TopRowRelation targetTop_0086 relationCoefficients_0086 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0086, relationCoefficients_0086, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0086 : BottomDetBound targetTop_0086 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0086

theorem canonicalBound_0086 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 4)) 9 := by
  have htop : targetTop_0086 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0086

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 3, 5)`. -/
def targetTop_0087 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0087 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0087 :
    TopRowRelation targetTop_0087 relationCoefficients_0087 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0087, relationCoefficients_0087, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0087 : BottomDetBound targetTop_0087 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0087

theorem canonicalBound_0087 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 5)) 9 := by
  have htop : targetTop_0087 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0087

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 3, 6)`. -/
def targetTop_0088 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0088 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0088 :
    TopRowRelation targetTop_0088 relationCoefficients_0088 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0088, relationCoefficients_0088, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0088 : BottomDetBound targetTop_0088 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0088

theorem canonicalBound_0088 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 6)) 9 := by
  have htop : targetTop_0088 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0088

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 3, 7)`. -/
def targetTop_0089 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0089 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0089 :
    TopRowRelation targetTop_0089 relationCoefficients_0089 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0089, relationCoefficients_0089, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0089 : BottomDetBound targetTop_0089 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0089

theorem canonicalBound_0089 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 3 7)) 9 := by
  have htop : targetTop_0089 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0089

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 4, 4)`. -/
def targetTop_0090 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0090 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0090 :
    TopRowRelation targetTop_0090 relationCoefficients_0090 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0090, relationCoefficients_0090, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0090 : BottomDetBound targetTop_0090 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0090

theorem canonicalBound_0090 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 4)) 9 := by
  have htop : targetTop_0090 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0090

/-- Explicit target top block for canonical pattern `(0, 0, 0, 3, 4, 5)`. -/
def targetTop_0091 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0091 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0091 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0091 : BottomDetBound targetTop_0091 9 := by
  have hU : rowTransform_0091.det.natAbs = 1 := by
    have hdet : rowTransform_0091.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0091 hU
  have hcols := hrows.permuteColumns columnPerm_0091
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0091 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0091 = targetTop_0091 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0091 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 5)) 9 := by
  have htop : targetTop_0091 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0091

/-- Explicit target top block for canonical pattern `(0, 0, 0, 3, 4, 6)`. -/
def targetTop_0092 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0092 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0092 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0092 : BottomDetBound targetTop_0092 9 := by
  have hU : rowTransform_0092.det.natAbs = 1 := by
    have hdet : rowTransform_0092.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0092 hU
  have hcols := hrows.permuteColumns columnPerm_0092
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0092 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0092 = targetTop_0092 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0092 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 6)) 9 := by
  have htop : targetTop_0092 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0092

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 4, 7)`. -/
def targetTop_0093 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0093 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0093 :
    TopRowRelation targetTop_0093 relationCoefficients_0093 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0093, relationCoefficients_0093, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0093 : BottomDetBound targetTop_0093 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0093

theorem canonicalBound_0093 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 7)) 9 := by
  have htop : targetTop_0093 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0093

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 5, 5)`. -/
def targetTop_0094 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0094 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0094 :
    TopRowRelation targetTop_0094 relationCoefficients_0094 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0094, relationCoefficients_0094, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0094 : BottomDetBound targetTop_0094 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0094

theorem canonicalBound_0094 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 5 5)) 9 := by
  have htop : targetTop_0094 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0094

/-- Explicit target top block for canonical pattern `(0, 0, 0, 3, 5, 6)`. -/
def targetTop_0095 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0095 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0095 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0095 : BottomDetBound targetTop_0095 9 := by
  have hU : rowTransform_0095.det.natAbs = 1 := by
    have hdet : rowTransform_0095.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R001.Aggregate.bottomBound.transformTopRows rowTransform_0095 hU
  have hcols := hrows.permuteColumns columnPerm_0095
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0095 MainTheory.Generated.BinaryBetaSixKernel.Representative.R001.Base.explicitTop)
          columnPerm_0095 = targetTop_0095 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0095 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 5 6)) 9 := by
  have htop : targetTop_0095 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0095

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005
