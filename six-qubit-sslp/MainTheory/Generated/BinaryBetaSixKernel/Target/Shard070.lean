-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 5, 6, 6, 7)`. -/
def targetTop_1120 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1120 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_1120 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1120 : BottomDetBound targetTop_1120 9 := by
  have hU : rowTransform_1120.det.natAbs = 1 := by
    have hdet : rowTransform_1120.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1120 hU
  have hcols := hrows.permuteColumns columnPerm_1120
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1120 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1120 = targetTop_1120 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1120 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 6 7)) 9 := by
  have htop : targetTop_1120 =
      topOfPattern (R := ℤ) (angle6 1 2 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1120

/-- Explicit target top block for canonical pattern `(1, 2, 5, 6, 7, 7)`. -/
def targetTop_1121 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1121 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1121 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1121 : BottomDetBound targetTop_1121 9 := by
  have hU : rowTransform_1121.det.natAbs = 1 := by
    have hdet : rowTransform_1121.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Aggregate.bottomBound.transformTopRows rowTransform_1121 hU
  have hcols := hrows.permuteColumns columnPerm_1121
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1121 MainTheory.Generated.BinaryBetaSixKernel.Representative.R064.Base.explicitTop)
          columnPerm_1121 = targetTop_1121 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1121 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 7 7)) 9 := by
  have htop : targetTop_1121 =
      topOfPattern (R := ℤ) (angle6 1 2 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1121

/-- Explicit target top block for canonical pattern `(1, 2, 5, 7, 7, 7)`. -/
def targetTop_1122 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1122 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1122 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1122 : BottomDetBound targetTop_1122 9 := by
  have hU : rowTransform_1122.det.natAbs = 1 := by
    have hdet : rowTransform_1122.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1122 hU
  have hcols := hrows.permuteColumns columnPerm_1122
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1122 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1122 = targetTop_1122 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1122 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 7 7 7)) 9 := by
  have htop : targetTop_1122 =
      topOfPattern (R := ℤ) (angle6 1 2 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1122

/-- Explicit target top block for canonical pattern `(1, 2, 6, 6, 6, 6)`. -/
def targetTop_1123 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1123 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1123 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1123 : BottomDetBound targetTop_1123 9 := by
  have hU : rowTransform_1123.det.natAbs = 1 := by
    have hdet : rowTransform_1123.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1123 hU
  have hcols := hrows.permuteColumns columnPerm_1123
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1123 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1123 = targetTop_1123 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1123 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 6 6)) 9 := by
  have htop : targetTop_1123 =
      topOfPattern (R := ℤ) (angle6 1 2 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1123

/-- Explicit target top block for canonical pattern `(1, 2, 6, 6, 6, 7)`. -/
def targetTop_1124 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1124 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1124 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1124 : BottomDetBound targetTop_1124 9 := by
  have hU : rowTransform_1124.det.natAbs = 1 := by
    have hdet : rowTransform_1124.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1124 hU
  have hcols := hrows.permuteColumns columnPerm_1124
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1124 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1124 = targetTop_1124 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1124 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 6 7)) 9 := by
  have htop : targetTop_1124 =
      topOfPattern (R := ℤ) (angle6 1 2 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1124

/-- Explicit target top block for canonical pattern `(1, 2, 6, 6, 7, 7)`. -/
def targetTop_1125 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1125 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1125 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1125 : BottomDetBound targetTop_1125 9 := by
  have hU : rowTransform_1125.det.natAbs = 1 := by
    have hdet : rowTransform_1125.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1125 hU
  have hcols := hrows.permuteColumns columnPerm_1125
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1125 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1125 = targetTop_1125 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1125 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 7 7)) 9 := by
  have htop : targetTop_1125 =
      topOfPattern (R := ℤ) (angle6 1 2 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1125

/-- Explicit target top block for canonical pattern `(1, 2, 6, 7, 7, 7)`. -/
def targetTop_1126 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1126 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_1126 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1126 : BottomDetBound targetTop_1126 9 := by
  have hU : rowTransform_1126.det.natAbs = 1 := by
    have hdet : rowTransform_1126.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1126 hU
  have hcols := hrows.permuteColumns columnPerm_1126
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1126 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1126 = targetTop_1126 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1126 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 7 7 7)) 9 := by
  have htop : targetTop_1126 =
      topOfPattern (R := ℤ) (angle6 1 2 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1126

/-- Explicit target top block for canonical pattern `(1, 2, 7, 7, 7, 7)`. -/
def targetTop_1127 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1127 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1127 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1127 : BottomDetBound targetTop_1127 9 := by
  have hU : rowTransform_1127.det.natAbs = 1 := by
    have hdet : rowTransform_1127.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1127 hU
  have hcols := hrows.permuteColumns columnPerm_1127
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1127 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1127 = targetTop_1127 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1127 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 7 7 7 7)) 9 := by
  have htop : targetTop_1127 =
      topOfPattern (R := ℤ) (angle6 1 2 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1127

/-- Explicit rank-deficient target for canonical pattern `(1, 3, 3, 3, 3, 3)`. -/
def targetTop_1128 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1128 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1128 :
    TopRowRelation targetTop_1128 relationCoefficients_1128 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1128, relationCoefficients_1128, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1128 : BottomDetBound targetTop_1128 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1128

theorem canonicalBound_1128 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 3)) 9 := by
  have htop : targetTop_1128 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1128

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 3, 4)`. -/
def targetTop_1129 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1129 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1129 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1129 : BottomDetBound targetTop_1129 9 := by
  have hU : rowTransform_1129.det.natAbs = 1 := by
    have hdet : rowTransform_1129.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1129 hU
  have hcols := hrows.permuteColumns columnPerm_1129
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1129 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1129 = targetTop_1129 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1129 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 4)) 9 := by
  have htop : targetTop_1129 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1129

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 3, 5)`. -/
def targetTop_1130 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1130 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1130 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1130 : BottomDetBound targetTop_1130 9 := by
  have hU : rowTransform_1130.det.natAbs = 1 := by
    have hdet : rowTransform_1130.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1130 hU
  have hcols := hrows.permuteColumns columnPerm_1130
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1130 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1130 = targetTop_1130 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1130 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 5)) 9 := by
  have htop : targetTop_1130 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1130

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 3, 6)`. -/
def targetTop_1131 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1131 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1131 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1131 : BottomDetBound targetTop_1131 9 := by
  have hU : rowTransform_1131.det.natAbs = 1 := by
    have hdet : rowTransform_1131.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1131 hU
  have hcols := hrows.permuteColumns columnPerm_1131
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1131 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1131 = targetTop_1131 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1131 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 6)) 9 := by
  have htop : targetTop_1131 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1131

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 3, 7)`. -/
def targetTop_1132 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1132 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1132 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1132 : BottomDetBound targetTop_1132 9 := by
  have hU : rowTransform_1132.det.natAbs = 1 := by
    have hdet : rowTransform_1132.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1132 hU
  have hcols := hrows.permuteColumns columnPerm_1132
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1132 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1132 = targetTop_1132 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1132 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 7)) 9 := by
  have htop : targetTop_1132 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1132

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 4, 4)`. -/
def targetTop_1133 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1133 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1133 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1133 : BottomDetBound targetTop_1133 9 := by
  have hU : rowTransform_1133.det.natAbs = 1 := by
    have hdet : rowTransform_1133.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1133 hU
  have hcols := hrows.permuteColumns columnPerm_1133
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1133 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1133 = targetTop_1133 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1133 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 4)) 9 := by
  have htop : targetTop_1133 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1133

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 4, 5)`. -/
def targetTop_1134 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1134 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1134 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1134 : BottomDetBound targetTop_1134 9 := by
  have hU : rowTransform_1134.det.natAbs = 1 := by
    have hdet : rowTransform_1134.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1134 hU
  have hcols := hrows.permuteColumns columnPerm_1134
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1134 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1134 = targetTop_1134 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1134 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 5)) 9 := by
  have htop : targetTop_1134 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1134

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 4, 6)`. -/
def targetTop_1135 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1135 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     0, 0, 1]

def columnPerm_1135 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1135 : BottomDetBound targetTop_1135 9 := by
  have hU : rowTransform_1135.det.natAbs = 1 := by
    have hdet : rowTransform_1135.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1135 hU
  have hcols := hrows.permuteColumns columnPerm_1135
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1135 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1135 = targetTop_1135 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1135 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 6)) 9 := by
  have htop : targetTop_1135 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1135

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070
