-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 2, 3, 5, 7, 7)`. -/
def targetTop_1088 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1088 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1088 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1088 : BottomDetBound targetTop_1088 9 := by
  have hU : rowTransform_1088.det.natAbs = 1 := by
    have hdet : rowTransform_1088.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1088 hU
  have hcols := hrows.permuteColumns columnPerm_1088
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1088 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1088 = targetTop_1088 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1088 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 5 7 7)) 9 := by
  have htop : targetTop_1088 =
      topOfPattern (R := ℤ) (angle6 1 2 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1088

/-- Explicit target top block for canonical pattern `(1, 2, 3, 6, 6, 6)`. -/
def targetTop_1089 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1089 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1089 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1089 : BottomDetBound targetTop_1089 9 := by
  have hU : rowTransform_1089.det.natAbs = 1 := by
    have hdet : rowTransform_1089.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1089 hU
  have hcols := hrows.permuteColumns columnPerm_1089
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1089 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1089 = targetTop_1089 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1089 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 6 6 6)) 9 := by
  have htop : targetTop_1089 =
      topOfPattern (R := ℤ) (angle6 1 2 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1089

/-- Explicit target top block for canonical pattern `(1, 2, 3, 6, 6, 7)`. -/
def targetTop_1090 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1090 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1090 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1090 : BottomDetBound targetTop_1090 9 := by
  have hU : rowTransform_1090.det.natAbs = 1 := by
    have hdet : rowTransform_1090.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1090 hU
  have hcols := hrows.permuteColumns columnPerm_1090
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1090 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1090 = targetTop_1090 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1090 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 6 6 7)) 9 := by
  have htop : targetTop_1090 =
      topOfPattern (R := ℤ) (angle6 1 2 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1090

/-- Explicit target top block for canonical pattern `(1, 2, 3, 6, 7, 7)`. -/
def targetTop_1091 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1091 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_1091 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1091 : BottomDetBound targetTop_1091 9 := by
  have hU : rowTransform_1091.det.natAbs = 1 := by
    have hdet : rowTransform_1091.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1091 hU
  have hcols := hrows.permuteColumns columnPerm_1091
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1091 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1091 = targetTop_1091 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1091 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 6 7 7)) 9 := by
  have htop : targetTop_1091 =
      topOfPattern (R := ℤ) (angle6 1 2 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1091

/-- Explicit target top block for canonical pattern `(1, 2, 3, 7, 7, 7)`. -/
def targetTop_1092 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1092 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1092 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1092 : BottomDetBound targetTop_1092 9 := by
  have hU : rowTransform_1092.det.natAbs = 1 := by
    have hdet : rowTransform_1092.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1092 hU
  have hcols := hrows.permuteColumns columnPerm_1092
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1092 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1092 = targetTop_1092 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1092 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 7 7 7)) 9 := by
  have htop : targetTop_1092 =
      topOfPattern (R := ℤ) (angle6 1 2 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1092

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 4, 4)`. -/
def targetTop_1093 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1093 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1093 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1093 : BottomDetBound targetTop_1093 9 := by
  have hU : rowTransform_1093.det.natAbs = 1 := by
    have hdet : rowTransform_1093.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1093 hU
  have hcols := hrows.permuteColumns columnPerm_1093
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1093 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1093 = targetTop_1093 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1093 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 4 4)) 9 := by
  have htop : targetTop_1093 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1093

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 4, 5)`. -/
def targetTop_1094 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1094 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1094 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1094 : BottomDetBound targetTop_1094 9 := by
  have hU : rowTransform_1094.det.natAbs = 1 := by
    have hdet : rowTransform_1094.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1094 hU
  have hcols := hrows.permuteColumns columnPerm_1094
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1094 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1094 = targetTop_1094 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1094 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 4 5)) 9 := by
  have htop : targetTop_1094 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1094

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 4, 6)`. -/
def targetTop_1095 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1095 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1095 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1095 : BottomDetBound targetTop_1095 9 := by
  have hU : rowTransform_1095.det.natAbs = 1 := by
    have hdet : rowTransform_1095.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1095 hU
  have hcols := hrows.permuteColumns columnPerm_1095
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1095 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1095 = targetTop_1095 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1095 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 4 6)) 9 := by
  have htop : targetTop_1095 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1095

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 4, 7)`. -/
def targetTop_1096 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1096 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1096 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1096 : BottomDetBound targetTop_1096 9 := by
  have hU : rowTransform_1096.det.natAbs = 1 := by
    have hdet : rowTransform_1096.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate.bottomBound.transformTopRows rowTransform_1096 hU
  have hcols := hrows.permuteColumns columnPerm_1096
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1096 MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Base.explicitTop)
          columnPerm_1096 = targetTop_1096 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1096 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 4 7)) 9 := by
  have htop : targetTop_1096 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1096

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 5, 5)`. -/
def targetTop_1097 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1097 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1097 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1097 : BottomDetBound targetTop_1097 9 := by
  have hU : rowTransform_1097.det.natAbs = 1 := by
    have hdet : rowTransform_1097.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1097 hU
  have hcols := hrows.permuteColumns columnPerm_1097
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1097 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1097 = targetTop_1097 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1097 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 5 5)) 9 := by
  have htop : targetTop_1097 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1097

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 5, 6)`. -/
def targetTop_1098 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1098 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1098 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1098 : BottomDetBound targetTop_1098 9 := by
  have hU : rowTransform_1098.det.natAbs = 1 := by
    have hdet : rowTransform_1098.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1098 hU
  have hcols := hrows.permuteColumns columnPerm_1098
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1098 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1098 = targetTop_1098 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1098 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 5 6)) 9 := by
  have htop : targetTop_1098 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1098

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 5, 7)`. -/
def targetTop_1099 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1099 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1099 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1099 : BottomDetBound targetTop_1099 9 := by
  have hU : rowTransform_1099.det.natAbs = 1 := by
    have hdet : rowTransform_1099.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_1099 hU
  have hcols := hrows.permuteColumns columnPerm_1099
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1099 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_1099 = targetTop_1099 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1099 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 5 7)) 9 := by
  have htop : targetTop_1099 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1099

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 6, 6)`. -/
def targetTop_1100 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1100 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1100 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1100 : BottomDetBound targetTop_1100 9 := by
  have hU : rowTransform_1100.det.natAbs = 1 := by
    have hdet : rowTransform_1100.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1100 hU
  have hcols := hrows.permuteColumns columnPerm_1100
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1100 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1100 = targetTop_1100 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1100 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 6 6)) 9 := by
  have htop : targetTop_1100 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1100

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 6, 7)`. -/
def targetTop_1101 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1101 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1101 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 3, 5]
  invFun := ![2, 3, 1, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1101 : BottomDetBound targetTop_1101 9 := by
  have hU : rowTransform_1101.det.natAbs = 1 := by
    have hdet : rowTransform_1101.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Aggregate.bottomBound.transformTopRows rowTransform_1101 hU
  have hcols := hrows.permuteColumns columnPerm_1101
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1101 MainTheory.Generated.BinaryBetaSixKernel.Representative.R044.Base.explicitTop)
          columnPerm_1101 = targetTop_1101 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1101 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 6 7)) 9 := by
  have htop : targetTop_1101 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1101

/-- Explicit target top block for canonical pattern `(1, 2, 4, 4, 7, 7)`. -/
def targetTop_1102 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1102 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1102 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1102 : BottomDetBound targetTop_1102 9 := by
  have hU : rowTransform_1102.det.natAbs = 1 := by
    have hdet : rowTransform_1102.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Aggregate.bottomBound.transformTopRows rowTransform_1102 hU
  have hcols := hrows.permuteColumns columnPerm_1102
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1102 MainTheory.Generated.BinaryBetaSixKernel.Representative.R048.Base.explicitTop)
          columnPerm_1102 = targetTop_1102 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1102 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 4 7 7)) 9 := by
  have htop : targetTop_1102 =
      topOfPattern (R := ℤ) (angle6 1 2 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1102

/-- Explicit target top block for canonical pattern `(1, 2, 4, 5, 5, 5)`. -/
def targetTop_1103 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1103 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1103 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1103 : BottomDetBound targetTop_1103 9 := by
  have hU : rowTransform_1103.det.natAbs = 1 := by
    have hdet : rowTransform_1103.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1103 hU
  have hcols := hrows.permuteColumns columnPerm_1103
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1103 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1103 = targetTop_1103 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1103 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 5 5)) 9 := by
  have htop : targetTop_1103 =
      topOfPattern (R := ℤ) (angle6 1 2 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1103

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068
