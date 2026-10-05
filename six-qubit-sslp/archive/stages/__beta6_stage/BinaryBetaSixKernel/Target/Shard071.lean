-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 4, 7)`. -/
def targetTop_1136 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1136 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1136 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1136 : BottomDetBound targetTop_1136 9 := by
  have hU : rowTransform_1136.det.natAbs = 1 := by
    have hdet : rowTransform_1136.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1136 hU
  have hcols := hrows.permuteColumns columnPerm_1136
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1136 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1136 = targetTop_1136 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1136 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 7)) 9 := by
  have htop : targetTop_1136 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1136

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 5, 5)`. -/
def targetTop_1137 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1137 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1137 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1137 : BottomDetBound targetTop_1137 9 := by
  have hU : rowTransform_1137.det.natAbs = 1 := by
    have hdet : rowTransform_1137.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1137 hU
  have hcols := hrows.permuteColumns columnPerm_1137
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1137 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1137 = targetTop_1137 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1137 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 5 5)) 9 := by
  have htop : targetTop_1137 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1137

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 5, 6)`. -/
def targetTop_1138 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1138 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1138 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1138 : BottomDetBound targetTop_1138 9 := by
  have hU : rowTransform_1138.det.natAbs = 1 := by
    have hdet : rowTransform_1138.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1138 hU
  have hcols := hrows.permuteColumns columnPerm_1138
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1138 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1138 = targetTop_1138 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1138 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 5 6)) 9 := by
  have htop : targetTop_1138 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1138

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 5, 7)`. -/
def targetTop_1139 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1139 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1139 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1139 : BottomDetBound targetTop_1139 9 := by
  have hU : rowTransform_1139.det.natAbs = 1 := by
    have hdet : rowTransform_1139.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1139 hU
  have hcols := hrows.permuteColumns columnPerm_1139
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1139 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1139 = targetTop_1139 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1139 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 5 7)) 9 := by
  have htop : targetTop_1139 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1139

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 6, 6)`. -/
def targetTop_1140 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1140 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1140 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1140 : BottomDetBound targetTop_1140 9 := by
  have hU : rowTransform_1140.det.natAbs = 1 := by
    have hdet : rowTransform_1140.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1140 hU
  have hcols := hrows.permuteColumns columnPerm_1140
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1140 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1140 = targetTop_1140 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1140 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 6 6)) 9 := by
  have htop : targetTop_1140 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1140

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 6, 7)`. -/
def targetTop_1141 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1141 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1141 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1141 : BottomDetBound targetTop_1141 9 := by
  have hU : rowTransform_1141.det.natAbs = 1 := by
    have hdet : rowTransform_1141.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1141 hU
  have hcols := hrows.permuteColumns columnPerm_1141
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1141 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1141 = targetTop_1141 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1141 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 6 7)) 9 := by
  have htop : targetTop_1141 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1141

/-- Explicit target top block for canonical pattern `(1, 3, 3, 3, 7, 7)`. -/
def targetTop_1142 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1142 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     0, 1, 0]

def columnPerm_1142 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1142 : BottomDetBound targetTop_1142 9 := by
  have hU : rowTransform_1142.det.natAbs = 1 := by
    have hdet : rowTransform_1142.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1142 hU
  have hcols := hrows.permuteColumns columnPerm_1142
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1142 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1142 = targetTop_1142 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1142 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 7 7)) 9 := by
  have htop : targetTop_1142 =
      topOfPattern (R := ℤ) (angle6 1 3 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1142

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 4, 4)`. -/
def targetTop_1143 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1143 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1143 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1143 : BottomDetBound targetTop_1143 9 := by
  have hU : rowTransform_1143.det.natAbs = 1 := by
    have hdet : rowTransform_1143.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1143 hU
  have hcols := hrows.permuteColumns columnPerm_1143
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1143 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1143 = targetTop_1143 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1143 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 4 4)) 9 := by
  have htop : targetTop_1143 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1143

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 4, 5)`. -/
def targetTop_1144 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1144 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1144 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1144 : BottomDetBound targetTop_1144 9 := by
  have hU : rowTransform_1144.det.natAbs = 1 := by
    have hdet : rowTransform_1144.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1144 hU
  have hcols := hrows.permuteColumns columnPerm_1144
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1144 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1144 = targetTop_1144 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1144 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 4 5)) 9 := by
  have htop : targetTop_1144 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1144

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 4, 6)`. -/
def targetTop_1145 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1145 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     0, 0, 1]

def columnPerm_1145 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1145 : BottomDetBound targetTop_1145 9 := by
  have hU : rowTransform_1145.det.natAbs = 1 := by
    have hdet : rowTransform_1145.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1145 hU
  have hcols := hrows.permuteColumns columnPerm_1145
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1145 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1145 = targetTop_1145 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1145 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 4 6)) 9 := by
  have htop : targetTop_1145 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1145

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 4, 7)`. -/
def targetTop_1146 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1146 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1146 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1146 : BottomDetBound targetTop_1146 9 := by
  have hU : rowTransform_1146.det.natAbs = 1 := by
    have hdet : rowTransform_1146.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1146 hU
  have hcols := hrows.permuteColumns columnPerm_1146
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1146 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1146 = targetTop_1146 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1146 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 4 7)) 9 := by
  have htop : targetTop_1146 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1146

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 5, 5)`. -/
def targetTop_1147 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1147 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1147 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1147 : BottomDetBound targetTop_1147 9 := by
  have hU : rowTransform_1147.det.natAbs = 1 := by
    have hdet : rowTransform_1147.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1147 hU
  have hcols := hrows.permuteColumns columnPerm_1147
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1147 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1147 = targetTop_1147 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1147 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 5 5)) 9 := by
  have htop : targetTop_1147 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1147

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 5, 6)`. -/
def targetTop_1148 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1148 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1148 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1148 : BottomDetBound targetTop_1148 9 := by
  have hU : rowTransform_1148.det.natAbs = 1 := by
    have hdet : rowTransform_1148.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1148 hU
  have hcols := hrows.permuteColumns columnPerm_1148
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1148 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1148 = targetTop_1148 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1148 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 5 6)) 9 := by
  have htop : targetTop_1148 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1148

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 5, 7)`. -/
def targetTop_1149 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1149 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1149 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1149 : BottomDetBound targetTop_1149 9 := by
  have hU : rowTransform_1149.det.natAbs = 1 := by
    have hdet : rowTransform_1149.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1149 hU
  have hcols := hrows.permuteColumns columnPerm_1149
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1149 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1149 = targetTop_1149 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1149 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 5 7)) 9 := by
  have htop : targetTop_1149 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1149

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 6, 6)`. -/
def targetTop_1150 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1150 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, (-1);
     0, 1, 0]

def columnPerm_1150 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1150 : BottomDetBound targetTop_1150 9 := by
  have hU : rowTransform_1150.det.natAbs = 1 := by
    have hdet : rowTransform_1150.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1150 hU
  have hcols := hrows.permuteColumns columnPerm_1150
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1150 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1150 = targetTop_1150 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1150 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 6 6)) 9 := by
  have htop : targetTop_1150 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1150

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 6, 7)`. -/
def targetTop_1151 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1151 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     0, 0, 1]

def columnPerm_1151 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1151 : BottomDetBound targetTop_1151 9 := by
  have hU : rowTransform_1151.det.natAbs = 1 := by
    have hdet : rowTransform_1151.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1151 hU
  have hcols := hrows.permuteColumns columnPerm_1151
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1151 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1151 = targetTop_1151 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1151 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 6 7)) 9 := by
  have htop : targetTop_1151 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1151

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071
