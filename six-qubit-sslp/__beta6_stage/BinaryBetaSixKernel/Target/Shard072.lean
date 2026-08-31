-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 3, 3, 4, 7, 7)`. -/
def targetTop_1152 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1152 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1152 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1152 : BottomDetBound targetTop_1152 9 := by
  have hU : rowTransform_1152.det.natAbs = 1 := by
    have hdet : rowTransform_1152.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1152 hU
  have hcols := hrows.permuteColumns columnPerm_1152
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1152 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1152 = targetTop_1152 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1152 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 7 7)) 9 := by
  have htop : targetTop_1152 =
      topOfPattern (R := ℤ) (angle6 1 3 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1152

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 5, 5)`. -/
def targetTop_1153 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1153 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1153 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1153 : BottomDetBound targetTop_1153 9 := by
  have hU : rowTransform_1153.det.natAbs = 1 := by
    have hdet : rowTransform_1153.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1153 hU
  have hcols := hrows.permuteColumns columnPerm_1153
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1153 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1153 = targetTop_1153 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1153 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 5 5)) 9 := by
  have htop : targetTop_1153 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1153

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 5, 6)`. -/
def targetTop_1154 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1154 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1154 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1154 : BottomDetBound targetTop_1154 9 := by
  have hU : rowTransform_1154.det.natAbs = 1 := by
    have hdet : rowTransform_1154.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate.bottomBound.transformTopRows rowTransform_1154 hU
  have hcols := hrows.permuteColumns columnPerm_1154
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1154 MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Base.explicitTop)
          columnPerm_1154 = targetTop_1154 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1154 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 5 6)) 9 := by
  have htop : targetTop_1154 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1154

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 5, 7)`. -/
def targetTop_1155 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1155 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1155 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1155 : BottomDetBound targetTop_1155 9 := by
  have hU : rowTransform_1155.det.natAbs = 1 := by
    have hdet : rowTransform_1155.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1155 hU
  have hcols := hrows.permuteColumns columnPerm_1155
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1155 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1155 = targetTop_1155 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1155 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 5 7)) 9 := by
  have htop : targetTop_1155 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1155

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 6, 6)`. -/
def targetTop_1156 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1156 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1156 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1156 : BottomDetBound targetTop_1156 9 := by
  have hU : rowTransform_1156.det.natAbs = 1 := by
    have hdet : rowTransform_1156.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1156 hU
  have hcols := hrows.permuteColumns columnPerm_1156
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1156 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1156 = targetTop_1156 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1156 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 6 6)) 9 := by
  have htop : targetTop_1156 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1156

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 6, 7)`. -/
def targetTop_1157 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1157 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1157 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1157 : BottomDetBound targetTop_1157 9 := by
  have hU : rowTransform_1157.det.natAbs = 1 := by
    have hdet : rowTransform_1157.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1157 hU
  have hcols := hrows.permuteColumns columnPerm_1157
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1157 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1157 = targetTop_1157 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1157 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 6 7)) 9 := by
  have htop : targetTop_1157 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1157

/-- Explicit target top block for canonical pattern `(1, 3, 3, 5, 7, 7)`. -/
def targetTop_1158 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1158 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, (-1);
     0, 1, 0]

def columnPerm_1158 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1158 : BottomDetBound targetTop_1158 9 := by
  have hU : rowTransform_1158.det.natAbs = 1 := by
    have hdet : rowTransform_1158.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1158 hU
  have hcols := hrows.permuteColumns columnPerm_1158
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1158 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1158 = targetTop_1158 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1158 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 7 7)) 9 := by
  have htop : targetTop_1158 =
      topOfPattern (R := ℤ) (angle6 1 3 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1158

/-- Explicit target top block for canonical pattern `(1, 3, 3, 6, 6, 6)`. -/
def targetTop_1159 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1159 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1159 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1159 : BottomDetBound targetTop_1159 9 := by
  have hU : rowTransform_1159.det.natAbs = 1 := by
    have hdet : rowTransform_1159.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1159 hU
  have hcols := hrows.permuteColumns columnPerm_1159
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1159 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1159 = targetTop_1159 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1159 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 6 6 6)) 9 := by
  have htop : targetTop_1159 =
      topOfPattern (R := ℤ) (angle6 1 3 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1159

/-- Explicit target top block for canonical pattern `(1, 3, 3, 6, 6, 7)`. -/
def targetTop_1160 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1160 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1160 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1160 : BottomDetBound targetTop_1160 9 := by
  have hU : rowTransform_1160.det.natAbs = 1 := by
    have hdet : rowTransform_1160.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1160 hU
  have hcols := hrows.permuteColumns columnPerm_1160
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1160 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1160 = targetTop_1160 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1160 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 6 6 7)) 9 := by
  have htop : targetTop_1160 =
      topOfPattern (R := ℤ) (angle6 1 3 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1160

/-- Explicit target top block for canonical pattern `(1, 3, 3, 6, 7, 7)`. -/
def targetTop_1161 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1161 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_1161 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1161 : BottomDetBound targetTop_1161 9 := by
  have hU : rowTransform_1161.det.natAbs = 1 := by
    have hdet : rowTransform_1161.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1161 hU
  have hcols := hrows.permuteColumns columnPerm_1161
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1161 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1161 = targetTop_1161 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1161 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 6 7 7)) 9 := by
  have htop : targetTop_1161 =
      topOfPattern (R := ℤ) (angle6 1 3 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1161

/-- Explicit target top block for canonical pattern `(1, 3, 3, 7, 7, 7)`. -/
def targetTop_1162 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1162 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_1162 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1162 : BottomDetBound targetTop_1162 9 := by
  have hU : rowTransform_1162.det.natAbs = 1 := by
    have hdet : rowTransform_1162.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1162 hU
  have hcols := hrows.permuteColumns columnPerm_1162
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1162 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1162 = targetTop_1162 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1162 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 7 7 7)) 9 := by
  have htop : targetTop_1162 =
      topOfPattern (R := ℤ) (angle6 1 3 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1162

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 4, 4)`. -/
def targetTop_1163 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1163 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1163 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1163 : BottomDetBound targetTop_1163 9 := by
  have hU : rowTransform_1163.det.natAbs = 1 := by
    have hdet : rowTransform_1163.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1163 hU
  have hcols := hrows.permuteColumns columnPerm_1163
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1163 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1163 = targetTop_1163 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1163 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 4 4)) 9 := by
  have htop : targetTop_1163 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1163

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 4, 5)`. -/
def targetTop_1164 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1164 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1164 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1164 : BottomDetBound targetTop_1164 9 := by
  have hU : rowTransform_1164.det.natAbs = 1 := by
    have hdet : rowTransform_1164.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1164 hU
  have hcols := hrows.permuteColumns columnPerm_1164
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1164 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1164 = targetTop_1164 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1164 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 4 5)) 9 := by
  have htop : targetTop_1164 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1164

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 4, 6)`. -/
def targetTop_1165 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1165 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1165 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1165 : BottomDetBound targetTop_1165 9 := by
  have hU : rowTransform_1165.det.natAbs = 1 := by
    have hdet : rowTransform_1165.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1165 hU
  have hcols := hrows.permuteColumns columnPerm_1165
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1165 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1165 = targetTop_1165 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1165 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 4 6)) 9 := by
  have htop : targetTop_1165 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1165

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 4, 7)`. -/
def targetTop_1166 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1166 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1166 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1166 : BottomDetBound targetTop_1166 9 := by
  have hU : rowTransform_1166.det.natAbs = 1 := by
    have hdet : rowTransform_1166.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1166 hU
  have hcols := hrows.permuteColumns columnPerm_1166
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1166 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1166 = targetTop_1166 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1166 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 4 7)) 9 := by
  have htop : targetTop_1166 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1166

/-- Explicit target top block for canonical pattern `(1, 3, 4, 4, 5, 5)`. -/
def targetTop_1167 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1167 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1167 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1167 : BottomDetBound targetTop_1167 9 := by
  have hU : rowTransform_1167.det.natAbs = 1 := by
    have hdet : rowTransform_1167.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1167 hU
  have hcols := hrows.permuteColumns columnPerm_1167
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1167 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1167 = targetTop_1167 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1167 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 5 5)) 9 := by
  have htop : targetTop_1167 =
      topOfPattern (R := ℤ) (angle6 1 3 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1167

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072
