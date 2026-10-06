-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard074

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 5, 6)`. -/
def targetTop_1184 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1184 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1184 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1184 : BottomDetBound targetTop_1184 9 := by
  have hU : rowTransform_1184.det.natAbs = 1 := by
    have hdet : rowTransform_1184.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1184 hU
  have hcols := hrows.permuteColumns columnPerm_1184
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1184 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1184 = targetTop_1184 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1184 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 5 6)) 9 := by
  have htop : targetTop_1184 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1184

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 5, 7)`. -/
def targetTop_1185 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1185 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1185 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1185 : BottomDetBound targetTop_1185 9 := by
  have hU : rowTransform_1185.det.natAbs = 1 := by
    have hdet : rowTransform_1185.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1185 hU
  have hcols := hrows.permuteColumns columnPerm_1185
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1185 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1185 = targetTop_1185 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1185 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 5 7)) 9 := by
  have htop : targetTop_1185 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1185

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 6, 6)`. -/
def targetTop_1186 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1186 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1186 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1186 : BottomDetBound targetTop_1186 9 := by
  have hU : rowTransform_1186.det.natAbs = 1 := by
    have hdet : rowTransform_1186.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1186 hU
  have hcols := hrows.permuteColumns columnPerm_1186
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1186 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1186 = targetTop_1186 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1186 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 6 6)) 9 := by
  have htop : targetTop_1186 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1186

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 6, 7)`. -/
def targetTop_1187 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1187 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1187 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1187 : BottomDetBound targetTop_1187 9 := by
  have hU : rowTransform_1187.det.natAbs = 1 := by
    have hdet : rowTransform_1187.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1187 hU
  have hcols := hrows.permuteColumns columnPerm_1187
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1187 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1187 = targetTop_1187 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1187 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 6 7)) 9 := by
  have htop : targetTop_1187 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1187

/-- Explicit target top block for canonical pattern `(1, 3, 5, 5, 7, 7)`. -/
def targetTop_1188 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1188 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 1, (-1)]

def columnPerm_1188 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1188 : BottomDetBound targetTop_1188 9 := by
  have hU : rowTransform_1188.det.natAbs = 1 := by
    have hdet : rowTransform_1188.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1188 hU
  have hcols := hrows.permuteColumns columnPerm_1188
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1188 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1188 = targetTop_1188 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1188 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 7 7)) 9 := by
  have htop : targetTop_1188 =
      topOfPattern (R := ℤ) (angle6 1 3 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1188

/-- Explicit target top block for canonical pattern `(1, 3, 5, 6, 6, 6)`. -/
def targetTop_1189 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1189 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1189 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1189 : BottomDetBound targetTop_1189 9 := by
  have hU : rowTransform_1189.det.natAbs = 1 := by
    have hdet : rowTransform_1189.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate.bottomBound.transformTopRows rowTransform_1189 hU
  have hcols := hrows.permuteColumns columnPerm_1189
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1189 MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Base.explicitTop)
          columnPerm_1189 = targetTop_1189 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1189 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 6 6 6)) 9 := by
  have htop : targetTop_1189 =
      topOfPattern (R := ℤ) (angle6 1 3 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1189

/-- Explicit target top block for canonical pattern `(1, 3, 5, 6, 6, 7)`. -/
def targetTop_1190 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1190 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1190 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1190 : BottomDetBound targetTop_1190 9 := by
  have hU : rowTransform_1190.det.natAbs = 1 := by
    have hdet : rowTransform_1190.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate.bottomBound.transformTopRows rowTransform_1190 hU
  have hcols := hrows.permuteColumns columnPerm_1190
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1190 MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Base.explicitTop)
          columnPerm_1190 = targetTop_1190 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1190 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 6 6 7)) 9 := by
  have htop : targetTop_1190 =
      topOfPattern (R := ℤ) (angle6 1 3 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1190

/-- Explicit target top block for canonical pattern `(1, 3, 5, 6, 7, 7)`. -/
def targetTop_1191 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1191 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1191 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1191 : BottomDetBound targetTop_1191 9 := by
  have hU : rowTransform_1191.det.natAbs = 1 := by
    have hdet : rowTransform_1191.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate.bottomBound.transformTopRows rowTransform_1191 hU
  have hcols := hrows.permuteColumns columnPerm_1191
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1191 MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Base.explicitTop)
          columnPerm_1191 = targetTop_1191 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1191 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 6 7 7)) 9 := by
  have htop : targetTop_1191 =
      topOfPattern (R := ℤ) (angle6 1 3 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1191

/-- Explicit target top block for canonical pattern `(1, 3, 5, 7, 7, 7)`. -/
def targetTop_1192 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1192 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, (-1);
     1, 0, 0]

def columnPerm_1192 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1192 : BottomDetBound targetTop_1192 9 := by
  have hU : rowTransform_1192.det.natAbs = 1 := by
    have hdet : rowTransform_1192.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1192 hU
  have hcols := hrows.permuteColumns columnPerm_1192
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1192 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1192 = targetTop_1192 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1192 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 7 7 7)) 9 := by
  have htop : targetTop_1192 =
      topOfPattern (R := ℤ) (angle6 1 3 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1192

/-- Explicit target top block for canonical pattern `(1, 3, 6, 6, 6, 6)`. -/
def targetTop_1193 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1193 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1193 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1193 : BottomDetBound targetTop_1193 9 := by
  have hU : rowTransform_1193.det.natAbs = 1 := by
    have hdet : rowTransform_1193.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1193 hU
  have hcols := hrows.permuteColumns columnPerm_1193
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1193 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1193 = targetTop_1193 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1193 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 6 6 6)) 9 := by
  have htop : targetTop_1193 =
      topOfPattern (R := ℤ) (angle6 1 3 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1193

/-- Explicit target top block for canonical pattern `(1, 3, 6, 6, 6, 7)`. -/
def targetTop_1194 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1194 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1194 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1194 : BottomDetBound targetTop_1194 9 := by
  have hU : rowTransform_1194.det.natAbs = 1 := by
    have hdet : rowTransform_1194.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1194 hU
  have hcols := hrows.permuteColumns columnPerm_1194
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1194 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1194 = targetTop_1194 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1194 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 6 6 7)) 9 := by
  have htop : targetTop_1194 =
      topOfPattern (R := ℤ) (angle6 1 3 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1194

/-- Explicit target top block for canonical pattern `(1, 3, 6, 6, 7, 7)`. -/
def targetTop_1195 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1195 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1195 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1195 : BottomDetBound targetTop_1195 9 := by
  have hU : rowTransform_1195.det.natAbs = 1 := by
    have hdet : rowTransform_1195.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1195 hU
  have hcols := hrows.permuteColumns columnPerm_1195
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1195 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1195 = targetTop_1195 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1195 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 6 7 7)) 9 := by
  have htop : targetTop_1195 =
      topOfPattern (R := ℤ) (angle6 1 3 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1195

/-- Explicit target top block for canonical pattern `(1, 3, 6, 7, 7, 7)`. -/
def targetTop_1196 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1196 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_1196 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1196 : BottomDetBound targetTop_1196 9 := by
  have hU : rowTransform_1196.det.natAbs = 1 := by
    have hdet : rowTransform_1196.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1196 hU
  have hcols := hrows.permuteColumns columnPerm_1196
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1196 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1196 = targetTop_1196 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1196 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 7 7 7)) 9 := by
  have htop : targetTop_1196 =
      topOfPattern (R := ℤ) (angle6 1 3 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1196

/-- Explicit target top block for canonical pattern `(1, 3, 7, 7, 7, 7)`. -/
def targetTop_1197 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1197 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_1197 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1197 : BottomDetBound targetTop_1197 9 := by
  have hU : rowTransform_1197.det.natAbs = 1 := by
    have hdet : rowTransform_1197.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1197 hU
  have hcols := hrows.permuteColumns columnPerm_1197
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1197 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1197 = targetTop_1197 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1197 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 7 7 7 7)) 9 := by
  have htop : targetTop_1197 =
      topOfPattern (R := ℤ) (angle6 1 3 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1197

/-- Explicit rank-deficient target for canonical pattern `(1, 4, 4, 4, 4, 4)`. -/
def targetTop_1198 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1198 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1198 :
    TopRowRelation targetTop_1198 relationCoefficients_1198 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1198, relationCoefficients_1198, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1198 : BottomDetBound targetTop_1198 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1198

theorem canonicalBound_1198 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 4 4)) 9 := by
  have htop : targetTop_1198 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1198

/-- Explicit rank-deficient target for canonical pattern `(1, 4, 4, 4, 4, 5)`. -/
def targetTop_1199 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1199 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1199 :
    TopRowRelation targetTop_1199 relationCoefficients_1199 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1199, relationCoefficients_1199, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1199 : BottomDetBound targetTop_1199 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1199

theorem canonicalBound_1199 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 4 5)) 9 := by
  have htop : targetTop_1199 =
      topOfPattern (R := ℤ) (angle6 1 4 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1199

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard074
