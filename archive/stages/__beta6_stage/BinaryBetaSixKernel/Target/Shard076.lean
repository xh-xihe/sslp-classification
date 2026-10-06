-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard076

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 4, 4, 6, 7, 7)`. -/
def targetTop_1216 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1216 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1216 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1216 : BottomDetBound targetTop_1216 9 := by
  have hU : rowTransform_1216.det.natAbs = 1 := by
    have hdet : rowTransform_1216.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1216 hU
  have hcols := hrows.permuteColumns columnPerm_1216
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1216 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1216 = targetTop_1216 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1216 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 6 7 7)) 9 := by
  have htop : targetTop_1216 =
      topOfPattern (R := ℤ) (angle6 1 4 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1216

/-- Explicit target top block for canonical pattern `(1, 4, 4, 7, 7, 7)`. -/
def targetTop_1217 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1217 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1217 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1217 : BottomDetBound targetTop_1217 9 := by
  have hU : rowTransform_1217.det.natAbs = 1 := by
    have hdet : rowTransform_1217.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1217 hU
  have hcols := hrows.permuteColumns columnPerm_1217
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1217 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1217 = targetTop_1217 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1217 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 7 7 7)) 9 := by
  have htop : targetTop_1217 =
      topOfPattern (R := ℤ) (angle6 1 4 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1217

/-- Explicit rank-deficient target for canonical pattern `(1, 4, 5, 5, 5, 5)`. -/
def targetTop_1218 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1218 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1218 :
    TopRowRelation targetTop_1218 relationCoefficients_1218 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1218, relationCoefficients_1218, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1218 : BottomDetBound targetTop_1218 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1218

theorem canonicalBound_1218 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 5 5)) 9 := by
  have htop : targetTop_1218 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1218

/-- Explicit target top block for canonical pattern `(1, 4, 5, 5, 5, 6)`. -/
def targetTop_1219 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1219 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_1219 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1219 : BottomDetBound targetTop_1219 9 := by
  have hU : rowTransform_1219.det.natAbs = 1 := by
    have hdet : rowTransform_1219.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1219 hU
  have hcols := hrows.permuteColumns columnPerm_1219
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1219 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1219 = targetTop_1219 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1219 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 5 6)) 9 := by
  have htop : targetTop_1219 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1219

/-- Explicit target top block for canonical pattern `(1, 4, 5, 5, 5, 7)`. -/
def targetTop_1220 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1220 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_1220 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1220 : BottomDetBound targetTop_1220 9 := by
  have hU : rowTransform_1220.det.natAbs = 1 := by
    have hdet : rowTransform_1220.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1220 hU
  have hcols := hrows.permuteColumns columnPerm_1220
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1220 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1220 = targetTop_1220 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1220 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 5 7)) 9 := by
  have htop : targetTop_1220 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1220

/-- Explicit target top block for canonical pattern `(1, 4, 5, 5, 6, 6)`. -/
def targetTop_1221 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1221 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1221 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1221 : BottomDetBound targetTop_1221 9 := by
  have hU : rowTransform_1221.det.natAbs = 1 := by
    have hdet : rowTransform_1221.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1221 hU
  have hcols := hrows.permuteColumns columnPerm_1221
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1221 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1221 = targetTop_1221 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1221 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 6 6)) 9 := by
  have htop : targetTop_1221 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1221

/-- Explicit target top block for canonical pattern `(1, 4, 5, 5, 6, 7)`. -/
def targetTop_1222 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1222 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_1222 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1222 : BottomDetBound targetTop_1222 9 := by
  have hU : rowTransform_1222.det.natAbs = 1 := by
    have hdet : rowTransform_1222.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1222 hU
  have hcols := hrows.permuteColumns columnPerm_1222
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1222 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1222 = targetTop_1222 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1222 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 6 7)) 9 := by
  have htop : targetTop_1222 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1222

/-- Explicit target top block for canonical pattern `(1, 4, 5, 5, 7, 7)`. -/
def targetTop_1223 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1223 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1223 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1223 : BottomDetBound targetTop_1223 9 := by
  have hU : rowTransform_1223.det.natAbs = 1 := by
    have hdet : rowTransform_1223.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1223 hU
  have hcols := hrows.permuteColumns columnPerm_1223
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1223 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1223 = targetTop_1223 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1223 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 7 7)) 9 := by
  have htop : targetTop_1223 =
      topOfPattern (R := ℤ) (angle6 1 4 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1223

/-- Explicit target top block for canonical pattern `(1, 4, 5, 6, 6, 6)`. -/
def targetTop_1224 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1224 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1224 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1224 : BottomDetBound targetTop_1224 9 := by
  have hU : rowTransform_1224.det.natAbs = 1 := by
    have hdet : rowTransform_1224.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1224 hU
  have hcols := hrows.permuteColumns columnPerm_1224
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1224 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1224 = targetTop_1224 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1224 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 6 6 6)) 9 := by
  have htop : targetTop_1224 =
      topOfPattern (R := ℤ) (angle6 1 4 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1224

/-- Explicit target top block for canonical pattern `(1, 4, 5, 6, 6, 7)`. -/
def targetTop_1225 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1225 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1225 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1225 : BottomDetBound targetTop_1225 9 := by
  have hU : rowTransform_1225.det.natAbs = 1 := by
    have hdet : rowTransform_1225.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1225 hU
  have hcols := hrows.permuteColumns columnPerm_1225
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1225 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1225 = targetTop_1225 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1225 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 6 6 7)) 9 := by
  have htop : targetTop_1225 =
      topOfPattern (R := ℤ) (angle6 1 4 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1225

/-- Explicit target top block for canonical pattern `(1, 4, 5, 6, 7, 7)`. -/
def targetTop_1226 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1226 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_1226 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1226 : BottomDetBound targetTop_1226 9 := by
  have hU : rowTransform_1226.det.natAbs = 1 := by
    have hdet : rowTransform_1226.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1226 hU
  have hcols := hrows.permuteColumns columnPerm_1226
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1226 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1226 = targetTop_1226 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1226 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 6 7 7)) 9 := by
  have htop : targetTop_1226 =
      topOfPattern (R := ℤ) (angle6 1 4 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1226

/-- Explicit target top block for canonical pattern `(1, 4, 5, 7, 7, 7)`. -/
def targetTop_1227 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1227 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1227 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1227 : BottomDetBound targetTop_1227 9 := by
  have hU : rowTransform_1227.det.natAbs = 1 := by
    have hdet : rowTransform_1227.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1227 hU
  have hcols := hrows.permuteColumns columnPerm_1227
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1227 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1227 = targetTop_1227 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1227 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 7 7 7)) 9 := by
  have htop : targetTop_1227 =
      topOfPattern (R := ℤ) (angle6 1 4 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1227

/-- Explicit target top block for canonical pattern `(1, 4, 6, 6, 6, 6)`. -/
def targetTop_1228 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1228 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1228 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1228 : BottomDetBound targetTop_1228 9 := by
  have hU : rowTransform_1228.det.natAbs = 1 := by
    have hdet : rowTransform_1228.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1228 hU
  have hcols := hrows.permuteColumns columnPerm_1228
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1228 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1228 = targetTop_1228 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1228 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 6 6 6)) 9 := by
  have htop : targetTop_1228 =
      topOfPattern (R := ℤ) (angle6 1 4 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1228

/-- Explicit target top block for canonical pattern `(1, 4, 6, 6, 6, 7)`. -/
def targetTop_1229 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1229 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1229 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1229 : BottomDetBound targetTop_1229 9 := by
  have hU : rowTransform_1229.det.natAbs = 1 := by
    have hdet : rowTransform_1229.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1229 hU
  have hcols := hrows.permuteColumns columnPerm_1229
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1229 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1229 = targetTop_1229 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1229 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 6 6 7)) 9 := by
  have htop : targetTop_1229 =
      topOfPattern (R := ℤ) (angle6 1 4 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1229

/-- Explicit target top block for canonical pattern `(1, 4, 6, 6, 7, 7)`. -/
def targetTop_1230 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1230 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1230 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1230 : BottomDetBound targetTop_1230 9 := by
  have hU : rowTransform_1230.det.natAbs = 1 := by
    have hdet : rowTransform_1230.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1230 hU
  have hcols := hrows.permuteColumns columnPerm_1230
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1230 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1230 = targetTop_1230 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1230 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 6 7 7)) 9 := by
  have htop : targetTop_1230 =
      topOfPattern (R := ℤ) (angle6 1 4 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1230

/-- Explicit target top block for canonical pattern `(1, 4, 6, 7, 7, 7)`. -/
def targetTop_1231 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1231 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_1231 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1231 : BottomDetBound targetTop_1231 9 := by
  have hU : rowTransform_1231.det.natAbs = 1 := by
    have hdet : rowTransform_1231.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1231 hU
  have hcols := hrows.permuteColumns columnPerm_1231
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1231 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1231 = targetTop_1231 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1231 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 7 7 7)) 9 := by
  have htop : targetTop_1231 =
      topOfPattern (R := ℤ) (angle6 1 4 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1231

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard076
