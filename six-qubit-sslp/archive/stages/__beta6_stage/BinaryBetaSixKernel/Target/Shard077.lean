-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard077

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 4, 7, 7, 7, 7)`. -/
def targetTop_1232 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1232 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1232 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1232 : BottomDetBound targetTop_1232 9 := by
  have hU : rowTransform_1232.det.natAbs = 1 := by
    have hdet : rowTransform_1232.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1232 hU
  have hcols := hrows.permuteColumns columnPerm_1232
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1232 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1232 = targetTop_1232 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1232 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 7 7 7 7)) 9 := by
  have htop : targetTop_1232 =
      topOfPattern (R := ℤ) (angle6 1 4 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1232

/-- Explicit rank-deficient target for canonical pattern `(1, 5, 5, 5, 5, 5)`. -/
def targetTop_1233 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1233 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1233 :
    TopRowRelation targetTop_1233 relationCoefficients_1233 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1233, relationCoefficients_1233, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1233 : BottomDetBound targetTop_1233 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1233

theorem canonicalBound_1233 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 5 5)) 9 := by
  have htop : targetTop_1233 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1233

/-- Explicit target top block for canonical pattern `(1, 5, 5, 5, 5, 6)`. -/
def targetTop_1234 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1234 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1234 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1234 : BottomDetBound targetTop_1234 9 := by
  have hU : rowTransform_1234.det.natAbs = 1 := by
    have hdet : rowTransform_1234.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1234 hU
  have hcols := hrows.permuteColumns columnPerm_1234
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1234 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1234 = targetTop_1234 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1234 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 5 6)) 9 := by
  have htop : targetTop_1234 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1234

/-- Explicit target top block for canonical pattern `(1, 5, 5, 5, 5, 7)`. -/
def targetTop_1235 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1235 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1235 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1235 : BottomDetBound targetTop_1235 9 := by
  have hU : rowTransform_1235.det.natAbs = 1 := by
    have hdet : rowTransform_1235.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1235 hU
  have hcols := hrows.permuteColumns columnPerm_1235
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1235 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1235 = targetTop_1235 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1235 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 5 7)) 9 := by
  have htop : targetTop_1235 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1235

/-- Explicit target top block for canonical pattern `(1, 5, 5, 5, 6, 6)`. -/
def targetTop_1236 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1236 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1236 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1236 : BottomDetBound targetTop_1236 9 := by
  have hU : rowTransform_1236.det.natAbs = 1 := by
    have hdet : rowTransform_1236.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1236 hU
  have hcols := hrows.permuteColumns columnPerm_1236
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1236 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1236 = targetTop_1236 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1236 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 6 6)) 9 := by
  have htop : targetTop_1236 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1236

/-- Explicit target top block for canonical pattern `(1, 5, 5, 5, 6, 7)`. -/
def targetTop_1237 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1237 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1237 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1237 : BottomDetBound targetTop_1237 9 := by
  have hU : rowTransform_1237.det.natAbs = 1 := by
    have hdet : rowTransform_1237.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1237 hU
  have hcols := hrows.permuteColumns columnPerm_1237
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1237 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1237 = targetTop_1237 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1237 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 6 7)) 9 := by
  have htop : targetTop_1237 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1237

/-- Explicit target top block for canonical pattern `(1, 5, 5, 5, 7, 7)`. -/
def targetTop_1238 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1238 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1238 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1238 : BottomDetBound targetTop_1238 9 := by
  have hU : rowTransform_1238.det.natAbs = 1 := by
    have hdet : rowTransform_1238.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1238 hU
  have hcols := hrows.permuteColumns columnPerm_1238
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1238 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1238 = targetTop_1238 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1238 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 5 7 7)) 9 := by
  have htop : targetTop_1238 =
      topOfPattern (R := ℤ) (angle6 1 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1238

/-- Explicit target top block for canonical pattern `(1, 5, 5, 6, 6, 6)`. -/
def targetTop_1239 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1239 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1239 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1239 : BottomDetBound targetTop_1239 9 := by
  have hU : rowTransform_1239.det.natAbs = 1 := by
    have hdet : rowTransform_1239.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1239 hU
  have hcols := hrows.permuteColumns columnPerm_1239
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1239 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1239 = targetTop_1239 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1239 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 6 6 6)) 9 := by
  have htop : targetTop_1239 =
      topOfPattern (R := ℤ) (angle6 1 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1239

/-- Explicit target top block for canonical pattern `(1, 5, 5, 6, 6, 7)`. -/
def targetTop_1240 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1240 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1240 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1240 : BottomDetBound targetTop_1240 9 := by
  have hU : rowTransform_1240.det.natAbs = 1 := by
    have hdet : rowTransform_1240.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1240 hU
  have hcols := hrows.permuteColumns columnPerm_1240
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1240 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1240 = targetTop_1240 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1240 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 6 6 7)) 9 := by
  have htop : targetTop_1240 =
      topOfPattern (R := ℤ) (angle6 1 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1240

/-- Explicit target top block for canonical pattern `(1, 5, 5, 6, 7, 7)`. -/
def targetTop_1241 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1241 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_1241 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1241 : BottomDetBound targetTop_1241 9 := by
  have hU : rowTransform_1241.det.natAbs = 1 := by
    have hdet : rowTransform_1241.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1241 hU
  have hcols := hrows.permuteColumns columnPerm_1241
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1241 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1241 = targetTop_1241 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1241 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 6 7 7)) 9 := by
  have htop : targetTop_1241 =
      topOfPattern (R := ℤ) (angle6 1 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1241

/-- Explicit target top block for canonical pattern `(1, 5, 5, 7, 7, 7)`. -/
def targetTop_1242 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1242 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1242 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1242 : BottomDetBound targetTop_1242 9 := by
  have hU : rowTransform_1242.det.natAbs = 1 := by
    have hdet : rowTransform_1242.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1242 hU
  have hcols := hrows.permuteColumns columnPerm_1242
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1242 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1242 = targetTop_1242 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1242 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 7 7 7)) 9 := by
  have htop : targetTop_1242 =
      topOfPattern (R := ℤ) (angle6 1 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1242

/-- Explicit target top block for canonical pattern `(1, 5, 6, 6, 6, 6)`. -/
def targetTop_1243 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1243 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1243 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1243 : BottomDetBound targetTop_1243 9 := by
  have hU : rowTransform_1243.det.natAbs = 1 := by
    have hdet : rowTransform_1243.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1243 hU
  have hcols := hrows.permuteColumns columnPerm_1243
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1243 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1243 = targetTop_1243 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1243 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 6 6 6 6)) 9 := by
  have htop : targetTop_1243 =
      topOfPattern (R := ℤ) (angle6 1 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1243

/-- Explicit target top block for canonical pattern `(1, 5, 6, 6, 6, 7)`. -/
def targetTop_1244 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1244 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1244 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1244 : BottomDetBound targetTop_1244 9 := by
  have hU : rowTransform_1244.det.natAbs = 1 := by
    have hdet : rowTransform_1244.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1244 hU
  have hcols := hrows.permuteColumns columnPerm_1244
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1244 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1244 = targetTop_1244 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1244 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 6 6 6 7)) 9 := by
  have htop : targetTop_1244 =
      topOfPattern (R := ℤ) (angle6 1 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1244

/-- Explicit target top block for canonical pattern `(1, 5, 6, 6, 7, 7)`. -/
def targetTop_1245 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1245 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1245 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1245 : BottomDetBound targetTop_1245 9 := by
  have hU : rowTransform_1245.det.natAbs = 1 := by
    have hdet : rowTransform_1245.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1245 hU
  have hcols := hrows.permuteColumns columnPerm_1245
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1245 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1245 = targetTop_1245 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1245 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 6 6 7 7)) 9 := by
  have htop : targetTop_1245 =
      topOfPattern (R := ℤ) (angle6 1 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1245

/-- Explicit target top block for canonical pattern `(1, 5, 6, 7, 7, 7)`. -/
def targetTop_1246 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1246 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_1246 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1246 : BottomDetBound targetTop_1246 9 := by
  have hU : rowTransform_1246.det.natAbs = 1 := by
    have hdet : rowTransform_1246.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1246 hU
  have hcols := hrows.permuteColumns columnPerm_1246
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1246 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1246 = targetTop_1246 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1246 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 6 7 7 7)) 9 := by
  have htop : targetTop_1246 =
      topOfPattern (R := ℤ) (angle6 1 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1246

/-- Explicit target top block for canonical pattern `(1, 5, 7, 7, 7, 7)`. -/
def targetTop_1247 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1247 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 0;
     1, 0, 1]

def columnPerm_1247 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1247 : BottomDetBound targetTop_1247 9 := by
  have hU : rowTransform_1247.det.natAbs = 1 := by
    have hdet : rowTransform_1247.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1247 hU
  have hcols := hrows.permuteColumns columnPerm_1247
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1247 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1247 = targetTop_1247 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1247 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 7 7 7 7)) 9 := by
  have htop : targetTop_1247 =
      topOfPattern (R := ℤ) (angle6 1 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1247

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard077
