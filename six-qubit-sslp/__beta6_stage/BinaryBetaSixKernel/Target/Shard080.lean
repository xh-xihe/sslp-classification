-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 4, 4)`. -/
def targetTop_1280 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1280 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1280 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1280 : BottomDetBound targetTop_1280 9 := by
  have hU : rowTransform_1280.det.natAbs = 1 := by
    have hdet : rowTransform_1280.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1280 hU
  have hcols := hrows.permuteColumns columnPerm_1280
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1280 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1280 = targetTop_1280 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1280 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 4 4)) 9 := by
  have htop : targetTop_1280 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1280

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 4, 5)`. -/
def targetTop_1281 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1281 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1281 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1281 : BottomDetBound targetTop_1281 9 := by
  have hU : rowTransform_1281.det.natAbs = 1 := by
    have hdet : rowTransform_1281.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1281 hU
  have hcols := hrows.permuteColumns columnPerm_1281
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1281 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1281 = targetTop_1281 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1281 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 4 5)) 9 := by
  have htop : targetTop_1281 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1281

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 4, 6)`. -/
def targetTop_1282 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1282 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1282 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1282 : BottomDetBound targetTop_1282 9 := by
  have hU : rowTransform_1282.det.natAbs = 1 := by
    have hdet : rowTransform_1282.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1282 hU
  have hcols := hrows.permuteColumns columnPerm_1282
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1282 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1282 = targetTop_1282 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1282 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 4 6)) 9 := by
  have htop : targetTop_1282 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1282

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 4, 7)`. -/
def targetTop_1283 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1283 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1283 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1283 : BottomDetBound targetTop_1283 9 := by
  have hU : rowTransform_1283.det.natAbs = 1 := by
    have hdet : rowTransform_1283.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1283 hU
  have hcols := hrows.permuteColumns columnPerm_1283
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1283 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1283 = targetTop_1283 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1283 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 4 7)) 9 := by
  have htop : targetTop_1283 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1283

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 5, 5)`. -/
def targetTop_1284 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1284 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1284 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1284 : BottomDetBound targetTop_1284 9 := by
  have hU : rowTransform_1284.det.natAbs = 1 := by
    have hdet : rowTransform_1284.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1284 hU
  have hcols := hrows.permuteColumns columnPerm_1284
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1284 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1284 = targetTop_1284 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1284 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 5 5)) 9 := by
  have htop : targetTop_1284 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1284

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 5, 6)`. -/
def targetTop_1285 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1285 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1285 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1285 : BottomDetBound targetTop_1285 9 := by
  have hU : rowTransform_1285.det.natAbs = 1 := by
    have hdet : rowTransform_1285.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate.bottomBound.transformTopRows rowTransform_1285 hU
  have hcols := hrows.permuteColumns columnPerm_1285
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1285 MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Base.explicitTop)
          columnPerm_1285 = targetTop_1285 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1285 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 5 6)) 9 := by
  have htop : targetTop_1285 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1285

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 5, 7)`. -/
def targetTop_1286 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1286 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1286 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1286 : BottomDetBound targetTop_1286 9 := by
  have hU : rowTransform_1286.det.natAbs = 1 := by
    have hdet : rowTransform_1286.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1286 hU
  have hcols := hrows.permuteColumns columnPerm_1286
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1286 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1286 = targetTop_1286 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1286 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 5 7)) 9 := by
  have htop : targetTop_1286 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1286

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 6, 6)`. -/
def targetTop_1287 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1287 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 0]

def columnPerm_1287 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1287 : BottomDetBound targetTop_1287 9 := by
  have hU : rowTransform_1287.det.natAbs = 1 := by
    have hdet : rowTransform_1287.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1287 hU
  have hcols := hrows.permuteColumns columnPerm_1287
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1287 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1287 = targetTop_1287 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1287 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 6 6)) 9 := by
  have htop : targetTop_1287 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1287

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 6, 7)`. -/
def targetTop_1288 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1288 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1288 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1288 : BottomDetBound targetTop_1288 9 := by
  have hU : rowTransform_1288.det.natAbs = 1 := by
    have hdet : rowTransform_1288.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1288 hU
  have hcols := hrows.permuteColumns columnPerm_1288
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1288 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1288 = targetTop_1288 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1288 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 6 7)) 9 := by
  have htop : targetTop_1288 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1288

/-- Explicit target top block for canonical pattern `(2, 2, 2, 3, 7, 7)`. -/
def targetTop_1289 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1289 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 1, 0]

def columnPerm_1289 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1289 : BottomDetBound targetTop_1289 9 := by
  have hU : rowTransform_1289.det.natAbs = 1 := by
    have hdet : rowTransform_1289.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1289 hU
  have hcols := hrows.permuteColumns columnPerm_1289
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1289 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1289 = targetTop_1289 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1289 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 7 7)) 9 := by
  have htop : targetTop_1289 =
      topOfPattern (R := ℤ) (angle6 2 2 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1289

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 4, 4, 4)`. -/
def targetTop_1290 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1290 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1290 :
    TopRowRelation targetTop_1290 relationCoefficients_1290 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1290, relationCoefficients_1290, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1290 : BottomDetBound targetTop_1290 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1290

theorem canonicalBound_1290 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 4)) 9 := by
  have htop : targetTop_1290 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1290

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 4, 5)`. -/
def targetTop_1291 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1291 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1291 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1291 : BottomDetBound targetTop_1291 9 := by
  have hU : rowTransform_1291.det.natAbs = 1 := by
    have hdet : rowTransform_1291.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1291 hU
  have hcols := hrows.permuteColumns columnPerm_1291
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1291 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1291 = targetTop_1291 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1291 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 5)) 9 := by
  have htop : targetTop_1291 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1291

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 2, 4, 4, 6)`. -/
def targetTop_1292 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1292 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1292 :
    TopRowRelation targetTop_1292 relationCoefficients_1292 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1292, relationCoefficients_1292, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1292 : BottomDetBound targetTop_1292 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1292

theorem canonicalBound_1292 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 6)) 9 := by
  have htop : targetTop_1292 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1292

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 4, 7)`. -/
def targetTop_1293 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1293 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1293 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1293 : BottomDetBound targetTop_1293 9 := by
  have hU : rowTransform_1293.det.natAbs = 1 := by
    have hdet : rowTransform_1293.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1293 hU
  have hcols := hrows.permuteColumns columnPerm_1293
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1293 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1293 = targetTop_1293 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1293 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 7)) 9 := by
  have htop : targetTop_1293 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1293

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 5, 5)`. -/
def targetTop_1294 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1294 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1294 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1294 : BottomDetBound targetTop_1294 9 := by
  have hU : rowTransform_1294.det.natAbs = 1 := by
    have hdet : rowTransform_1294.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1294 hU
  have hcols := hrows.permuteColumns columnPerm_1294
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1294 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1294 = targetTop_1294 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1294 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 5 5)) 9 := by
  have htop : targetTop_1294 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1294

/-- Explicit target top block for canonical pattern `(2, 2, 2, 4, 5, 6)`. -/
def targetTop_1295 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1295 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1295 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1295 : BottomDetBound targetTop_1295 9 := by
  have hU : rowTransform_1295.det.natAbs = 1 := by
    have hdet : rowTransform_1295.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1295 hU
  have hcols := hrows.permuteColumns columnPerm_1295
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1295 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1295 = targetTop_1295 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1295 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 5 6)) 9 := by
  have htop : targetTop_1295 =
      topOfPattern (R := ℤ) (angle6 2 2 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1295

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080
