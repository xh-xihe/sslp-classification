-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 2, 6, 6, 6, 7)`. -/
def targetTop_1376 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1376 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1376 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1376 : BottomDetBound targetTop_1376 9 := by
  have hU : rowTransform_1376.det.natAbs = 1 := by
    have hdet : rowTransform_1376.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1376 hU
  have hcols := hrows.permuteColumns columnPerm_1376
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1376 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1376 = targetTop_1376 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1376 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 6 7)) 9 := by
  have htop : targetTop_1376 =
      topOfPattern (R := ℤ) (angle6 2 2 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1376

/-- Explicit target top block for canonical pattern `(2, 2, 6, 6, 7, 7)`. -/
def targetTop_1377 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1377 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1377 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1377 : BottomDetBound targetTop_1377 9 := by
  have hU : rowTransform_1377.det.natAbs = 1 := by
    have hdet : rowTransform_1377.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1377 hU
  have hcols := hrows.permuteColumns columnPerm_1377
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1377 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1377 = targetTop_1377 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1377 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 7 7)) 9 := by
  have htop : targetTop_1377 =
      topOfPattern (R := ℤ) (angle6 2 2 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1377

/-- Explicit target top block for canonical pattern `(2, 2, 6, 7, 7, 7)`. -/
def targetTop_1378 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1378 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1378 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1378 : BottomDetBound targetTop_1378 9 := by
  have hU : rowTransform_1378.det.natAbs = 1 := by
    have hdet : rowTransform_1378.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1378 hU
  have hcols := hrows.permuteColumns columnPerm_1378
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1378 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1378 = targetTop_1378 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1378 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 7 7 7)) 9 := by
  have htop : targetTop_1378 =
      topOfPattern (R := ℤ) (angle6 2 2 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1378

/-- Explicit rank-deficient target for canonical pattern `(2, 2, 7, 7, 7, 7)`. -/
def targetTop_1379 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1379 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1379 :
    TopRowRelation targetTop_1379 relationCoefficients_1379 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1379, relationCoefficients_1379, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1379 : BottomDetBound targetTop_1379 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1379

theorem canonicalBound_1379 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 7 7 7 7)) 9 := by
  have htop : targetTop_1379 =
      topOfPattern (R := ℤ) (angle6 2 2 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1379

/-- Explicit rank-deficient target for canonical pattern `(2, 3, 3, 3, 3, 3)`. -/
def targetTop_1380 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1380 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_1380 :
    TopRowRelation targetTop_1380 relationCoefficients_1380 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1380, relationCoefficients_1380, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1380 : BottomDetBound targetTop_1380 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1380

theorem canonicalBound_1380 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 3)) 9 := by
  have htop : targetTop_1380 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1380

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 3, 4)`. -/
def targetTop_1381 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1381 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1381 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1381 : BottomDetBound targetTop_1381 9 := by
  have hU : rowTransform_1381.det.natAbs = 1 := by
    have hdet : rowTransform_1381.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1381 hU
  have hcols := hrows.permuteColumns columnPerm_1381
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1381 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1381 = targetTop_1381 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1381 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 4)) 9 := by
  have htop : targetTop_1381 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1381

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 3, 5)`. -/
def targetTop_1382 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1382 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1382 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1382 : BottomDetBound targetTop_1382 9 := by
  have hU : rowTransform_1382.det.natAbs = 1 := by
    have hdet : rowTransform_1382.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1382 hU
  have hcols := hrows.permuteColumns columnPerm_1382
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1382 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1382 = targetTop_1382 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1382 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 5)) 9 := by
  have htop : targetTop_1382 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1382

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 3, 6)`. -/
def targetTop_1383 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1383 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1383 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1383 : BottomDetBound targetTop_1383 9 := by
  have hU : rowTransform_1383.det.natAbs = 1 := by
    have hdet : rowTransform_1383.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1383 hU
  have hcols := hrows.permuteColumns columnPerm_1383
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1383 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1383 = targetTop_1383 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1383 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 6)) 9 := by
  have htop : targetTop_1383 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1383

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 3, 7)`. -/
def targetTop_1384 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1384 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_1384 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1384 : BottomDetBound targetTop_1384 9 := by
  have hU : rowTransform_1384.det.natAbs = 1 := by
    have hdet : rowTransform_1384.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1384 hU
  have hcols := hrows.permuteColumns columnPerm_1384
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1384 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1384 = targetTop_1384 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1384 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 7)) 9 := by
  have htop : targetTop_1384 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1384

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 4, 4)`. -/
def targetTop_1385 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1385 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1385 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1385 : BottomDetBound targetTop_1385 9 := by
  have hU : rowTransform_1385.det.natAbs = 1 := by
    have hdet : rowTransform_1385.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1385 hU
  have hcols := hrows.permuteColumns columnPerm_1385
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1385 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1385 = targetTop_1385 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1385 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 4 4)) 9 := by
  have htop : targetTop_1385 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1385

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 4, 5)`. -/
def targetTop_1386 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1386 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1386 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1386 : BottomDetBound targetTop_1386 9 := by
  have hU : rowTransform_1386.det.natAbs = 1 := by
    have hdet : rowTransform_1386.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1386 hU
  have hcols := hrows.permuteColumns columnPerm_1386
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1386 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1386 = targetTop_1386 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1386 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 4 5)) 9 := by
  have htop : targetTop_1386 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1386

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 4, 6)`. -/
def targetTop_1387 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1387 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1387 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1387 : BottomDetBound targetTop_1387 9 := by
  have hU : rowTransform_1387.det.natAbs = 1 := by
    have hdet : rowTransform_1387.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1387 hU
  have hcols := hrows.permuteColumns columnPerm_1387
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1387 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1387 = targetTop_1387 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1387 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 4 6)) 9 := by
  have htop : targetTop_1387 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1387

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 4, 7)`. -/
def targetTop_1388 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1388 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1388 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1388 : BottomDetBound targetTop_1388 9 := by
  have hU : rowTransform_1388.det.natAbs = 1 := by
    have hdet : rowTransform_1388.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1388 hU
  have hcols := hrows.permuteColumns columnPerm_1388
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1388 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1388 = targetTop_1388 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1388 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 4 7)) 9 := by
  have htop : targetTop_1388 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1388

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 5, 5)`. -/
def targetTop_1389 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1389 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1389 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1389 : BottomDetBound targetTop_1389 9 := by
  have hU : rowTransform_1389.det.natAbs = 1 := by
    have hdet : rowTransform_1389.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1389 hU
  have hcols := hrows.permuteColumns columnPerm_1389
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1389 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1389 = targetTop_1389 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1389 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 5 5)) 9 := by
  have htop : targetTop_1389 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1389

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 5, 6)`. -/
def targetTop_1390 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1390 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1390 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1390 : BottomDetBound targetTop_1390 9 := by
  have hU : rowTransform_1390.det.natAbs = 1 := by
    have hdet : rowTransform_1390.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1390 hU
  have hcols := hrows.permuteColumns columnPerm_1390
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1390 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1390 = targetTop_1390 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1390 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 5 6)) 9 := by
  have htop : targetTop_1390 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1390

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 5, 7)`. -/
def targetTop_1391 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1391 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1391 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1391 : BottomDetBound targetTop_1391 9 := by
  have hU : rowTransform_1391.det.natAbs = 1 := by
    have hdet : rowTransform_1391.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1391 hU
  have hcols := hrows.permuteColumns columnPerm_1391
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1391 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1391 = targetTop_1391 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1391 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 5 7)) 9 := by
  have htop : targetTop_1391 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1391

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086
