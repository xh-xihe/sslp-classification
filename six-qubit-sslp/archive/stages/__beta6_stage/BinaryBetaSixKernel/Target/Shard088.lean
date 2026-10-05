-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 6, 6)`. -/
def targetTop_1408 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1408 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1408 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1408 : BottomDetBound targetTop_1408 9 := by
  have hU : rowTransform_1408.det.natAbs = 1 := by
    have hdet : rowTransform_1408.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate.bottomBound.transformTopRows rowTransform_1408 hU
  have hcols := hrows.permuteColumns columnPerm_1408
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1408 MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Base.explicitTop)
          columnPerm_1408 = targetTop_1408 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1408 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 6 6)) 9 := by
  have htop : targetTop_1408 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1408

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 6, 7)`. -/
def targetTop_1409 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1409 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1409 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1409 : BottomDetBound targetTop_1409 9 := by
  have hU : rowTransform_1409.det.natAbs = 1 := by
    have hdet : rowTransform_1409.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1409 hU
  have hcols := hrows.permuteColumns columnPerm_1409
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1409 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1409 = targetTop_1409 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1409 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 6 7)) 9 := by
  have htop : targetTop_1409 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1409

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 7, 7)`. -/
def targetTop_1410 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1410 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1410 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1410 : BottomDetBound targetTop_1410 9 := by
  have hU : rowTransform_1410.det.natAbs = 1 := by
    have hdet : rowTransform_1410.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1410 hU
  have hcols := hrows.permuteColumns columnPerm_1410
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1410 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1410 = targetTop_1410 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1410 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 7 7)) 9 := by
  have htop : targetTop_1410 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1410

/-- Explicit target top block for canonical pattern `(2, 3, 3, 6, 6, 6)`. -/
def targetTop_1411 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1411 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1411 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1411 : BottomDetBound targetTop_1411 9 := by
  have hU : rowTransform_1411.det.natAbs = 1 := by
    have hdet : rowTransform_1411.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1411 hU
  have hcols := hrows.permuteColumns columnPerm_1411
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1411 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1411 = targetTop_1411 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1411 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 6 6 6)) 9 := by
  have htop : targetTop_1411 =
      topOfPattern (R := ℤ) (angle6 2 3 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1411

/-- Explicit target top block for canonical pattern `(2, 3, 3, 6, 6, 7)`. -/
def targetTop_1412 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1412 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1412 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1412 : BottomDetBound targetTop_1412 9 := by
  have hU : rowTransform_1412.det.natAbs = 1 := by
    have hdet : rowTransform_1412.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1412 hU
  have hcols := hrows.permuteColumns columnPerm_1412
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1412 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1412 = targetTop_1412 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1412 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 6 6 7)) 9 := by
  have htop : targetTop_1412 =
      topOfPattern (R := ℤ) (angle6 2 3 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1412

/-- Explicit target top block for canonical pattern `(2, 3, 3, 6, 7, 7)`. -/
def targetTop_1413 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1413 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 1, 0;
     0, 1, 0]

def columnPerm_1413 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1413 : BottomDetBound targetTop_1413 9 := by
  have hU : rowTransform_1413.det.natAbs = 1 := by
    have hdet : rowTransform_1413.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1413 hU
  have hcols := hrows.permuteColumns columnPerm_1413
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1413 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1413 = targetTop_1413 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1413 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 6 7 7)) 9 := by
  have htop : targetTop_1413 =
      topOfPattern (R := ℤ) (angle6 2 3 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1413

/-- Explicit target top block for canonical pattern `(2, 3, 3, 7, 7, 7)`. -/
def targetTop_1414 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1414 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     1, 0, 0]

def columnPerm_1414 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1414 : BottomDetBound targetTop_1414 9 := by
  have hU : rowTransform_1414.det.natAbs = 1 := by
    have hdet : rowTransform_1414.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1414 hU
  have hcols := hrows.permuteColumns columnPerm_1414
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1414 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1414 = targetTop_1414 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1414 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 7 7 7)) 9 := by
  have htop : targetTop_1414 =
      topOfPattern (R := ℤ) (angle6 2 3 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1414

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 4, 4)`. -/
def targetTop_1415 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1415 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1415 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1415 : BottomDetBound targetTop_1415 9 := by
  have hU : rowTransform_1415.det.natAbs = 1 := by
    have hdet : rowTransform_1415.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1415 hU
  have hcols := hrows.permuteColumns columnPerm_1415
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1415 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1415 = targetTop_1415 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1415 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 4 4)) 9 := by
  have htop : targetTop_1415 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1415

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 4, 5)`. -/
def targetTop_1416 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1416 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1416 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1416 : BottomDetBound targetTop_1416 9 := by
  have hU : rowTransform_1416.det.natAbs = 1 := by
    have hdet : rowTransform_1416.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1416 hU
  have hcols := hrows.permuteColumns columnPerm_1416
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1416 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1416 = targetTop_1416 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1416 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 4 5)) 9 := by
  have htop : targetTop_1416 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1416

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 4, 6)`. -/
def targetTop_1417 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1417 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1417 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1417 : BottomDetBound targetTop_1417 9 := by
  have hU : rowTransform_1417.det.natAbs = 1 := by
    have hdet : rowTransform_1417.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1417 hU
  have hcols := hrows.permuteColumns columnPerm_1417
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1417 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1417 = targetTop_1417 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1417 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 4 6)) 9 := by
  have htop : targetTop_1417 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1417

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 4, 7)`. -/
def targetTop_1418 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1418 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1418 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1418 : BottomDetBound targetTop_1418 9 := by
  have hU : rowTransform_1418.det.natAbs = 1 := by
    have hdet : rowTransform_1418.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1418 hU
  have hcols := hrows.permuteColumns columnPerm_1418
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1418 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1418 = targetTop_1418 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1418 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 4 7)) 9 := by
  have htop : targetTop_1418 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1418

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 5, 5)`. -/
def targetTop_1419 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1419 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, (-1)]

def columnPerm_1419 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1419 : BottomDetBound targetTop_1419 9 := by
  have hU : rowTransform_1419.det.natAbs = 1 := by
    have hdet : rowTransform_1419.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1419 hU
  have hcols := hrows.permuteColumns columnPerm_1419
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1419 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1419 = targetTop_1419 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1419 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 5 5)) 9 := by
  have htop : targetTop_1419 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1419

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 5, 6)`. -/
def targetTop_1420 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1420 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1420 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1420 : BottomDetBound targetTop_1420 9 := by
  have hU : rowTransform_1420.det.natAbs = 1 := by
    have hdet : rowTransform_1420.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Aggregate.bottomBound.transformTopRows rowTransform_1420 hU
  have hcols := hrows.permuteColumns columnPerm_1420
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1420 MainTheory.Generated.BinaryBetaSixKernel.Representative.R045.Base.explicitTop)
          columnPerm_1420 = targetTop_1420 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1420 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 5 6)) 9 := by
  have htop : targetTop_1420 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1420

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 5, 7)`. -/
def targetTop_1421 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1421 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1421 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1421 : BottomDetBound targetTop_1421 9 := by
  have hU : rowTransform_1421.det.natAbs = 1 := by
    have hdet : rowTransform_1421.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1421 hU
  have hcols := hrows.permuteColumns columnPerm_1421
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1421 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1421 = targetTop_1421 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1421 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 5 7)) 9 := by
  have htop : targetTop_1421 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1421

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 6, 6)`. -/
def targetTop_1422 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1422 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1422 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1422 : BottomDetBound targetTop_1422 9 := by
  have hU : rowTransform_1422.det.natAbs = 1 := by
    have hdet : rowTransform_1422.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1422 hU
  have hcols := hrows.permuteColumns columnPerm_1422
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1422 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1422 = targetTop_1422 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1422 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 6 6)) 9 := by
  have htop : targetTop_1422 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1422

/-- Explicit target top block for canonical pattern `(2, 3, 4, 4, 6, 7)`. -/
def targetTop_1423 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1423 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1423 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1423 : BottomDetBound targetTop_1423 9 := by
  have hU : rowTransform_1423.det.natAbs = 1 := by
    have hdet : rowTransform_1423.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Aggregate.bottomBound.transformTopRows rowTransform_1423 hU
  have hcols := hrows.permuteColumns columnPerm_1423
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1423 MainTheory.Generated.BinaryBetaSixKernel.Representative.R042.Base.explicitTop)
          columnPerm_1423 = targetTop_1423 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1423 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 4 6 7)) 9 := by
  have htop : targetTop_1423 =
      topOfPattern (R := ℤ) (angle6 2 3 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1423

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088
