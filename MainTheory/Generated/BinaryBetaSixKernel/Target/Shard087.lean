-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 6, 6)`. -/
def targetTop_1392 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1392 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 1, 0]

def columnPerm_1392 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1392 : BottomDetBound targetTop_1392 9 := by
  have hU : rowTransform_1392.det.natAbs = 1 := by
    have hdet : rowTransform_1392.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1392 hU
  have hcols := hrows.permuteColumns columnPerm_1392
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1392 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1392 = targetTop_1392 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1392 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 6 6)) 9 := by
  have htop : targetTop_1392 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1392

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 6, 7)`. -/
def targetTop_1393 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1393 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1393 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1393 : BottomDetBound targetTop_1393 9 := by
  have hU : rowTransform_1393.det.natAbs = 1 := by
    have hdet : rowTransform_1393.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1393 hU
  have hcols := hrows.permuteColumns columnPerm_1393
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1393 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1393 = targetTop_1393 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1393 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 6 7)) 9 := by
  have htop : targetTop_1393 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1393

/-- Explicit target top block for canonical pattern `(2, 3, 3, 3, 7, 7)`. -/
def targetTop_1394 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1394 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     0, 1, 0]

def columnPerm_1394 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1394 : BottomDetBound targetTop_1394 9 := by
  have hU : rowTransform_1394.det.natAbs = 1 := by
    have hdet : rowTransform_1394.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1394 hU
  have hcols := hrows.permuteColumns columnPerm_1394
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1394 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1394 = targetTop_1394 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1394 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 7 7)) 9 := by
  have htop : targetTop_1394 =
      topOfPattern (R := ℤ) (angle6 2 3 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1394

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 4, 4)`. -/
def targetTop_1395 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1395 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1395 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1395 : BottomDetBound targetTop_1395 9 := by
  have hU : rowTransform_1395.det.natAbs = 1 := by
    have hdet : rowTransform_1395.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1395 hU
  have hcols := hrows.permuteColumns columnPerm_1395
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1395 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1395 = targetTop_1395 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1395 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 4 4)) 9 := by
  have htop : targetTop_1395 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1395

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 4, 5)`. -/
def targetTop_1396 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1396 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1396 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1396 : BottomDetBound targetTop_1396 9 := by
  have hU : rowTransform_1396.det.natAbs = 1 := by
    have hdet : rowTransform_1396.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1396 hU
  have hcols := hrows.permuteColumns columnPerm_1396
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1396 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1396 = targetTop_1396 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1396 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 4 5)) 9 := by
  have htop : targetTop_1396 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1396

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 4, 6)`. -/
def targetTop_1397 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1397 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1397 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1397 : BottomDetBound targetTop_1397 9 := by
  have hU : rowTransform_1397.det.natAbs = 1 := by
    have hdet : rowTransform_1397.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1397 hU
  have hcols := hrows.permuteColumns columnPerm_1397
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1397 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1397 = targetTop_1397 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1397 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 4 6)) 9 := by
  have htop : targetTop_1397 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1397

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 4, 7)`. -/
def targetTop_1398 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1398 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1398 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1398 : BottomDetBound targetTop_1398 9 := by
  have hU : rowTransform_1398.det.natAbs = 1 := by
    have hdet : rowTransform_1398.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1398 hU
  have hcols := hrows.permuteColumns columnPerm_1398
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1398 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1398 = targetTop_1398 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1398 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 4 7)) 9 := by
  have htop : targetTop_1398 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1398

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 5, 5)`. -/
def targetTop_1399 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1399 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     0, 1, 0]

def columnPerm_1399 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1399 : BottomDetBound targetTop_1399 9 := by
  have hU : rowTransform_1399.det.natAbs = 1 := by
    have hdet : rowTransform_1399.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1399 hU
  have hcols := hrows.permuteColumns columnPerm_1399
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1399 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1399 = targetTop_1399 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1399 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 5 5)) 9 := by
  have htop : targetTop_1399 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1399

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 5, 6)`. -/
def targetTop_1400 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1400 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1400 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 5, 2]
  invFun := ![0, 3, 5, 1, 2, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1400 : BottomDetBound targetTop_1400 9 := by
  have hU : rowTransform_1400.det.natAbs = 1 := by
    have hdet : rowTransform_1400.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Aggregate.bottomBound.transformTopRows rowTransform_1400 hU
  have hcols := hrows.permuteColumns columnPerm_1400
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1400 MainTheory.Generated.BinaryBetaSixKernel.Representative.R061.Base.explicitTop)
          columnPerm_1400 = targetTop_1400 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1400 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 5 6)) 9 := by
  have htop : targetTop_1400 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1400

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 5, 7)`. -/
def targetTop_1401 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1401 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_1401 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1401 : BottomDetBound targetTop_1401 9 := by
  have hU : rowTransform_1401.det.natAbs = 1 := by
    have hdet : rowTransform_1401.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Aggregate.bottomBound.transformTopRows rowTransform_1401 hU
  have hcols := hrows.permuteColumns columnPerm_1401
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1401 MainTheory.Generated.BinaryBetaSixKernel.Representative.R050.Base.explicitTop)
          columnPerm_1401 = targetTop_1401 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1401 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 5 7)) 9 := by
  have htop : targetTop_1401 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1401

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 6, 6)`. -/
def targetTop_1402 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1402 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_1402 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1402 : BottomDetBound targetTop_1402 9 := by
  have hU : rowTransform_1402.det.natAbs = 1 := by
    have hdet : rowTransform_1402.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1402 hU
  have hcols := hrows.permuteColumns columnPerm_1402
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1402 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1402 = targetTop_1402 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1402 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 6 6)) 9 := by
  have htop : targetTop_1402 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1402

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 6, 7)`. -/
def targetTop_1403 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1403 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1403 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1403 : BottomDetBound targetTop_1403 9 := by
  have hU : rowTransform_1403.det.natAbs = 1 := by
    have hdet : rowTransform_1403.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1403 hU
  have hcols := hrows.permuteColumns columnPerm_1403
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1403 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1403 = targetTop_1403 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1403 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 6 7)) 9 := by
  have htop : targetTop_1403 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1403

/-- Explicit target top block for canonical pattern `(2, 3, 3, 4, 7, 7)`. -/
def targetTop_1404 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1404 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_1404 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1404 : BottomDetBound targetTop_1404 9 := by
  have hU : rowTransform_1404.det.natAbs = 1 := by
    have hdet : rowTransform_1404.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1404 hU
  have hcols := hrows.permuteColumns columnPerm_1404
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1404 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1404 = targetTop_1404 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1404 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 7 7)) 9 := by
  have htop : targetTop_1404 =
      topOfPattern (R := ℤ) (angle6 2 3 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1404

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 5, 5)`. -/
def targetTop_1405 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1405 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1405 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1405 : BottomDetBound targetTop_1405 9 := by
  have hU : rowTransform_1405.det.natAbs = 1 := by
    have hdet : rowTransform_1405.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1405 hU
  have hcols := hrows.permuteColumns columnPerm_1405
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1405 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1405 = targetTop_1405 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1405 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 5 5)) 9 := by
  have htop : targetTop_1405 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1405

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 5, 6)`. -/
def targetTop_1406 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1406 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1406 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1406 : BottomDetBound targetTop_1406 9 := by
  have hU : rowTransform_1406.det.natAbs = 1 := by
    have hdet : rowTransform_1406.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1406 hU
  have hcols := hrows.permuteColumns columnPerm_1406
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1406 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1406 = targetTop_1406 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1406 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 5 6)) 9 := by
  have htop : targetTop_1406 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1406

/-- Explicit target top block for canonical pattern `(2, 3, 3, 5, 5, 7)`. -/
def targetTop_1407 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1407 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     1, 0, 0]

def columnPerm_1407 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1407 : BottomDetBound targetTop_1407 9 := by
  have hU : rowTransform_1407.det.natAbs = 1 := by
    have hdet : rowTransform_1407.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1407 hU
  have hcols := hrows.permuteColumns columnPerm_1407
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1407 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1407 = targetTop_1407 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1407 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 5 7)) 9 := by
  have htop : targetTop_1407 =
      topOfPattern (R := ℤ) (angle6 2 3 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1407

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087
