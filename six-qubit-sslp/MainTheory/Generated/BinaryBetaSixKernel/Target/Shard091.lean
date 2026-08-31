-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard091

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 5, 7)`. -/
def targetTop_1456 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1456 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1456 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1456 : BottomDetBound targetTop_1456 9 := by
  have hU : rowTransform_1456.det.natAbs = 1 := by
    have hdet : rowTransform_1456.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1456 hU
  have hcols := hrows.permuteColumns columnPerm_1456
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1456 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1456 = targetTop_1456 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1456 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 5 7)) 9 := by
  have htop : targetTop_1456 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1456

/-- Explicit rank-deficient target for canonical pattern `(2, 4, 4, 4, 6, 6)`. -/
def targetTop_1457 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1457 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1457 :
    TopRowRelation targetTop_1457 relationCoefficients_1457 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1457, relationCoefficients_1457, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1457 : BottomDetBound targetTop_1457 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1457

theorem canonicalBound_1457 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 6 6)) 9 := by
  have htop : targetTop_1457 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1457

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 6, 7)`. -/
def targetTop_1458 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1458 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1458 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1458 : BottomDetBound targetTop_1458 9 := by
  have hU : rowTransform_1458.det.natAbs = 1 := by
    have hdet : rowTransform_1458.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1458 hU
  have hcols := hrows.permuteColumns columnPerm_1458
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1458 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1458 = targetTop_1458 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1458 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 6 7)) 9 := by
  have htop : targetTop_1458 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1458

/-- Explicit target top block for canonical pattern `(2, 4, 4, 4, 7, 7)`. -/
def targetTop_1459 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1459 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1459 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1459 : BottomDetBound targetTop_1459 9 := by
  have hU : rowTransform_1459.det.natAbs = 1 := by
    have hdet : rowTransform_1459.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1459 hU
  have hcols := hrows.permuteColumns columnPerm_1459
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1459 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1459 = targetTop_1459 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1459 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 4 7 7)) 9 := by
  have htop : targetTop_1459 =
      topOfPattern (R := ℤ) (angle6 2 4 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1459

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 5, 5)`. -/
def targetTop_1460 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1460 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1460 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1460 : BottomDetBound targetTop_1460 9 := by
  have hU : rowTransform_1460.det.natAbs = 1 := by
    have hdet : rowTransform_1460.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1460 hU
  have hcols := hrows.permuteColumns columnPerm_1460
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1460 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1460 = targetTop_1460 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1460 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 5 5)) 9 := by
  have htop : targetTop_1460 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1460

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 5, 6)`. -/
def targetTop_1461 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1461 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1461 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1461 : BottomDetBound targetTop_1461 9 := by
  have hU : rowTransform_1461.det.natAbs = 1 := by
    have hdet : rowTransform_1461.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1461 hU
  have hcols := hrows.permuteColumns columnPerm_1461
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1461 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1461 = targetTop_1461 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1461 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 5 6)) 9 := by
  have htop : targetTop_1461 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1461

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 5, 7)`. -/
def targetTop_1462 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1462 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1462 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1462 : BottomDetBound targetTop_1462 9 := by
  have hU : rowTransform_1462.det.natAbs = 1 := by
    have hdet : rowTransform_1462.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1462 hU
  have hcols := hrows.permuteColumns columnPerm_1462
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1462 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1462 = targetTop_1462 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1462 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 5 7)) 9 := by
  have htop : targetTop_1462 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1462

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 6, 6)`. -/
def targetTop_1463 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1463 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1463 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1463 : BottomDetBound targetTop_1463 9 := by
  have hU : rowTransform_1463.det.natAbs = 1 := by
    have hdet : rowTransform_1463.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1463 hU
  have hcols := hrows.permuteColumns columnPerm_1463
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1463 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1463 = targetTop_1463 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1463 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 6 6)) 9 := by
  have htop : targetTop_1463 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1463

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 6, 7)`. -/
def targetTop_1464 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1464 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1464 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1464 : BottomDetBound targetTop_1464 9 := by
  have hU : rowTransform_1464.det.natAbs = 1 := by
    have hdet : rowTransform_1464.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1464 hU
  have hcols := hrows.permuteColumns columnPerm_1464
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1464 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1464 = targetTop_1464 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1464 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 6 7)) 9 := by
  have htop : targetTop_1464 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1464

/-- Explicit target top block for canonical pattern `(2, 4, 4, 5, 7, 7)`. -/
def targetTop_1465 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1465 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1465 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1465 : BottomDetBound targetTop_1465 9 := by
  have hU : rowTransform_1465.det.natAbs = 1 := by
    have hdet : rowTransform_1465.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1465 hU
  have hcols := hrows.permuteColumns columnPerm_1465
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1465 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1465 = targetTop_1465 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1465 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 5 7 7)) 9 := by
  have htop : targetTop_1465 =
      topOfPattern (R := ℤ) (angle6 2 4 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1465

/-- Explicit rank-deficient target for canonical pattern `(2, 4, 4, 6, 6, 6)`. -/
def targetTop_1466 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1466 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1466 :
    TopRowRelation targetTop_1466 relationCoefficients_1466 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1466, relationCoefficients_1466, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1466 : BottomDetBound targetTop_1466 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1466

theorem canonicalBound_1466 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 6 6 6)) 9 := by
  have htop : targetTop_1466 =
      topOfPattern (R := ℤ) (angle6 2 4 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1466

/-- Explicit target top block for canonical pattern `(2, 4, 4, 6, 6, 7)`. -/
def targetTop_1467 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1467 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1467 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1467 : BottomDetBound targetTop_1467 9 := by
  have hU : rowTransform_1467.det.natAbs = 1 := by
    have hdet : rowTransform_1467.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1467 hU
  have hcols := hrows.permuteColumns columnPerm_1467
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1467 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1467 = targetTop_1467 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1467 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 6 6 7)) 9 := by
  have htop : targetTop_1467 =
      topOfPattern (R := ℤ) (angle6 2 4 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1467

/-- Explicit target top block for canonical pattern `(2, 4, 4, 6, 7, 7)`. -/
def targetTop_1468 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1468 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1468 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1468 : BottomDetBound targetTop_1468 9 := by
  have hU : rowTransform_1468.det.natAbs = 1 := by
    have hdet : rowTransform_1468.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1468 hU
  have hcols := hrows.permuteColumns columnPerm_1468
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1468 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1468 = targetTop_1468 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1468 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 6 7 7)) 9 := by
  have htop : targetTop_1468 =
      topOfPattern (R := ℤ) (angle6 2 4 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1468

/-- Explicit target top block for canonical pattern `(2, 4, 4, 7, 7, 7)`. -/
def targetTop_1469 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1469 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     1, 1, 0]

def columnPerm_1469 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1469 : BottomDetBound targetTop_1469 9 := by
  have hU : rowTransform_1469.det.natAbs = 1 := by
    have hdet : rowTransform_1469.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1469 hU
  have hcols := hrows.permuteColumns columnPerm_1469
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1469 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1469 = targetTop_1469 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1469 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 7 7 7)) 9 := by
  have htop : targetTop_1469 =
      topOfPattern (R := ℤ) (angle6 2 4 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1469

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 5, 5)`. -/
def targetTop_1470 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1470 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1470 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1470 : BottomDetBound targetTop_1470 9 := by
  have hU : rowTransform_1470.det.natAbs = 1 := by
    have hdet : rowTransform_1470.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1470 hU
  have hcols := hrows.permuteColumns columnPerm_1470
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1470 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1470 = targetTop_1470 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1470 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 5 5)) 9 := by
  have htop : targetTop_1470 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1470

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 5, 6)`. -/
def targetTop_1471 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1471 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1471 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1471 : BottomDetBound targetTop_1471 9 := by
  have hU : rowTransform_1471.det.natAbs = 1 := by
    have hdet : rowTransform_1471.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1471 hU
  have hcols := hrows.permuteColumns columnPerm_1471
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1471 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1471 = targetTop_1471 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1471 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 5 6)) 9 := by
  have htop : targetTop_1471 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1471

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard091
