-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 5, 7)`. -/
def targetTop_1472 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1472 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1472 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1472 : BottomDetBound targetTop_1472 9 := by
  have hU : rowTransform_1472.det.natAbs = 1 := by
    have hdet : rowTransform_1472.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1472 hU
  have hcols := hrows.permuteColumns columnPerm_1472
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1472 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1472 = targetTop_1472 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1472 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 5 7)) 9 := by
  have htop : targetTop_1472 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1472

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 6, 6)`. -/
def targetTop_1473 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1473 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1473 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1473 : BottomDetBound targetTop_1473 9 := by
  have hU : rowTransform_1473.det.natAbs = 1 := by
    have hdet : rowTransform_1473.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1473 hU
  have hcols := hrows.permuteColumns columnPerm_1473
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1473 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1473 = targetTop_1473 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1473 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 6 6)) 9 := by
  have htop : targetTop_1473 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1473

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 6, 7)`. -/
def targetTop_1474 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1474 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1474 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 5, 3]
  invFun := ![2, 3, 0, 5, 1, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1474 : BottomDetBound targetTop_1474 9 := by
  have hU : rowTransform_1474.det.natAbs = 1 := by
    have hdet : rowTransform_1474.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Aggregate.bottomBound.transformTopRows rowTransform_1474 hU
  have hcols := hrows.permuteColumns columnPerm_1474
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1474 MainTheory.Generated.BinaryBetaSixKernel.Representative.R043.Base.explicitTop)
          columnPerm_1474 = targetTop_1474 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1474 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 6 7)) 9 := by
  have htop : targetTop_1474 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1474

/-- Explicit target top block for canonical pattern `(2, 4, 5, 5, 7, 7)`. -/
def targetTop_1475 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1475 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1475 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1475 : BottomDetBound targetTop_1475 9 := by
  have hU : rowTransform_1475.det.natAbs = 1 := by
    have hdet : rowTransform_1475.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1475 hU
  have hcols := hrows.permuteColumns columnPerm_1475
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1475 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1475 = targetTop_1475 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1475 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 5 7 7)) 9 := by
  have htop : targetTop_1475 =
      topOfPattern (R := ℤ) (angle6 2 4 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1475

/-- Explicit target top block for canonical pattern `(2, 4, 5, 6, 6, 6)`. -/
def targetTop_1476 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1476 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1476 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1476 : BottomDetBound targetTop_1476 9 := by
  have hU : rowTransform_1476.det.natAbs = 1 := by
    have hdet : rowTransform_1476.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1476 hU
  have hcols := hrows.permuteColumns columnPerm_1476
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1476 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1476 = targetTop_1476 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1476 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 6 6 6)) 9 := by
  have htop : targetTop_1476 =
      topOfPattern (R := ℤ) (angle6 2 4 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1476

/-- Explicit target top block for canonical pattern `(2, 4, 5, 6, 6, 7)`. -/
def targetTop_1477 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1477 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1477 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1477 : BottomDetBound targetTop_1477 9 := by
  have hU : rowTransform_1477.det.natAbs = 1 := by
    have hdet : rowTransform_1477.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1477 hU
  have hcols := hrows.permuteColumns columnPerm_1477
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1477 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1477 = targetTop_1477 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1477 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 6 6 7)) 9 := by
  have htop : targetTop_1477 =
      topOfPattern (R := ℤ) (angle6 2 4 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1477

/-- Explicit target top block for canonical pattern `(2, 4, 5, 6, 7, 7)`. -/
def targetTop_1478 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1478 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1478 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1478 : BottomDetBound targetTop_1478 9 := by
  have hU : rowTransform_1478.det.natAbs = 1 := by
    have hdet : rowTransform_1478.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Aggregate.bottomBound.transformTopRows rowTransform_1478 hU
  have hcols := hrows.permuteColumns columnPerm_1478
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1478 MainTheory.Generated.BinaryBetaSixKernel.Representative.R055.Base.explicitTop)
          columnPerm_1478 = targetTop_1478 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1478 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 6 7 7)) 9 := by
  have htop : targetTop_1478 =
      topOfPattern (R := ℤ) (angle6 2 4 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1478

/-- Explicit target top block for canonical pattern `(2, 4, 5, 7, 7, 7)`. -/
def targetTop_1479 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1479 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1479 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1479 : BottomDetBound targetTop_1479 9 := by
  have hU : rowTransform_1479.det.natAbs = 1 := by
    have hdet : rowTransform_1479.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1479 hU
  have hcols := hrows.permuteColumns columnPerm_1479
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1479 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1479 = targetTop_1479 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1479 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 7 7 7)) 9 := by
  have htop : targetTop_1479 =
      topOfPattern (R := ℤ) (angle6 2 4 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1479

/-- Explicit rank-deficient target for canonical pattern `(2, 4, 6, 6, 6, 6)`. -/
def targetTop_1480 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1480 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1480 :
    TopRowRelation targetTop_1480 relationCoefficients_1480 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1480, relationCoefficients_1480, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1480 : BottomDetBound targetTop_1480 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1480

theorem canonicalBound_1480 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 6 6 6 6)) 9 := by
  have htop : targetTop_1480 =
      topOfPattern (R := ℤ) (angle6 2 4 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1480

/-- Explicit target top block for canonical pattern `(2, 4, 6, 6, 6, 7)`. -/
def targetTop_1481 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1481 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1481 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1481 : BottomDetBound targetTop_1481 9 := by
  have hU : rowTransform_1481.det.natAbs = 1 := by
    have hdet : rowTransform_1481.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1481 hU
  have hcols := hrows.permuteColumns columnPerm_1481
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1481 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1481 = targetTop_1481 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1481 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 6 6 6 7)) 9 := by
  have htop : targetTop_1481 =
      topOfPattern (R := ℤ) (angle6 2 4 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1481

/-- Explicit target top block for canonical pattern `(2, 4, 6, 6, 7, 7)`. -/
def targetTop_1482 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1482 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1482 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1482 : BottomDetBound targetTop_1482 9 := by
  have hU : rowTransform_1482.det.natAbs = 1 := by
    have hdet : rowTransform_1482.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1482 hU
  have hcols := hrows.permuteColumns columnPerm_1482
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1482 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1482 = targetTop_1482 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1482 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 6 6 7 7)) 9 := by
  have htop : targetTop_1482 =
      topOfPattern (R := ℤ) (angle6 2 4 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1482

/-- Explicit target top block for canonical pattern `(2, 4, 6, 7, 7, 7)`. -/
def targetTop_1483 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1483 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1483 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1483 : BottomDetBound targetTop_1483 9 := by
  have hU : rowTransform_1483.det.natAbs = 1 := by
    have hdet : rowTransform_1483.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1483 hU
  have hcols := hrows.permuteColumns columnPerm_1483
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1483 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1483 = targetTop_1483 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1483 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 6 7 7 7)) 9 := by
  have htop : targetTop_1483 =
      topOfPattern (R := ℤ) (angle6 2 4 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1483

/-- Explicit target top block for canonical pattern `(2, 4, 7, 7, 7, 7)`. -/
def targetTop_1484 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1484 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1484 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1484 : BottomDetBound targetTop_1484 9 := by
  have hU : rowTransform_1484.det.natAbs = 1 := by
    have hdet : rowTransform_1484.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1484 hU
  have hcols := hrows.permuteColumns columnPerm_1484
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1484 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1484 = targetTop_1484 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1484 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 7 7 7 7)) 9 := by
  have htop : targetTop_1484 =
      topOfPattern (R := ℤ) (angle6 2 4 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1484

/-- Explicit rank-deficient target for canonical pattern `(2, 5, 5, 5, 5, 5)`. -/
def targetTop_1485 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1485 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1485 :
    TopRowRelation targetTop_1485 relationCoefficients_1485 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1485, relationCoefficients_1485, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1485 : BottomDetBound targetTop_1485 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1485

theorem canonicalBound_1485 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 5 5)) 9 := by
  have htop : targetTop_1485 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1485

/-- Explicit target top block for canonical pattern `(2, 5, 5, 5, 5, 6)`. -/
def targetTop_1486 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1486 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1486 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1486 : BottomDetBound targetTop_1486 9 := by
  have hU : rowTransform_1486.det.natAbs = 1 := by
    have hdet : rowTransform_1486.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1486 hU
  have hcols := hrows.permuteColumns columnPerm_1486
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1486 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1486 = targetTop_1486 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1486 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 5 6)) 9 := by
  have htop : targetTop_1486 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1486

/-- Explicit rank-deficient target for canonical pattern `(2, 5, 5, 5, 5, 7)`. -/
def targetTop_1487 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1487 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1487 :
    TopRowRelation targetTop_1487 relationCoefficients_1487 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1487, relationCoefficients_1487, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1487 : BottomDetBound targetTop_1487 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1487

theorem canonicalBound_1487 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 5 7)) 9 := by
  have htop : targetTop_1487 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1487

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092
