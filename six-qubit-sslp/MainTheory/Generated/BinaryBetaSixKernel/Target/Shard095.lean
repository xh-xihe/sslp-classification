-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard095

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 7, 7)`. -/
def targetTop_1520 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1520 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1520 :
    TopRowRelation targetTop_1520 relationCoefficients_1520 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1520, relationCoefficients_1520, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1520 : BottomDetBound targetTop_1520 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1520

theorem canonicalBound_1520 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 7 7)) 9 := by
  have htop : targetTop_1520 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1520

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 4, 4, 4)`. -/
def targetTop_1521 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1521 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1521 :
    TopRowRelation targetTop_1521 relationCoefficients_1521 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1521, relationCoefficients_1521, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1521 : BottomDetBound targetTop_1521 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1521

theorem canonicalBound_1521 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 4 4)) 9 := by
  have htop : targetTop_1521 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1521

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 4, 5)`. -/
def targetTop_1522 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1522 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1522 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1522 : BottomDetBound targetTop_1522 9 := by
  have hU : rowTransform_1522.det.natAbs = 1 := by
    have hdet : rowTransform_1522.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1522 hU
  have hcols := hrows.permuteColumns columnPerm_1522
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1522 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1522 = targetTop_1522 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1522 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 4 5)) 9 := by
  have htop : targetTop_1522 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1522

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 4, 6)`. -/
def targetTop_1523 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1523 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1523 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1523 : BottomDetBound targetTop_1523 9 := by
  have hU : rowTransform_1523.det.natAbs = 1 := by
    have hdet : rowTransform_1523.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1523 hU
  have hcols := hrows.permuteColumns columnPerm_1523
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1523 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1523 = targetTop_1523 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1523 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 4 6)) 9 := by
  have htop : targetTop_1523 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1523

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 4, 4, 7)`. -/
def targetTop_1524 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1524 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1524 :
    TopRowRelation targetTop_1524 relationCoefficients_1524 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1524, relationCoefficients_1524, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1524 : BottomDetBound targetTop_1524 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1524

theorem canonicalBound_1524 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 4 7)) 9 := by
  have htop : targetTop_1524 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1524

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 5, 5)`. -/
def targetTop_1525 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1525 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1525 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1525 : BottomDetBound targetTop_1525 9 := by
  have hU : rowTransform_1525.det.natAbs = 1 := by
    have hdet : rowTransform_1525.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1525 hU
  have hcols := hrows.permuteColumns columnPerm_1525
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1525 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1525 = targetTop_1525 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1525 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 5 5)) 9 := by
  have htop : targetTop_1525 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1525

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 5, 6)`. -/
def targetTop_1526 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1526 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1526 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1526 : BottomDetBound targetTop_1526 9 := by
  have hU : rowTransform_1526.det.natAbs = 1 := by
    have hdet : rowTransform_1526.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Aggregate.bottomBound.transformTopRows rowTransform_1526 hU
  have hcols := hrows.permuteColumns columnPerm_1526
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1526 MainTheory.Generated.BinaryBetaSixKernel.Representative.R069.Base.explicitTop)
          columnPerm_1526 = targetTop_1526 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1526 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 5 6)) 9 := by
  have htop : targetTop_1526 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1526

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 5, 7)`. -/
def targetTop_1527 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1527 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1527 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1527 : BottomDetBound targetTop_1527 9 := by
  have hU : rowTransform_1527.det.natAbs = 1 := by
    have hdet : rowTransform_1527.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1527 hU
  have hcols := hrows.permuteColumns columnPerm_1527
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1527 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1527 = targetTop_1527 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1527 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 5 7)) 9 := by
  have htop : targetTop_1527 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1527

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 6, 6)`. -/
def targetTop_1528 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1528 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1528 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1528 : BottomDetBound targetTop_1528 9 := by
  have hU : rowTransform_1528.det.natAbs = 1 := by
    have hdet : rowTransform_1528.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1528 hU
  have hcols := hrows.permuteColumns columnPerm_1528
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1528 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1528 = targetTop_1528 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1528 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 6 6)) 9 := by
  have htop : targetTop_1528 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1528

/-- Explicit target top block for canonical pattern `(3, 3, 3, 4, 6, 7)`. -/
def targetTop_1529 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1529 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1529 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1529 : BottomDetBound targetTop_1529 9 := by
  have hU : rowTransform_1529.det.natAbs = 1 := by
    have hdet : rowTransform_1529.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1529 hU
  have hcols := hrows.permuteColumns columnPerm_1529
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1529 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1529 = targetTop_1529 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1529 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 6 7)) 9 := by
  have htop : targetTop_1529 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1529

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 4, 7, 7)`. -/
def targetTop_1530 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1530 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1530 :
    TopRowRelation targetTop_1530 relationCoefficients_1530 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1530, relationCoefficients_1530, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1530 : BottomDetBound targetTop_1530 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1530

theorem canonicalBound_1530 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 4 7 7)) 9 := by
  have htop : targetTop_1530 =
      topOfPattern (R := ℤ) (angle6 3 3 3 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1530

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 5, 5, 5)`. -/
def targetTop_1531 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1531 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_1531 :
    TopRowRelation targetTop_1531 relationCoefficients_1531 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1531, relationCoefficients_1531, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1531 : BottomDetBound targetTop_1531 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1531

theorem canonicalBound_1531 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 5 5)) 9 := by
  have htop : targetTop_1531 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1531

/-- Explicit target top block for canonical pattern `(3, 3, 3, 5, 5, 6)`. -/
def targetTop_1532 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1532 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1532 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1532 : BottomDetBound targetTop_1532 9 := by
  have hU : rowTransform_1532.det.natAbs = 1 := by
    have hdet : rowTransform_1532.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1532 hU
  have hcols := hrows.permuteColumns columnPerm_1532
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1532 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1532 = targetTop_1532 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1532 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 5 6)) 9 := by
  have htop : targetTop_1532 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1532

/-- Explicit target top block for canonical pattern `(3, 3, 3, 5, 5, 7)`. -/
def targetTop_1533 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1533 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1533 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1533 : BottomDetBound targetTop_1533 9 := by
  have hU : rowTransform_1533.det.natAbs = 1 := by
    have hdet : rowTransform_1533.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1533 hU
  have hcols := hrows.permuteColumns columnPerm_1533
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1533 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1533 = targetTop_1533 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1533 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 5 7)) 9 := by
  have htop : targetTop_1533 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1533

/-- Explicit target top block for canonical pattern `(3, 3, 3, 5, 6, 6)`. -/
def targetTop_1534 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1534 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1534 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1534 : BottomDetBound targetTop_1534 9 := by
  have hU : rowTransform_1534.det.natAbs = 1 := by
    have hdet : rowTransform_1534.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1534 hU
  have hcols := hrows.permuteColumns columnPerm_1534
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1534 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1534 = targetTop_1534 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1534 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 6 6)) 9 := by
  have htop : targetTop_1534 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1534

/-- Explicit target top block for canonical pattern `(3, 3, 3, 5, 6, 7)`. -/
def targetTop_1535 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1535 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1535 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1535 : BottomDetBound targetTop_1535 9 := by
  have hU : rowTransform_1535.det.natAbs = 1 := by
    have hdet : rowTransform_1535.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate.bottomBound.transformTopRows rowTransform_1535 hU
  have hcols := hrows.permuteColumns columnPerm_1535
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1535 MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop)
          columnPerm_1535 = targetTop_1535 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1535 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 6 7)) 9 := by
  have htop : targetTop_1535 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1535

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard095
