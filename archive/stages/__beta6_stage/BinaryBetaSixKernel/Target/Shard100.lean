-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard100

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 6, 7)`. -/
def targetTop_1600 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1600 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1600 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1600 : BottomDetBound targetTop_1600 9 := by
  have hU : rowTransform_1600.det.natAbs = 1 := by
    have hdet : rowTransform_1600.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1600 hU
  have hcols := hrows.permuteColumns columnPerm_1600
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1600 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1600 = targetTop_1600 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1600 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 6 7)) 9 := by
  have htop : targetTop_1600 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1600

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 7, 7)`. -/
def targetTop_1601 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1601 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1601 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1601 : BottomDetBound targetTop_1601 9 := by
  have hU : rowTransform_1601.det.natAbs = 1 := by
    have hdet : rowTransform_1601.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1601 hU
  have hcols := hrows.permuteColumns columnPerm_1601
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1601 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1601 = targetTop_1601 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1601 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 7 7)) 9 := by
  have htop : targetTop_1601 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1601

/-- Explicit target top block for canonical pattern `(3, 4, 5, 6, 6, 6)`. -/
def targetTop_1602 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1602 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1602 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1602 : BottomDetBound targetTop_1602 9 := by
  have hU : rowTransform_1602.det.natAbs = 1 := by
    have hdet : rowTransform_1602.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1602 hU
  have hcols := hrows.permuteColumns columnPerm_1602
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1602 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1602 = targetTop_1602 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1602 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 6 6 6)) 9 := by
  have htop : targetTop_1602 =
      topOfPattern (R := ℤ) (angle6 3 4 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1602

/-- Explicit target top block for canonical pattern `(3, 4, 5, 6, 6, 7)`. -/
def targetTop_1603 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1603 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1603 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 3, 1, 2, 5]
  invFun := ![1, 3, 4, 2, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1603 : BottomDetBound targetTop_1603 9 := by
  have hU : rowTransform_1603.det.natAbs = 1 := by
    have hdet : rowTransform_1603.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Aggregate.bottomBound.transformTopRows rowTransform_1603 hU
  have hcols := hrows.permuteColumns columnPerm_1603
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1603 MainTheory.Generated.BinaryBetaSixKernel.Representative.R068.Base.explicitTop)
          columnPerm_1603 = targetTop_1603 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1603 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 6 6 7)) 9 := by
  have htop : targetTop_1603 =
      topOfPattern (R := ℤ) (angle6 3 4 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1603

/-- Explicit target top block for canonical pattern `(3, 4, 5, 6, 7, 7)`. -/
def targetTop_1604 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1604 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1604 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1604 : BottomDetBound targetTop_1604 9 := by
  have hU : rowTransform_1604.det.natAbs = 1 := by
    have hdet : rowTransform_1604.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Aggregate.bottomBound.transformTopRows rowTransform_1604 hU
  have hcols := hrows.permuteColumns columnPerm_1604
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1604 MainTheory.Generated.BinaryBetaSixKernel.Representative.R071.Base.explicitTop)
          columnPerm_1604 = targetTop_1604 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1604 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 6 7 7)) 9 := by
  have htop : targetTop_1604 =
      topOfPattern (R := ℤ) (angle6 3 4 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1604

/-- Explicit target top block for canonical pattern `(3, 4, 5, 7, 7, 7)`. -/
def targetTop_1605 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1605 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1605 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1605 : BottomDetBound targetTop_1605 9 := by
  have hU : rowTransform_1605.det.natAbs = 1 := by
    have hdet : rowTransform_1605.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1605 hU
  have hcols := hrows.permuteColumns columnPerm_1605
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1605 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1605 = targetTop_1605 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1605 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 7 7 7)) 9 := by
  have htop : targetTop_1605 =
      topOfPattern (R := ℤ) (angle6 3 4 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1605

/-- Explicit target top block for canonical pattern `(3, 4, 6, 6, 6, 6)`. -/
def targetTop_1606 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1606 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1606 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1606 : BottomDetBound targetTop_1606 9 := by
  have hU : rowTransform_1606.det.natAbs = 1 := by
    have hdet : rowTransform_1606.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1606 hU
  have hcols := hrows.permuteColumns columnPerm_1606
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1606 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1606 = targetTop_1606 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1606 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 6 6 6 6)) 9 := by
  have htop : targetTop_1606 =
      topOfPattern (R := ℤ) (angle6 3 4 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1606

/-- Explicit target top block for canonical pattern `(3, 4, 6, 6, 6, 7)`. -/
def targetTop_1607 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1607 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1607 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1607 : BottomDetBound targetTop_1607 9 := by
  have hU : rowTransform_1607.det.natAbs = 1 := by
    have hdet : rowTransform_1607.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1607 hU
  have hcols := hrows.permuteColumns columnPerm_1607
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1607 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1607 = targetTop_1607 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1607 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 6 6 6 7)) 9 := by
  have htop : targetTop_1607 =
      topOfPattern (R := ℤ) (angle6 3 4 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1607

/-- Explicit target top block for canonical pattern `(3, 4, 6, 6, 7, 7)`. -/
def targetTop_1608 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1608 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1608 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1608 : BottomDetBound targetTop_1608 9 := by
  have hU : rowTransform_1608.det.natAbs = 1 := by
    have hdet : rowTransform_1608.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1608 hU
  have hcols := hrows.permuteColumns columnPerm_1608
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1608 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1608 = targetTop_1608 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1608 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 6 6 7 7)) 9 := by
  have htop : targetTop_1608 =
      topOfPattern (R := ℤ) (angle6 3 4 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1608

/-- Explicit target top block for canonical pattern `(3, 4, 6, 7, 7, 7)`. -/
def targetTop_1609 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1609 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1609 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1609 : BottomDetBound targetTop_1609 9 := by
  have hU : rowTransform_1609.det.natAbs = 1 := by
    have hdet : rowTransform_1609.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1609 hU
  have hcols := hrows.permuteColumns columnPerm_1609
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1609 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1609 = targetTop_1609 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1609 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 6 7 7 7)) 9 := by
  have htop : targetTop_1609 =
      topOfPattern (R := ℤ) (angle6 3 4 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1609

/-- Explicit rank-deficient target for canonical pattern `(3, 4, 7, 7, 7, 7)`. -/
def targetTop_1610 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1610 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1610 :
    TopRowRelation targetTop_1610 relationCoefficients_1610 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1610, relationCoefficients_1610, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1610 : BottomDetBound targetTop_1610 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1610

theorem canonicalBound_1610 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 7 7 7 7)) 9 := by
  have htop : targetTop_1610 =
      topOfPattern (R := ℤ) (angle6 3 4 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1610

/-- Explicit rank-deficient target for canonical pattern `(3, 5, 5, 5, 5, 5)`. -/
def targetTop_1611 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1611 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_1611 :
    TopRowRelation targetTop_1611 relationCoefficients_1611 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1611, relationCoefficients_1611, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1611 : BottomDetBound targetTop_1611 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1611

theorem canonicalBound_1611 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 5 5)) 9 := by
  have htop : targetTop_1611 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1611

/-- Explicit target top block for canonical pattern `(3, 5, 5, 5, 5, 6)`. -/
def targetTop_1612 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1612 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1612 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1612 : BottomDetBound targetTop_1612 9 := by
  have hU : rowTransform_1612.det.natAbs = 1 := by
    have hdet : rowTransform_1612.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate.bottomBound.transformTopRows rowTransform_1612 hU
  have hcols := hrows.permuteColumns columnPerm_1612
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1612 MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Base.explicitTop)
          columnPerm_1612 = targetTop_1612 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1612 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 5 6)) 9 := by
  have htop : targetTop_1612 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1612

/-- Explicit target top block for canonical pattern `(3, 5, 5, 5, 5, 7)`. -/
def targetTop_1613 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1613 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1613 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1613 : BottomDetBound targetTop_1613 9 := by
  have hU : rowTransform_1613.det.natAbs = 1 := by
    have hdet : rowTransform_1613.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1613 hU
  have hcols := hrows.permuteColumns columnPerm_1613
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1613 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1613 = targetTop_1613 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1613 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 5 7)) 9 := by
  have htop : targetTop_1613 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1613

/-- Explicit target top block for canonical pattern `(3, 5, 5, 5, 6, 6)`. -/
def targetTop_1614 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1614 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1614 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1614 : BottomDetBound targetTop_1614 9 := by
  have hU : rowTransform_1614.det.natAbs = 1 := by
    have hdet : rowTransform_1614.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1614 hU
  have hcols := hrows.permuteColumns columnPerm_1614
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1614 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1614 = targetTop_1614 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1614 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 6 6)) 9 := by
  have htop : targetTop_1614 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1614

/-- Explicit target top block for canonical pattern `(3, 5, 5, 5, 6, 7)`. -/
def targetTop_1615 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1615 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1615 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1615 : BottomDetBound targetTop_1615 9 := by
  have hU : rowTransform_1615.det.natAbs = 1 := by
    have hdet : rowTransform_1615.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate.bottomBound.transformTopRows rowTransform_1615 hU
  have hcols := hrows.permuteColumns columnPerm_1615
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1615 MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop)
          columnPerm_1615 = targetTop_1615 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1615 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 6 7)) 9 := by
  have htop : targetTop_1615 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1615

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard100
