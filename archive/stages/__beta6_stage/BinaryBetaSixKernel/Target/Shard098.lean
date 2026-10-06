-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 3, 5, 6, 6, 7)`. -/
def targetTop_1568 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1568 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_1568 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1568 : BottomDetBound targetTop_1568 9 := by
  have hU : rowTransform_1568.det.natAbs = 1 := by
    have hdet : rowTransform_1568.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate.bottomBound.transformTopRows rowTransform_1568 hU
  have hcols := hrows.permuteColumns columnPerm_1568
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1568 MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Base.explicitTop)
          columnPerm_1568 = targetTop_1568 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1568 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 6 6 7)) 9 := by
  have htop : targetTop_1568 =
      topOfPattern (R := ℤ) (angle6 3 3 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1568

/-- Explicit target top block for canonical pattern `(3, 3, 5, 6, 7, 7)`. -/
def targetTop_1569 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1569 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1569 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1569 : BottomDetBound targetTop_1569 9 := by
  have hU : rowTransform_1569.det.natAbs = 1 := by
    have hdet : rowTransform_1569.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Aggregate.bottomBound.transformTopRows rowTransform_1569 hU
  have hcols := hrows.permuteColumns columnPerm_1569
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1569 MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Base.explicitTop)
          columnPerm_1569 = targetTop_1569 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1569 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 6 7 7)) 9 := by
  have htop : targetTop_1569 =
      topOfPattern (R := ℤ) (angle6 3 3 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1569

/-- Explicit target top block for canonical pattern `(3, 3, 5, 7, 7, 7)`. -/
def targetTop_1570 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1570 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1570 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1570 : BottomDetBound targetTop_1570 9 := by
  have hU : rowTransform_1570.det.natAbs = 1 := by
    have hdet : rowTransform_1570.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1570 hU
  have hcols := hrows.permuteColumns columnPerm_1570
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1570 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1570 = targetTop_1570 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1570 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 7 7 7)) 9 := by
  have htop : targetTop_1570 =
      topOfPattern (R := ℤ) (angle6 3 3 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1570

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 6, 6, 6, 6)`. -/
def targetTop_1571 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1571 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_1571 :
    TopRowRelation targetTop_1571 relationCoefficients_1571 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1571, relationCoefficients_1571, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1571 : BottomDetBound targetTop_1571 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1571

theorem canonicalBound_1571 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 6 6 6 6)) 9 := by
  have htop : targetTop_1571 =
      topOfPattern (R := ℤ) (angle6 3 3 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1571

/-- Explicit target top block for canonical pattern `(3, 3, 6, 6, 6, 7)`. -/
def targetTop_1572 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1572 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1572 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1572 : BottomDetBound targetTop_1572 9 := by
  have hU : rowTransform_1572.det.natAbs = 1 := by
    have hdet : rowTransform_1572.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1572 hU
  have hcols := hrows.permuteColumns columnPerm_1572
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1572 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1572 = targetTop_1572 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1572 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 6 6 6 7)) 9 := by
  have htop : targetTop_1572 =
      topOfPattern (R := ℤ) (angle6 3 3 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1572

/-- Explicit target top block for canonical pattern `(3, 3, 6, 6, 7, 7)`. -/
def targetTop_1573 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1573 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1573 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1573 : BottomDetBound targetTop_1573 9 := by
  have hU : rowTransform_1573.det.natAbs = 1 := by
    have hdet : rowTransform_1573.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1573 hU
  have hcols := hrows.permuteColumns columnPerm_1573
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1573 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1573 = targetTop_1573 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1573 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 6 6 7 7)) 9 := by
  have htop : targetTop_1573 =
      topOfPattern (R := ℤ) (angle6 3 3 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1573

/-- Explicit target top block for canonical pattern `(3, 3, 6, 7, 7, 7)`. -/
def targetTop_1574 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1574 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1574 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1574 : BottomDetBound targetTop_1574 9 := by
  have hU : rowTransform_1574.det.natAbs = 1 := by
    have hdet : rowTransform_1574.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1574 hU
  have hcols := hrows.permuteColumns columnPerm_1574
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1574 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1574 = targetTop_1574 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1574 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 6 7 7 7)) 9 := by
  have htop : targetTop_1574 =
      topOfPattern (R := ℤ) (angle6 3 3 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1574

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 7, 7, 7, 7)`. -/
def targetTop_1575 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1575 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1575 :
    TopRowRelation targetTop_1575 relationCoefficients_1575 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1575, relationCoefficients_1575, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1575 : BottomDetBound targetTop_1575 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1575

theorem canonicalBound_1575 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 7 7 7 7)) 9 := by
  have htop : targetTop_1575 =
      topOfPattern (R := ℤ) (angle6 3 3 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1575

/-- Explicit rank-deficient target for canonical pattern `(3, 4, 4, 4, 4, 4)`. -/
def targetTop_1576 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1576 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1576 :
    TopRowRelation targetTop_1576 relationCoefficients_1576 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1576, relationCoefficients_1576, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1576 : BottomDetBound targetTop_1576 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1576

theorem canonicalBound_1576 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 4 4)) 9 := by
  have htop : targetTop_1576 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1576

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 4, 5)`. -/
def targetTop_1577 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1577 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1577 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1577 : BottomDetBound targetTop_1577 9 := by
  have hU : rowTransform_1577.det.natAbs = 1 := by
    have hdet : rowTransform_1577.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1577 hU
  have hcols := hrows.permuteColumns columnPerm_1577
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1577 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1577 = targetTop_1577 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1577 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 4 5)) 9 := by
  have htop : targetTop_1577 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1577

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 4, 6)`. -/
def targetTop_1578 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1578 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1578 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1578 : BottomDetBound targetTop_1578 9 := by
  have hU : rowTransform_1578.det.natAbs = 1 := by
    have hdet : rowTransform_1578.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1578 hU
  have hcols := hrows.permuteColumns columnPerm_1578
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1578 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1578 = targetTop_1578 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1578 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 4 6)) 9 := by
  have htop : targetTop_1578 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1578

/-- Explicit rank-deficient target for canonical pattern `(3, 4, 4, 4, 4, 7)`. -/
def targetTop_1579 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1579 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1579 :
    TopRowRelation targetTop_1579 relationCoefficients_1579 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1579, relationCoefficients_1579, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1579 : BottomDetBound targetTop_1579 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1579

theorem canonicalBound_1579 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 4 7)) 9 := by
  have htop : targetTop_1579 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1579

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 5, 5)`. -/
def targetTop_1580 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1580 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1580 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1580 : BottomDetBound targetTop_1580 9 := by
  have hU : rowTransform_1580.det.natAbs = 1 := by
    have hdet : rowTransform_1580.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1580 hU
  have hcols := hrows.permuteColumns columnPerm_1580
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1580 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1580 = targetTop_1580 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1580 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 5 5)) 9 := by
  have htop : targetTop_1580 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1580

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 5, 6)`. -/
def targetTop_1581 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1581 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1581 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1581 : BottomDetBound targetTop_1581 9 := by
  have hU : rowTransform_1581.det.natAbs = 1 := by
    have hdet : rowTransform_1581.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Aggregate.bottomBound.transformTopRows rowTransform_1581 hU
  have hcols := hrows.permuteColumns columnPerm_1581
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1581 MainTheory.Generated.BinaryBetaSixKernel.Representative.R035.Base.explicitTop)
          columnPerm_1581 = targetTop_1581 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1581 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 5 6)) 9 := by
  have htop : targetTop_1581 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1581

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 5, 7)`. -/
def targetTop_1582 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1582 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1582 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1582 : BottomDetBound targetTop_1582 9 := by
  have hU : rowTransform_1582.det.natAbs = 1 := by
    have hdet : rowTransform_1582.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1582 hU
  have hcols := hrows.permuteColumns columnPerm_1582
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1582 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1582 = targetTop_1582 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1582 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 5 7)) 9 := by
  have htop : targetTop_1582 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1582

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 6, 6)`. -/
def targetTop_1583 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1583 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1583 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1583 : BottomDetBound targetTop_1583 9 := by
  have hU : rowTransform_1583.det.natAbs = 1 := by
    have hdet : rowTransform_1583.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1583 hU
  have hcols := hrows.permuteColumns columnPerm_1583
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1583 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1583 = targetTop_1583 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1583 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 6 6)) 9 := by
  have htop : targetTop_1583 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1583

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098
