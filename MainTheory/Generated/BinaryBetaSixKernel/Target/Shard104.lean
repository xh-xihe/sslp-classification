-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard104

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(4, 4, 6, 6, 7, 7)`. -/
def targetTop_1664 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1664 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1664 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1664 : BottomDetBound targetTop_1664 9 := by
  have hU : rowTransform_1664.det.natAbs = 1 := by
    have hdet : rowTransform_1664.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1664 hU
  have hcols := hrows.permuteColumns columnPerm_1664
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1664 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1664 = targetTop_1664 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1664 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 6 6 7 7)) 9 := by
  have htop : targetTop_1664 =
      topOfPattern (R := ℤ) (angle6 4 4 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1664

/-- Explicit target top block for canonical pattern `(4, 4, 6, 7, 7, 7)`. -/
def targetTop_1665 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1665 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1665 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1665 : BottomDetBound targetTop_1665 9 := by
  have hU : rowTransform_1665.det.natAbs = 1 := by
    have hdet : rowTransform_1665.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1665 hU
  have hcols := hrows.permuteColumns columnPerm_1665
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1665 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1665 = targetTop_1665 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1665 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 6 7 7 7)) 9 := by
  have htop : targetTop_1665 =
      topOfPattern (R := ℤ) (angle6 4 4 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1665

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 7, 7, 7, 7)`. -/
def targetTop_1666 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1666 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1666 :
    TopRowRelation targetTop_1666 relationCoefficients_1666 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1666, relationCoefficients_1666, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1666 : BottomDetBound targetTop_1666 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1666

theorem canonicalBound_1666 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 7 7 7 7)) 9 := by
  have htop : targetTop_1666 =
      topOfPattern (R := ℤ) (angle6 4 4 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1666

/-- Explicit rank-deficient target for canonical pattern `(4, 5, 5, 5, 5, 5)`. -/
def targetTop_1667 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1667 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1667 :
    TopRowRelation targetTop_1667 relationCoefficients_1667 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1667, relationCoefficients_1667, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1667 : BottomDetBound targetTop_1667 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1667

theorem canonicalBound_1667 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 5 5)) 9 := by
  have htop : targetTop_1667 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1667

/-- Explicit target top block for canonical pattern `(4, 5, 5, 5, 5, 6)`. -/
def targetTop_1668 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1668 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1668 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1668 : BottomDetBound targetTop_1668 9 := by
  have hU : rowTransform_1668.det.natAbs = 1 := by
    have hdet : rowTransform_1668.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1668 hU
  have hcols := hrows.permuteColumns columnPerm_1668
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1668 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1668 = targetTop_1668 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1668 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 5 6)) 9 := by
  have htop : targetTop_1668 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1668

/-- Explicit target top block for canonical pattern `(4, 5, 5, 5, 5, 7)`. -/
def targetTop_1669 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1669 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1669 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1669 : BottomDetBound targetTop_1669 9 := by
  have hU : rowTransform_1669.det.natAbs = 1 := by
    have hdet : rowTransform_1669.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1669 hU
  have hcols := hrows.permuteColumns columnPerm_1669
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1669 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1669 = targetTop_1669 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1669 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 5 7)) 9 := by
  have htop : targetTop_1669 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1669

/-- Explicit target top block for canonical pattern `(4, 5, 5, 5, 6, 6)`. -/
def targetTop_1670 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1670 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 1, 1]

def columnPerm_1670 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1670 : BottomDetBound targetTop_1670 9 := by
  have hU : rowTransform_1670.det.natAbs = 1 := by
    have hdet : rowTransform_1670.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1670 hU
  have hcols := hrows.permuteColumns columnPerm_1670
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1670 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1670 = targetTop_1670 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1670 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 6 6)) 9 := by
  have htop : targetTop_1670 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1670

/-- Explicit target top block for canonical pattern `(4, 5, 5, 5, 6, 7)`. -/
def targetTop_1671 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1671 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1671 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1671 : BottomDetBound targetTop_1671 9 := by
  have hU : rowTransform_1671.det.natAbs = 1 := by
    have hdet : rowTransform_1671.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1671 hU
  have hcols := hrows.permuteColumns columnPerm_1671
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1671 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1671 = targetTop_1671 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1671 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 6 7)) 9 := by
  have htop : targetTop_1671 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1671

/-- Explicit target top block for canonical pattern `(4, 5, 5, 5, 7, 7)`. -/
def targetTop_1672 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1672 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 1, 1]

def columnPerm_1672 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1672 : BottomDetBound targetTop_1672 9 := by
  have hU : rowTransform_1672.det.natAbs = 1 := by
    have hdet : rowTransform_1672.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1672 hU
  have hcols := hrows.permuteColumns columnPerm_1672
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1672 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1672 = targetTop_1672 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1672 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 5 7 7)) 9 := by
  have htop : targetTop_1672 =
      topOfPattern (R := ℤ) (angle6 4 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1672

/-- Explicit target top block for canonical pattern `(4, 5, 5, 6, 6, 6)`. -/
def targetTop_1673 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1673 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1673 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1673 : BottomDetBound targetTop_1673 9 := by
  have hU : rowTransform_1673.det.natAbs = 1 := by
    have hdet : rowTransform_1673.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1673 hU
  have hcols := hrows.permuteColumns columnPerm_1673
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1673 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1673 = targetTop_1673 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1673 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 6 6 6)) 9 := by
  have htop : targetTop_1673 =
      topOfPattern (R := ℤ) (angle6 4 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1673

/-- Explicit target top block for canonical pattern `(4, 5, 5, 6, 6, 7)`. -/
def targetTop_1674 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1674 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1674 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1674 : BottomDetBound targetTop_1674 9 := by
  have hU : rowTransform_1674.det.natAbs = 1 := by
    have hdet : rowTransform_1674.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1674 hU
  have hcols := hrows.permuteColumns columnPerm_1674
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1674 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1674 = targetTop_1674 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1674 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 6 6 7)) 9 := by
  have htop : targetTop_1674 =
      topOfPattern (R := ℤ) (angle6 4 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1674

/-- Explicit target top block for canonical pattern `(4, 5, 5, 6, 7, 7)`. -/
def targetTop_1675 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1675 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     1, 1, 0]

def columnPerm_1675 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1675 : BottomDetBound targetTop_1675 9 := by
  have hU : rowTransform_1675.det.natAbs = 1 := by
    have hdet : rowTransform_1675.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1675 hU
  have hcols := hrows.permuteColumns columnPerm_1675
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1675 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1675 = targetTop_1675 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1675 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 6 7 7)) 9 := by
  have htop : targetTop_1675 =
      topOfPattern (R := ℤ) (angle6 4 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1675

/-- Explicit target top block for canonical pattern `(4, 5, 5, 7, 7, 7)`. -/
def targetTop_1676 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1676 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1676 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1676 : BottomDetBound targetTop_1676 9 := by
  have hU : rowTransform_1676.det.natAbs = 1 := by
    have hdet : rowTransform_1676.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1676 hU
  have hcols := hrows.permuteColumns columnPerm_1676
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1676 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1676 = targetTop_1676 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1676 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 7 7 7)) 9 := by
  have htop : targetTop_1676 =
      topOfPattern (R := ℤ) (angle6 4 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1676

/-- Explicit target top block for canonical pattern `(4, 5, 6, 6, 6, 6)`. -/
def targetTop_1677 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1677 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1677 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1677 : BottomDetBound targetTop_1677 9 := by
  have hU : rowTransform_1677.det.natAbs = 1 := by
    have hdet : rowTransform_1677.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1677 hU
  have hcols := hrows.permuteColumns columnPerm_1677
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1677 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1677 = targetTop_1677 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1677 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 6 6 6 6)) 9 := by
  have htop : targetTop_1677 =
      topOfPattern (R := ℤ) (angle6 4 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1677

/-- Explicit target top block for canonical pattern `(4, 5, 6, 6, 6, 7)`. -/
def targetTop_1678 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1678 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_1678 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1678 : BottomDetBound targetTop_1678 9 := by
  have hU : rowTransform_1678.det.natAbs = 1 := by
    have hdet : rowTransform_1678.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1678 hU
  have hcols := hrows.permuteColumns columnPerm_1678
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1678 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1678 = targetTop_1678 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1678 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 6 6 6 7)) 9 := by
  have htop : targetTop_1678 =
      topOfPattern (R := ℤ) (angle6 4 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1678

/-- Explicit target top block for canonical pattern `(4, 5, 6, 6, 7, 7)`. -/
def targetTop_1679 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1679 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     1, 1, 0]

def columnPerm_1679 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1679 : BottomDetBound targetTop_1679 9 := by
  have hU : rowTransform_1679.det.natAbs = 1 := by
    have hdet : rowTransform_1679.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1679 hU
  have hcols := hrows.permuteColumns columnPerm_1679
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1679 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1679 = targetTop_1679 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1679 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 6 6 7 7)) 9 := by
  have htop : targetTop_1679 =
      topOfPattern (R := ℤ) (angle6 4 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1679

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard104
