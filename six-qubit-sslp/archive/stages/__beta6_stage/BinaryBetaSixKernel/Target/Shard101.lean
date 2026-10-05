-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R078.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard101

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 5, 5, 5, 7, 7)`. -/
def targetTop_1616 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1616 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1616 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1616 : BottomDetBound targetTop_1616 9 := by
  have hU : rowTransform_1616.det.natAbs = 1 := by
    have hdet : rowTransform_1616.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1616 hU
  have hcols := hrows.permuteColumns columnPerm_1616
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1616 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1616 = targetTop_1616 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1616 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 5 7 7)) 9 := by
  have htop : targetTop_1616 =
      topOfPattern (R := ℤ) (angle6 3 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1616

/-- Explicit target top block for canonical pattern `(3, 5, 5, 6, 6, 6)`. -/
def targetTop_1617 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1617 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1617 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1617 : BottomDetBound targetTop_1617 9 := by
  have hU : rowTransform_1617.det.natAbs = 1 := by
    have hdet : rowTransform_1617.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1617 hU
  have hcols := hrows.permuteColumns columnPerm_1617
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1617 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1617 = targetTop_1617 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1617 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 6 6 6)) 9 := by
  have htop : targetTop_1617 =
      topOfPattern (R := ℤ) (angle6 3 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1617

/-- Explicit target top block for canonical pattern `(3, 5, 5, 6, 6, 7)`. -/
def targetTop_1618 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1618 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1618 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1618 : BottomDetBound targetTop_1618 9 := by
  have hU : rowTransform_1618.det.natAbs = 1 := by
    have hdet : rowTransform_1618.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate.bottomBound.transformTopRows rowTransform_1618 hU
  have hcols := hrows.permuteColumns columnPerm_1618
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1618 MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Base.explicitTop)
          columnPerm_1618 = targetTop_1618 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1618 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 6 6 7)) 9 := by
  have htop : targetTop_1618 =
      topOfPattern (R := ℤ) (angle6 3 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1618

/-- Explicit target top block for canonical pattern `(3, 5, 5, 6, 7, 7)`. -/
def targetTop_1619 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1619 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1619 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1619 : BottomDetBound targetTop_1619 9 := by
  have hU : rowTransform_1619.det.natAbs = 1 := by
    have hdet : rowTransform_1619.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Aggregate.bottomBound.transformTopRows rowTransform_1619 hU
  have hcols := hrows.permuteColumns columnPerm_1619
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1619 MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Base.explicitTop)
          columnPerm_1619 = targetTop_1619 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1619 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 6 7 7)) 9 := by
  have htop : targetTop_1619 =
      topOfPattern (R := ℤ) (angle6 3 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1619

/-- Explicit target top block for canonical pattern `(3, 5, 5, 7, 7, 7)`. -/
def targetTop_1620 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1620 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     1, 1, 0]

def columnPerm_1620 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1620 : BottomDetBound targetTop_1620 9 := by
  have hU : rowTransform_1620.det.natAbs = 1 := by
    have hdet : rowTransform_1620.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1620 hU
  have hcols := hrows.permuteColumns columnPerm_1620
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1620 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1620 = targetTop_1620 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1620 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 7 7 7)) 9 := by
  have htop : targetTop_1620 =
      topOfPattern (R := ℤ) (angle6 3 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1620

/-- Explicit target top block for canonical pattern `(3, 5, 6, 6, 6, 6)`. -/
def targetTop_1621 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1621 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1621 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1621 : BottomDetBound targetTop_1621 9 := by
  have hU : rowTransform_1621.det.natAbs = 1 := by
    have hdet : rowTransform_1621.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate.bottomBound.transformTopRows rowTransform_1621 hU
  have hcols := hrows.permuteColumns columnPerm_1621
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1621 MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Base.explicitTop)
          columnPerm_1621 = targetTop_1621 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1621 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 6 6 6 6)) 9 := by
  have htop : targetTop_1621 =
      topOfPattern (R := ℤ) (angle6 3 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1621

/-- Explicit target top block for canonical pattern `(3, 5, 6, 6, 6, 7)`. -/
def targetTop_1622 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1622 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1622 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1622 : BottomDetBound targetTop_1622 9 := by
  have hU : rowTransform_1622.det.natAbs = 1 := by
    have hdet : rowTransform_1622.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Aggregate.bottomBound.transformTopRows rowTransform_1622 hU
  have hcols := hrows.permuteColumns columnPerm_1622
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1622 MainTheory.Generated.BinaryBetaSixKernel.Representative.R074.Base.explicitTop)
          columnPerm_1622 = targetTop_1622 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1622 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 6 6 6 7)) 9 := by
  have htop : targetTop_1622 =
      topOfPattern (R := ℤ) (angle6 3 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1622

/-- Explicit target top block for canonical pattern `(3, 5, 6, 6, 7, 7)`. -/
def targetTop_1623 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1623 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1623 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1623 : BottomDetBound targetTop_1623 9 := by
  have hU : rowTransform_1623.det.natAbs = 1 := by
    have hdet : rowTransform_1623.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Aggregate.bottomBound.transformTopRows rowTransform_1623 hU
  have hcols := hrows.permuteColumns columnPerm_1623
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1623 MainTheory.Generated.BinaryBetaSixKernel.Representative.R077.Base.explicitTop)
          columnPerm_1623 = targetTop_1623 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1623 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 6 6 7 7)) 9 := by
  have htop : targetTop_1623 =
      topOfPattern (R := ℤ) (angle6 3 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1623

/-- Explicit target top block for canonical pattern `(3, 5, 6, 7, 7, 7)`. -/
def targetTop_1624 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1624 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1624 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1624 : BottomDetBound targetTop_1624 9 := by
  have hU : rowTransform_1624.det.natAbs = 1 := by
    have hdet : rowTransform_1624.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R078.Aggregate.bottomBound.transformTopRows rowTransform_1624 hU
  have hcols := hrows.permuteColumns columnPerm_1624
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1624 MainTheory.Generated.BinaryBetaSixKernel.Representative.R078.Base.explicitTop)
          columnPerm_1624 = targetTop_1624 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1624 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 6 7 7 7)) 9 := by
  have htop : targetTop_1624 =
      topOfPattern (R := ℤ) (angle6 3 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1624

/-- Explicit target top block for canonical pattern `(3, 5, 7, 7, 7, 7)`. -/
def targetTop_1625 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1625 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1625 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1625 : BottomDetBound targetTop_1625 9 := by
  have hU : rowTransform_1625.det.natAbs = 1 := by
    have hdet : rowTransform_1625.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1625 hU
  have hcols := hrows.permuteColumns columnPerm_1625
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1625 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1625 = targetTop_1625 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1625 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 7 7 7 7)) 9 := by
  have htop : targetTop_1625 =
      topOfPattern (R := ℤ) (angle6 3 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1625

/-- Explicit rank-deficient target for canonical pattern `(3, 6, 6, 6, 6, 6)`. -/
def targetTop_1626 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1626 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_1626 :
    TopRowRelation targetTop_1626 relationCoefficients_1626 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1626, relationCoefficients_1626, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1626 : BottomDetBound targetTop_1626 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1626

theorem canonicalBound_1626 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 6 6 6 6)) 9 := by
  have htop : targetTop_1626 =
      topOfPattern (R := ℤ) (angle6 3 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1626

/-- Explicit target top block for canonical pattern `(3, 6, 6, 6, 6, 7)`. -/
def targetTop_1627 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1627 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1627 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1627 : BottomDetBound targetTop_1627 9 := by
  have hU : rowTransform_1627.det.natAbs = 1 := by
    have hdet : rowTransform_1627.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1627 hU
  have hcols := hrows.permuteColumns columnPerm_1627
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1627 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1627 = targetTop_1627 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1627 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 6 6 6 7)) 9 := by
  have htop : targetTop_1627 =
      topOfPattern (R := ℤ) (angle6 3 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1627

/-- Explicit target top block for canonical pattern `(3, 6, 6, 6, 7, 7)`. -/
def targetTop_1628 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1628 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 1, 0]

def columnPerm_1628 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1628 : BottomDetBound targetTop_1628 9 := by
  have hU : rowTransform_1628.det.natAbs = 1 := by
    have hdet : rowTransform_1628.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1628 hU
  have hcols := hrows.permuteColumns columnPerm_1628
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1628 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1628 = targetTop_1628 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1628 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 6 6 7 7)) 9 := by
  have htop : targetTop_1628 =
      topOfPattern (R := ℤ) (angle6 3 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1628

/-- Explicit target top block for canonical pattern `(3, 6, 6, 7, 7, 7)`. -/
def targetTop_1629 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1629 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     1, 1, 0]

def columnPerm_1629 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1629 : BottomDetBound targetTop_1629 9 := by
  have hU : rowTransform_1629.det.natAbs = 1 := by
    have hdet : rowTransform_1629.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1629 hU
  have hcols := hrows.permuteColumns columnPerm_1629
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1629 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1629 = targetTop_1629 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1629 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 6 7 7 7)) 9 := by
  have htop : targetTop_1629 =
      topOfPattern (R := ℤ) (angle6 3 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1629

/-- Explicit target top block for canonical pattern `(3, 6, 7, 7, 7, 7)`. -/
def targetTop_1630 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1630 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1630 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1630 : BottomDetBound targetTop_1630 9 := by
  have hU : rowTransform_1630.det.natAbs = 1 := by
    have hdet : rowTransform_1630.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1630 hU
  have hcols := hrows.permuteColumns columnPerm_1630
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1630 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1630 = targetTop_1630 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1630 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 7 7 7 7)) 9 := by
  have htop : targetTop_1630 =
      topOfPattern (R := ℤ) (angle6 3 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1630

/-- Explicit rank-deficient target for canonical pattern `(3, 7, 7, 7, 7, 7)`. -/
def targetTop_1631 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1631 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1631 :
    TopRowRelation targetTop_1631 relationCoefficients_1631 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1631, relationCoefficients_1631, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1631 : BottomDetBound targetTop_1631 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1631

theorem canonicalBound_1631 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 7 7 7 7 7)) 9 := by
  have htop : targetTop_1631 =
      topOfPattern (R := ℤ) (angle6 3 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1631

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard101
