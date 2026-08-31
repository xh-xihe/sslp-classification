-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard103

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 6, 6, 6)`. -/
def targetTop_1648 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1648 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1648 :
    TopRowRelation targetTop_1648 relationCoefficients_1648 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1648, relationCoefficients_1648, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1648 : BottomDetBound targetTop_1648 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1648

theorem canonicalBound_1648 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 6 6 6)) 9 := by
  have htop : targetTop_1648 =
      topOfPattern (R := ℤ) (angle6 4 4 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1648

/-- Explicit target top block for canonical pattern `(4, 4, 4, 6, 6, 7)`. -/
def targetTop_1649 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1649 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1649 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1649 : BottomDetBound targetTop_1649 9 := by
  have hU : rowTransform_1649.det.natAbs = 1 := by
    have hdet : rowTransform_1649.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1649 hU
  have hcols := hrows.permuteColumns columnPerm_1649
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1649 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1649 = targetTop_1649 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1649 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 6 6 7)) 9 := by
  have htop : targetTop_1649 =
      topOfPattern (R := ℤ) (angle6 4 4 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1649

/-- Explicit target top block for canonical pattern `(4, 4, 4, 6, 7, 7)`. -/
def targetTop_1650 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1650 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1650 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1650 : BottomDetBound targetTop_1650 9 := by
  have hU : rowTransform_1650.det.natAbs = 1 := by
    have hdet : rowTransform_1650.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1650 hU
  have hcols := hrows.permuteColumns columnPerm_1650
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1650 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1650 = targetTop_1650 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1650 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 6 7 7)) 9 := by
  have htop : targetTop_1650 =
      topOfPattern (R := ℤ) (angle6 4 4 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1650

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 7, 7, 7)`. -/
def targetTop_1651 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1651 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1651 :
    TopRowRelation targetTop_1651 relationCoefficients_1651 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1651, relationCoefficients_1651, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1651 : BottomDetBound targetTop_1651 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1651

theorem canonicalBound_1651 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 7 7 7)) 9 := by
  have htop : targetTop_1651 =
      topOfPattern (R := ℤ) (angle6 4 4 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1651

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 5, 5, 5, 5)`. -/
def targetTop_1652 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1652 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1652 :
    TopRowRelation targetTop_1652 relationCoefficients_1652 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1652, relationCoefficients_1652, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1652 : BottomDetBound targetTop_1652 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1652

theorem canonicalBound_1652 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 5 5)) 9 := by
  have htop : targetTop_1652 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1652

/-- Explicit target top block for canonical pattern `(4, 4, 5, 5, 5, 6)`. -/
def targetTop_1653 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1653 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1653 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1653 : BottomDetBound targetTop_1653 9 := by
  have hU : rowTransform_1653.det.natAbs = 1 := by
    have hdet : rowTransform_1653.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1653 hU
  have hcols := hrows.permuteColumns columnPerm_1653
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1653 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1653 = targetTop_1653 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1653 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 5 6)) 9 := by
  have htop : targetTop_1653 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1653

/-- Explicit target top block for canonical pattern `(4, 4, 5, 5, 5, 7)`. -/
def targetTop_1654 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1654 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1654 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1654 : BottomDetBound targetTop_1654 9 := by
  have hU : rowTransform_1654.det.natAbs = 1 := by
    have hdet : rowTransform_1654.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1654 hU
  have hcols := hrows.permuteColumns columnPerm_1654
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1654 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1654 = targetTop_1654 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1654 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 5 7)) 9 := by
  have htop : targetTop_1654 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1654

/-- Explicit target top block for canonical pattern `(4, 4, 5, 5, 6, 6)`. -/
def targetTop_1655 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1655 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1655 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1655 : BottomDetBound targetTop_1655 9 := by
  have hU : rowTransform_1655.det.natAbs = 1 := by
    have hdet : rowTransform_1655.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1655 hU
  have hcols := hrows.permuteColumns columnPerm_1655
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1655 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1655 = targetTop_1655 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1655 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 6 6)) 9 := by
  have htop : targetTop_1655 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1655

/-- Explicit target top block for canonical pattern `(4, 4, 5, 5, 6, 7)`. -/
def targetTop_1656 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1656 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1656 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1656 : BottomDetBound targetTop_1656 9 := by
  have hU : rowTransform_1656.det.natAbs = 1 := by
    have hdet : rowTransform_1656.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1656 hU
  have hcols := hrows.permuteColumns columnPerm_1656
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1656 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1656 = targetTop_1656 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1656 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 6 7)) 9 := by
  have htop : targetTop_1656 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1656

/-- Explicit target top block for canonical pattern `(4, 4, 5, 5, 7, 7)`. -/
def targetTop_1657 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1657 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1657 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1657 : BottomDetBound targetTop_1657 9 := by
  have hU : rowTransform_1657.det.natAbs = 1 := by
    have hdet : rowTransform_1657.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1657 hU
  have hcols := hrows.permuteColumns columnPerm_1657
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1657 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1657 = targetTop_1657 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1657 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 5 7 7)) 9 := by
  have htop : targetTop_1657 =
      topOfPattern (R := ℤ) (angle6 4 4 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1657

/-- Explicit target top block for canonical pattern `(4, 4, 5, 6, 6, 6)`. -/
def targetTop_1658 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1658 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1658 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1658 : BottomDetBound targetTop_1658 9 := by
  have hU : rowTransform_1658.det.natAbs = 1 := by
    have hdet : rowTransform_1658.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1658 hU
  have hcols := hrows.permuteColumns columnPerm_1658
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1658 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1658 = targetTop_1658 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1658 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 6 6 6)) 9 := by
  have htop : targetTop_1658 =
      topOfPattern (R := ℤ) (angle6 4 4 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1658

/-- Explicit target top block for canonical pattern `(4, 4, 5, 6, 6, 7)`. -/
def targetTop_1659 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1659 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 0]

def columnPerm_1659 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1659 : BottomDetBound targetTop_1659 9 := by
  have hU : rowTransform_1659.det.natAbs = 1 := by
    have hdet : rowTransform_1659.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Aggregate.bottomBound.transformTopRows rowTransform_1659 hU
  have hcols := hrows.permuteColumns columnPerm_1659
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1659 MainTheory.Generated.BinaryBetaSixKernel.Representative.R040.Base.explicitTop)
          columnPerm_1659 = targetTop_1659 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1659 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 6 6 7)) 9 := by
  have htop : targetTop_1659 =
      topOfPattern (R := ℤ) (angle6 4 4 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1659

/-- Explicit target top block for canonical pattern `(4, 4, 5, 6, 7, 7)`. -/
def targetTop_1660 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1660 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1660 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1660 : BottomDetBound targetTop_1660 9 := by
  have hU : rowTransform_1660.det.natAbs = 1 := by
    have hdet : rowTransform_1660.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Aggregate.bottomBound.transformTopRows rowTransform_1660 hU
  have hcols := hrows.permuteColumns columnPerm_1660
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1660 MainTheory.Generated.BinaryBetaSixKernel.Representative.R049.Base.explicitTop)
          columnPerm_1660 = targetTop_1660 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1660 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 6 7 7)) 9 := by
  have htop : targetTop_1660 =
      topOfPattern (R := ℤ) (angle6 4 4 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1660

/-- Explicit target top block for canonical pattern `(4, 4, 5, 7, 7, 7)`. -/
def targetTop_1661 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1661 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1661 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1661 : BottomDetBound targetTop_1661 9 := by
  have hU : rowTransform_1661.det.natAbs = 1 := by
    have hdet : rowTransform_1661.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1661 hU
  have hcols := hrows.permuteColumns columnPerm_1661
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1661 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1661 = targetTop_1661 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1661 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 7 7 7)) 9 := by
  have htop : targetTop_1661 =
      topOfPattern (R := ℤ) (angle6 4 4 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1661

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 6, 6, 6, 6)`. -/
def targetTop_1662 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1662 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1662 :
    TopRowRelation targetTop_1662 relationCoefficients_1662 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1662, relationCoefficients_1662, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1662 : BottomDetBound targetTop_1662 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1662

theorem canonicalBound_1662 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 6 6 6 6)) 9 := by
  have htop : targetTop_1662 =
      topOfPattern (R := ℤ) (angle6 4 4 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1662

/-- Explicit target top block for canonical pattern `(4, 4, 6, 6, 6, 7)`. -/
def targetTop_1663 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1663 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1663 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1663 : BottomDetBound targetTop_1663 9 := by
  have hU : rowTransform_1663.det.natAbs = 1 := by
    have hdet : rowTransform_1663.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1663 hU
  have hcols := hrows.permuteColumns columnPerm_1663
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1663 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1663 = targetTop_1663 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1663 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 6 6 6 7)) 9 := by
  have htop : targetTop_1663 =
      topOfPattern (R := ℤ) (angle6 4 4 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1663

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard103
