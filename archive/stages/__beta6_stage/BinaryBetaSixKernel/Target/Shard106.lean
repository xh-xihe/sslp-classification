-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard106

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(5, 5, 5, 6, 7, 7)`. -/
def targetTop_1696 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1696 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1696 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1696 : BottomDetBound targetTop_1696 9 := by
  have hU : rowTransform_1696.det.natAbs = 1 := by
    have hdet : rowTransform_1696.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1696 hU
  have hcols := hrows.permuteColumns columnPerm_1696
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1696 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1696 = targetTop_1696 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1696 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 6 7 7)) 9 := by
  have htop : targetTop_1696 =
      topOfPattern (R := ℤ) (angle6 5 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1696

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 7, 7, 7)`. -/
def targetTop_1697 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1697 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1697 :
    TopRowRelation targetTop_1697 relationCoefficients_1697 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1697, relationCoefficients_1697, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1697 : BottomDetBound targetTop_1697 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1697

theorem canonicalBound_1697 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 7 7 7)) 9 := by
  have htop : targetTop_1697 =
      topOfPattern (R := ℤ) (angle6 5 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1697

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 6, 6, 6, 6)`. -/
def targetTop_1698 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1698 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_1698 :
    TopRowRelation targetTop_1698 relationCoefficients_1698 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1698, relationCoefficients_1698, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1698 : BottomDetBound targetTop_1698 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1698

theorem canonicalBound_1698 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 6 6 6 6)) 9 := by
  have htop : targetTop_1698 =
      topOfPattern (R := ℤ) (angle6 5 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1698

/-- Explicit target top block for canonical pattern `(5, 5, 6, 6, 6, 7)`. -/
def targetTop_1699 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1699 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1699 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1699 : BottomDetBound targetTop_1699 9 := by
  have hU : rowTransform_1699.det.natAbs = 1 := by
    have hdet : rowTransform_1699.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1699 hU
  have hcols := hrows.permuteColumns columnPerm_1699
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1699 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1699 = targetTop_1699 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1699 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 6 6 6 7)) 9 := by
  have htop : targetTop_1699 =
      topOfPattern (R := ℤ) (angle6 5 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1699

/-- Explicit target top block for canonical pattern `(5, 5, 6, 6, 7, 7)`. -/
def targetTop_1700 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1700 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1700 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1700 : BottomDetBound targetTop_1700 9 := by
  have hU : rowTransform_1700.det.natAbs = 1 := by
    have hdet : rowTransform_1700.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1700 hU
  have hcols := hrows.permuteColumns columnPerm_1700
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1700 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1700 = targetTop_1700 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1700 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 6 6 7 7)) 9 := by
  have htop : targetTop_1700 =
      topOfPattern (R := ℤ) (angle6 5 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1700

/-- Explicit target top block for canonical pattern `(5, 5, 6, 7, 7, 7)`. -/
def targetTop_1701 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1701 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1701 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1701 : BottomDetBound targetTop_1701 9 := by
  have hU : rowTransform_1701.det.natAbs = 1 := by
    have hdet : rowTransform_1701.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1701 hU
  have hcols := hrows.permuteColumns columnPerm_1701
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1701 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1701 = targetTop_1701 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1701 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 6 7 7 7)) 9 := by
  have htop : targetTop_1701 =
      topOfPattern (R := ℤ) (angle6 5 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1701

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 7, 7, 7, 7)`. -/
def targetTop_1702 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1702 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1702 :
    TopRowRelation targetTop_1702 relationCoefficients_1702 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1702, relationCoefficients_1702, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1702 : BottomDetBound targetTop_1702 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1702

theorem canonicalBound_1702 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 7 7 7 7)) 9 := by
  have htop : targetTop_1702 =
      topOfPattern (R := ℤ) (angle6 5 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1702

/-- Explicit rank-deficient target for canonical pattern `(5, 6, 6, 6, 6, 6)`. -/
def targetTop_1703 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1703 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_1703 :
    TopRowRelation targetTop_1703 relationCoefficients_1703 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1703, relationCoefficients_1703, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1703 : BottomDetBound targetTop_1703 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1703

theorem canonicalBound_1703 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 6 6 6 6)) 9 := by
  have htop : targetTop_1703 =
      topOfPattern (R := ℤ) (angle6 5 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1703

/-- Explicit target top block for canonical pattern `(5, 6, 6, 6, 6, 7)`. -/
def targetTop_1704 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1704 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1704 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1704 : BottomDetBound targetTop_1704 9 := by
  have hU : rowTransform_1704.det.natAbs = 1 := by
    have hdet : rowTransform_1704.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1704 hU
  have hcols := hrows.permuteColumns columnPerm_1704
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1704 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1704 = targetTop_1704 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1704 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 6 6 6 7)) 9 := by
  have htop : targetTop_1704 =
      topOfPattern (R := ℤ) (angle6 5 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1704

/-- Explicit target top block for canonical pattern `(5, 6, 6, 6, 7, 7)`. -/
def targetTop_1705 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1705 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     1, 1, 1]

def columnPerm_1705 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1705 : BottomDetBound targetTop_1705 9 := by
  have hU : rowTransform_1705.det.natAbs = 1 := by
    have hdet : rowTransform_1705.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1705 hU
  have hcols := hrows.permuteColumns columnPerm_1705
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1705 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1705 = targetTop_1705 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1705 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 6 6 7 7)) 9 := by
  have htop : targetTop_1705 =
      topOfPattern (R := ℤ) (angle6 5 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1705

/-- Explicit target top block for canonical pattern `(5, 6, 6, 7, 7, 7)`. -/
def targetTop_1706 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1706 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     1, 1, 1]

def columnPerm_1706 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1706 : BottomDetBound targetTop_1706 9 := by
  have hU : rowTransform_1706.det.natAbs = 1 := by
    have hdet : rowTransform_1706.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1706 hU
  have hcols := hrows.permuteColumns columnPerm_1706
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1706 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1706 = targetTop_1706 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1706 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 6 7 7 7)) 9 := by
  have htop : targetTop_1706 =
      topOfPattern (R := ℤ) (angle6 5 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1706

/-- Explicit target top block for canonical pattern `(5, 6, 7, 7, 7, 7)`. -/
def targetTop_1707 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1707 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1707 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1707 : BottomDetBound targetTop_1707 9 := by
  have hU : rowTransform_1707.det.natAbs = 1 := by
    have hdet : rowTransform_1707.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1707 hU
  have hcols := hrows.permuteColumns columnPerm_1707
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1707 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1707 = targetTop_1707 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1707 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 7 7 7 7)) 9 := by
  have htop : targetTop_1707 =
      topOfPattern (R := ℤ) (angle6 5 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1707

/-- Explicit rank-deficient target for canonical pattern `(5, 7, 7, 7, 7, 7)`. -/
def targetTop_1708 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1708 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1708 :
    TopRowRelation targetTop_1708 relationCoefficients_1708 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1708, relationCoefficients_1708, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1708 : BottomDetBound targetTop_1708 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1708

theorem canonicalBound_1708 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 7 7 7 7 7)) 9 := by
  have htop : targetTop_1708 =
      topOfPattern (R := ℤ) (angle6 5 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1708

/-- Explicit rank-deficient target for canonical pattern `(6, 6, 6, 6, 6, 6)`. -/
def targetTop_1709 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1709 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1709 :
    TopRowRelation targetTop_1709 relationCoefficients_1709 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1709, relationCoefficients_1709, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1709 : BottomDetBound targetTop_1709 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1709

theorem canonicalBound_1709 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 6 6 6 6)) 9 := by
  have htop : targetTop_1709 =
      topOfPattern (R := ℤ) (angle6 6 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1709

/-- Explicit rank-deficient target for canonical pattern `(6, 6, 6, 6, 6, 7)`. -/
def targetTop_1710 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1710 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1710 :
    TopRowRelation targetTop_1710 relationCoefficients_1710 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1710, relationCoefficients_1710, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1710 : BottomDetBound targetTop_1710 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1710

theorem canonicalBound_1710 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 6 6 6 7)) 9 := by
  have htop : targetTop_1710 =
      topOfPattern (R := ℤ) (angle6 6 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1710

/-- Explicit rank-deficient target for canonical pattern `(6, 6, 6, 6, 7, 7)`. -/
def targetTop_1711 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1711 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_1711 :
    TopRowRelation targetTop_1711 relationCoefficients_1711 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1711, relationCoefficients_1711, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1711 : BottomDetBound targetTop_1711 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1711

theorem canonicalBound_1711 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 6 6 7 7)) 9 := by
  have htop : targetTop_1711 =
      topOfPattern (R := ℤ) (angle6 6 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1711

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard106
