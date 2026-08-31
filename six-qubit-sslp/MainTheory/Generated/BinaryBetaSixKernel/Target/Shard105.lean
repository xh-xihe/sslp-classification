-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard105

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(4, 5, 6, 7, 7, 7)`. -/
def targetTop_1680 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1680 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     1, 1, 0]

def columnPerm_1680 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1680 : BottomDetBound targetTop_1680 9 := by
  have hU : rowTransform_1680.det.natAbs = 1 := by
    have hdet : rowTransform_1680.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1680 hU
  have hcols := hrows.permuteColumns columnPerm_1680
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1680 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1680 = targetTop_1680 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1680 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 6 7 7 7)) 9 := by
  have htop : targetTop_1680 =
      topOfPattern (R := ℤ) (angle6 4 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1680

/-- Explicit target top block for canonical pattern `(4, 5, 7, 7, 7, 7)`. -/
def targetTop_1681 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1681 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_1681 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1681 : BottomDetBound targetTop_1681 9 := by
  have hU : rowTransform_1681.det.natAbs = 1 := by
    have hdet : rowTransform_1681.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1681 hU
  have hcols := hrows.permuteColumns columnPerm_1681
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1681 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1681 = targetTop_1681 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1681 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 7 7 7 7)) 9 := by
  have htop : targetTop_1681 =
      topOfPattern (R := ℤ) (angle6 4 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1681

/-- Explicit rank-deficient target for canonical pattern `(4, 6, 6, 6, 6, 6)`. -/
def targetTop_1682 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1682 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1682 :
    TopRowRelation targetTop_1682 relationCoefficients_1682 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1682, relationCoefficients_1682, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1682 : BottomDetBound targetTop_1682 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1682

theorem canonicalBound_1682 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 6 6 6 6)) 9 := by
  have htop : targetTop_1682 =
      topOfPattern (R := ℤ) (angle6 4 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1682

/-- Explicit target top block for canonical pattern `(4, 6, 6, 6, 6, 7)`. -/
def targetTop_1683 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1683 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1683 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1683 : BottomDetBound targetTop_1683 9 := by
  have hU : rowTransform_1683.det.natAbs = 1 := by
    have hdet : rowTransform_1683.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1683 hU
  have hcols := hrows.permuteColumns columnPerm_1683
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1683 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1683 = targetTop_1683 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1683 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 6 6 6 7)) 9 := by
  have htop : targetTop_1683 =
      topOfPattern (R := ℤ) (angle6 4 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1683

/-- Explicit target top block for canonical pattern `(4, 6, 6, 6, 7, 7)`. -/
def targetTop_1684 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1684 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 1, 1]

def columnPerm_1684 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1684 : BottomDetBound targetTop_1684 9 := by
  have hU : rowTransform_1684.det.natAbs = 1 := by
    have hdet : rowTransform_1684.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1684 hU
  have hcols := hrows.permuteColumns columnPerm_1684
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1684 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1684 = targetTop_1684 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1684 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 6 6 7 7)) 9 := by
  have htop : targetTop_1684 =
      topOfPattern (R := ℤ) (angle6 4 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1684

/-- Explicit target top block for canonical pattern `(4, 6, 6, 7, 7, 7)`. -/
def targetTop_1685 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1685 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 1, 1]

def columnPerm_1685 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1685 : BottomDetBound targetTop_1685 9 := by
  have hU : rowTransform_1685.det.natAbs = 1 := by
    have hdet : rowTransform_1685.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1685 hU
  have hcols := hrows.permuteColumns columnPerm_1685
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1685 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1685 = targetTop_1685 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1685 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 6 7 7 7)) 9 := by
  have htop : targetTop_1685 =
      topOfPattern (R := ℤ) (angle6 4 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1685

/-- Explicit target top block for canonical pattern `(4, 6, 7, 7, 7, 7)`. -/
def targetTop_1686 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1686 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     1, 1, 1]

def columnPerm_1686 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1686 : BottomDetBound targetTop_1686 9 := by
  have hU : rowTransform_1686.det.natAbs = 1 := by
    have hdet : rowTransform_1686.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1686 hU
  have hcols := hrows.permuteColumns columnPerm_1686
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1686 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1686 = targetTop_1686 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1686 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 7 7 7 7)) 9 := by
  have htop : targetTop_1686 =
      topOfPattern (R := ℤ) (angle6 4 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1686

/-- Explicit rank-deficient target for canonical pattern `(4, 7, 7, 7, 7, 7)`. -/
def targetTop_1687 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1687 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1687 :
    TopRowRelation targetTop_1687 relationCoefficients_1687 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1687, relationCoefficients_1687, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1687 : BottomDetBound targetTop_1687 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1687

theorem canonicalBound_1687 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 7 7 7 7 7)) 9 := by
  have htop : targetTop_1687 =
      topOfPattern (R := ℤ) (angle6 4 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1687

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 5, 5, 5)`. -/
def targetTop_1688 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1688 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1688 :
    TopRowRelation targetTop_1688 relationCoefficients_1688 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1688, relationCoefficients_1688, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1688 : BottomDetBound targetTop_1688 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1688

theorem canonicalBound_1688 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 5 5)) 9 := by
  have htop : targetTop_1688 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1688

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 5, 5, 6)`. -/
def targetTop_1689 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1689 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_1689 :
    TopRowRelation targetTop_1689 relationCoefficients_1689 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1689, relationCoefficients_1689, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1689 : BottomDetBound targetTop_1689 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1689

theorem canonicalBound_1689 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 5 6)) 9 := by
  have htop : targetTop_1689 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1689

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 5, 5, 7)`. -/
def targetTop_1690 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1690 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1690 :
    TopRowRelation targetTop_1690 relationCoefficients_1690 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1690, relationCoefficients_1690, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1690 : BottomDetBound targetTop_1690 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1690

theorem canonicalBound_1690 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 5 7)) 9 := by
  have htop : targetTop_1690 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1690

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 5, 6, 6)`. -/
def targetTop_1691 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1691 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_1691 :
    TopRowRelation targetTop_1691 relationCoefficients_1691 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1691, relationCoefficients_1691, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1691 : BottomDetBound targetTop_1691 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1691

theorem canonicalBound_1691 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 6 6)) 9 := by
  have htop : targetTop_1691 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1691

/-- Explicit target top block for canonical pattern `(5, 5, 5, 5, 6, 7)`. -/
def targetTop_1692 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1692 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1692 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1692 : BottomDetBound targetTop_1692 9 := by
  have hU : rowTransform_1692.det.natAbs = 1 := by
    have hdet : rowTransform_1692.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1692 hU
  have hcols := hrows.permuteColumns columnPerm_1692
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1692 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1692 = targetTop_1692 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1692 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 6 7)) 9 := by
  have htop : targetTop_1692 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1692

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 5, 7, 7)`. -/
def targetTop_1693 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1693 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1693 :
    TopRowRelation targetTop_1693 relationCoefficients_1693 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1693, relationCoefficients_1693, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1693 : BottomDetBound targetTop_1693 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1693

theorem canonicalBound_1693 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 5 7 7)) 9 := by
  have htop : targetTop_1693 =
      topOfPattern (R := ℤ) (angle6 5 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1693

/-- Explicit rank-deficient target for canonical pattern `(5, 5, 5, 6, 6, 6)`. -/
def targetTop_1694 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1694 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_1694 :
    TopRowRelation targetTop_1694 relationCoefficients_1694 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1694, relationCoefficients_1694, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1694 : BottomDetBound targetTop_1694 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1694

theorem canonicalBound_1694 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 6 6 6)) 9 := by
  have htop : targetTop_1694 =
      topOfPattern (R := ℤ) (angle6 5 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1694

/-- Explicit target top block for canonical pattern `(5, 5, 5, 6, 6, 7)`. -/
def targetTop_1695 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1695 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1695 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1695 : BottomDetBound targetTop_1695 9 := by
  have hU : rowTransform_1695.det.natAbs = 1 := by
    have hdet : rowTransform_1695.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1695 hU
  have hcols := hrows.permuteColumns columnPerm_1695
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1695 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1695 = targetTop_1695 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1695 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 6 6 7)) 9 := by
  have htop : targetTop_1695 =
      topOfPattern (R := ℤ) (angle6 5 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1695

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard105
