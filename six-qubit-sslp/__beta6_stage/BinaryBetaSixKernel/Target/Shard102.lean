-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard102

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 4, 4)`. -/
def targetTop_1632 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1632 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1632 :
    TopRowRelation targetTop_1632 relationCoefficients_1632 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1632, relationCoefficients_1632, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1632 : BottomDetBound targetTop_1632 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1632

theorem canonicalBound_1632 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 4 4)) 9 := by
  have htop : targetTop_1632 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1632

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 4, 5)`. -/
def targetTop_1633 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1633 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1633 :
    TopRowRelation targetTop_1633 relationCoefficients_1633 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1633, relationCoefficients_1633, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1633 : BottomDetBound targetTop_1633 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1633

theorem canonicalBound_1633 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 4 5)) 9 := by
  have htop : targetTop_1633 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1633

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 4, 6)`. -/
def targetTop_1634 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1634 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1634 :
    TopRowRelation targetTop_1634 relationCoefficients_1634 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1634, relationCoefficients_1634, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1634 : BottomDetBound targetTop_1634 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1634

theorem canonicalBound_1634 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 4 6)) 9 := by
  have htop : targetTop_1634 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1634

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 4, 7)`. -/
def targetTop_1635 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1635 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1635 :
    TopRowRelation targetTop_1635 relationCoefficients_1635 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1635, relationCoefficients_1635, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1635 : BottomDetBound targetTop_1635 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1635

theorem canonicalBound_1635 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 4 7)) 9 := by
  have htop : targetTop_1635 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1635

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 5, 5)`. -/
def targetTop_1636 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1636 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1636 :
    TopRowRelation targetTop_1636 relationCoefficients_1636 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1636, relationCoefficients_1636, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1636 : BottomDetBound targetTop_1636 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1636

theorem canonicalBound_1636 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 5 5)) 9 := by
  have htop : targetTop_1636 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1636

/-- Explicit target top block for canonical pattern `(4, 4, 4, 4, 5, 6)`. -/
def targetTop_1637 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1637 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1637 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1637 : BottomDetBound targetTop_1637 9 := by
  have hU : rowTransform_1637.det.natAbs = 1 := by
    have hdet : rowTransform_1637.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1637 hU
  have hcols := hrows.permuteColumns columnPerm_1637
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1637 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1637 = targetTop_1637 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1637 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 5 6)) 9 := by
  have htop : targetTop_1637 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1637

/-- Explicit target top block for canonical pattern `(4, 4, 4, 4, 5, 7)`. -/
def targetTop_1638 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1638 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1638 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1638 : BottomDetBound targetTop_1638 9 := by
  have hU : rowTransform_1638.det.natAbs = 1 := by
    have hdet : rowTransform_1638.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1638 hU
  have hcols := hrows.permuteColumns columnPerm_1638
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1638 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1638 = targetTop_1638 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1638 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 5 7)) 9 := by
  have htop : targetTop_1638 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1638

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 6, 6)`. -/
def targetTop_1639 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1639 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1639 :
    TopRowRelation targetTop_1639 relationCoefficients_1639 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1639, relationCoefficients_1639, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1639 : BottomDetBound targetTop_1639 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1639

theorem canonicalBound_1639 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 6 6)) 9 := by
  have htop : targetTop_1639 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1639

/-- Explicit target top block for canonical pattern `(4, 4, 4, 4, 6, 7)`. -/
def targetTop_1640 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1640 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_1640 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1640 : BottomDetBound targetTop_1640 9 := by
  have hU : rowTransform_1640.det.natAbs = 1 := by
    have hdet : rowTransform_1640.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1640 hU
  have hcols := hrows.permuteColumns columnPerm_1640
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1640 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1640 = targetTop_1640 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1640 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 6 7)) 9 := by
  have htop : targetTop_1640 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1640

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 4, 7, 7)`. -/
def targetTop_1641 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1641 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1641 :
    TopRowRelation targetTop_1641 relationCoefficients_1641 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1641, relationCoefficients_1641, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1641 : BottomDetBound targetTop_1641 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1641

theorem canonicalBound_1641 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 4 7 7)) 9 := by
  have htop : targetTop_1641 =
      topOfPattern (R := ℤ) (angle6 4 4 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1641

/-- Explicit rank-deficient target for canonical pattern `(4, 4, 4, 5, 5, 5)`. -/
def targetTop_1642 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1642 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_1642 :
    TopRowRelation targetTop_1642 relationCoefficients_1642 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1642, relationCoefficients_1642, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1642 : BottomDetBound targetTop_1642 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1642

theorem canonicalBound_1642 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 5 5)) 9 := by
  have htop : targetTop_1642 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1642

/-- Explicit target top block for canonical pattern `(4, 4, 4, 5, 5, 6)`. -/
def targetTop_1643 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1643 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1643 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1643 : BottomDetBound targetTop_1643 9 := by
  have hU : rowTransform_1643.det.natAbs = 1 := by
    have hdet : rowTransform_1643.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1643 hU
  have hcols := hrows.permuteColumns columnPerm_1643
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1643 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1643 = targetTop_1643 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1643 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 5 6)) 9 := by
  have htop : targetTop_1643 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1643

/-- Explicit target top block for canonical pattern `(4, 4, 4, 5, 5, 7)`. -/
def targetTop_1644 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1644 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_1644 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1644 : BottomDetBound targetTop_1644 9 := by
  have hU : rowTransform_1644.det.natAbs = 1 := by
    have hdet : rowTransform_1644.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1644 hU
  have hcols := hrows.permuteColumns columnPerm_1644
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1644 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1644 = targetTop_1644 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1644 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 5 7)) 9 := by
  have htop : targetTop_1644 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1644

/-- Explicit target top block for canonical pattern `(4, 4, 4, 5, 6, 6)`. -/
def targetTop_1645 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1645 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 1]

def columnPerm_1645 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1645 : BottomDetBound targetTop_1645 9 := by
  have hU : rowTransform_1645.det.natAbs = 1 := by
    have hdet : rowTransform_1645.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1645 hU
  have hcols := hrows.permuteColumns columnPerm_1645
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1645 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1645 = targetTop_1645 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1645 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 6 6)) 9 := by
  have htop : targetTop_1645 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1645

/-- Explicit target top block for canonical pattern `(4, 4, 4, 5, 6, 7)`. -/
def targetTop_1646 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1646 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1646 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1646 : BottomDetBound targetTop_1646 9 := by
  have hU : rowTransform_1646.det.natAbs = 1 := by
    have hdet : rowTransform_1646.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_1646 hU
  have hcols := hrows.permuteColumns columnPerm_1646
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1646 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_1646 = targetTop_1646 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1646 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 6 7)) 9 := by
  have htop : targetTop_1646 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1646

/-- Explicit target top block for canonical pattern `(4, 4, 4, 5, 7, 7)`. -/
def targetTop_1647 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1647 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 1, 1]

def columnPerm_1647 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1647 : BottomDetBound targetTop_1647 9 := by
  have hU : rowTransform_1647.det.natAbs = 1 := by
    have hdet : rowTransform_1647.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1647 hU
  have hcols := hrows.permuteColumns columnPerm_1647
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1647 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1647 = targetTop_1647 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1647 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 5 7 7)) 9 := by
  have htop : targetTop_1647 =
      topOfPattern (R := ℤ) (angle6 4 4 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1647

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard102
