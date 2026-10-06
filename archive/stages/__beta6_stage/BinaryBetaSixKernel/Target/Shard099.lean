-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard099

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 4, 4, 4, 6, 7)`. -/
def targetTop_1584 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1584 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1584 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1584 : BottomDetBound targetTop_1584 9 := by
  have hU : rowTransform_1584.det.natAbs = 1 := by
    have hdet : rowTransform_1584.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1584 hU
  have hcols := hrows.permuteColumns columnPerm_1584
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1584 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1584 = targetTop_1584 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1584 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 6 7)) 9 := by
  have htop : targetTop_1584 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1584

/-- Explicit rank-deficient target for canonical pattern `(3, 4, 4, 4, 7, 7)`. -/
def targetTop_1585 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1585 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1585 :
    TopRowRelation targetTop_1585 relationCoefficients_1585 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1585, relationCoefficients_1585, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1585 : BottomDetBound targetTop_1585 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1585

theorem canonicalBound_1585 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 7 7)) 9 := by
  have htop : targetTop_1585 =
      topOfPattern (R := ℤ) (angle6 3 4 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1585

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 5, 5)`. -/
def targetTop_1586 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1586 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1586 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1586 : BottomDetBound targetTop_1586 9 := by
  have hU : rowTransform_1586.det.natAbs = 1 := by
    have hdet : rowTransform_1586.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1586 hU
  have hcols := hrows.permuteColumns columnPerm_1586
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1586 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1586 = targetTop_1586 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1586 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 5 5)) 9 := by
  have htop : targetTop_1586 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1586

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 5, 6)`. -/
def targetTop_1587 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1587 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1587 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1587 : BottomDetBound targetTop_1587 9 := by
  have hU : rowTransform_1587.det.natAbs = 1 := by
    have hdet : rowTransform_1587.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_1587 hU
  have hcols := hrows.permuteColumns columnPerm_1587
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1587 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_1587 = targetTop_1587 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1587 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 5 6)) 9 := by
  have htop : targetTop_1587 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1587

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 5, 7)`. -/
def targetTop_1588 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1588 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 0]

def columnPerm_1588 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1588 : BottomDetBound targetTop_1588 9 := by
  have hU : rowTransform_1588.det.natAbs = 1 := by
    have hdet : rowTransform_1588.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1588 hU
  have hcols := hrows.permuteColumns columnPerm_1588
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1588 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1588 = targetTop_1588 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1588 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 5 7)) 9 := by
  have htop : targetTop_1588 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1588

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 6, 6)`. -/
def targetTop_1589 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1589 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1589 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 2, 3]
  invFun := ![1, 2, 4, 5, 3, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1589 : BottomDetBound targetTop_1589 9 := by
  have hU : rowTransform_1589.det.natAbs = 1 := by
    have hdet : rowTransform_1589.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Aggregate.bottomBound.transformTopRows rowTransform_1589 hU
  have hcols := hrows.permuteColumns columnPerm_1589
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1589 MainTheory.Generated.BinaryBetaSixKernel.Representative.R051.Base.explicitTop)
          columnPerm_1589 = targetTop_1589 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1589 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 6 6)) 9 := by
  have htop : targetTop_1589 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1589

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 6, 7)`. -/
def targetTop_1590 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1590 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1590 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1590 : BottomDetBound targetTop_1590 9 := by
  have hU : rowTransform_1590.det.natAbs = 1 := by
    have hdet : rowTransform_1590.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Aggregate.bottomBound.transformTopRows rowTransform_1590 hU
  have hcols := hrows.permuteColumns columnPerm_1590
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1590 MainTheory.Generated.BinaryBetaSixKernel.Representative.R053.Base.explicitTop)
          columnPerm_1590 = targetTop_1590 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1590 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 6 7)) 9 := by
  have htop : targetTop_1590 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1590

/-- Explicit target top block for canonical pattern `(3, 4, 4, 5, 7, 7)`. -/
def targetTop_1591 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1591 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1591 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1591 : BottomDetBound targetTop_1591 9 := by
  have hU : rowTransform_1591.det.natAbs = 1 := by
    have hdet : rowTransform_1591.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1591 hU
  have hcols := hrows.permuteColumns columnPerm_1591
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1591 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1591 = targetTop_1591 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1591 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 5 7 7)) 9 := by
  have htop : targetTop_1591 =
      topOfPattern (R := ℤ) (angle6 3 4 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1591

/-- Explicit target top block for canonical pattern `(3, 4, 4, 6, 6, 6)`. -/
def targetTop_1592 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1592 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     1, 1, 0]

def columnPerm_1592 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1592 : BottomDetBound targetTop_1592 9 := by
  have hU : rowTransform_1592.det.natAbs = 1 := by
    have hdet : rowTransform_1592.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1592 hU
  have hcols := hrows.permuteColumns columnPerm_1592
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1592 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1592 = targetTop_1592 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1592 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 6 6 6)) 9 := by
  have htop : targetTop_1592 =
      topOfPattern (R := ℤ) (angle6 3 4 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1592

/-- Explicit target top block for canonical pattern `(3, 4, 4, 6, 6, 7)`. -/
def targetTop_1593 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1593 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1593 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1593 : BottomDetBound targetTop_1593 9 := by
  have hU : rowTransform_1593.det.natAbs = 1 := by
    have hdet : rowTransform_1593.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1593 hU
  have hcols := hrows.permuteColumns columnPerm_1593
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1593 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1593 = targetTop_1593 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1593 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 6 6 7)) 9 := by
  have htop : targetTop_1593 =
      topOfPattern (R := ℤ) (angle6 3 4 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1593

/-- Explicit target top block for canonical pattern `(3, 4, 4, 6, 7, 7)`. -/
def targetTop_1594 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1594 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1594 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1594 : BottomDetBound targetTop_1594 9 := by
  have hU : rowTransform_1594.det.natAbs = 1 := by
    have hdet : rowTransform_1594.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1594 hU
  have hcols := hrows.permuteColumns columnPerm_1594
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1594 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1594 = targetTop_1594 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1594 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 6 7 7)) 9 := by
  have htop : targetTop_1594 =
      topOfPattern (R := ℤ) (angle6 3 4 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1594

/-- Explicit rank-deficient target for canonical pattern `(3, 4, 4, 7, 7, 7)`. -/
def targetTop_1595 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1595 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1595 :
    TopRowRelation targetTop_1595 relationCoefficients_1595 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1595, relationCoefficients_1595, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1595 : BottomDetBound targetTop_1595 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1595

theorem canonicalBound_1595 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 7 7 7)) 9 := by
  have htop : targetTop_1595 =
      topOfPattern (R := ℤ) (angle6 3 4 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1595

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 5, 5)`. -/
def targetTop_1596 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1596 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1596 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1596 : BottomDetBound targetTop_1596 9 := by
  have hU : rowTransform_1596.det.natAbs = 1 := by
    have hdet : rowTransform_1596.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1596 hU
  have hcols := hrows.permuteColumns columnPerm_1596
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1596 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1596 = targetTop_1596 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1596 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 5 5)) 9 := by
  have htop : targetTop_1596 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1596

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 5, 6)`. -/
def targetTop_1597 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 0;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1597 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1597 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1597 : BottomDetBound targetTop_1597 9 := by
  have hU : rowTransform_1597.det.natAbs = 1 := by
    have hdet : rowTransform_1597.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Aggregate.bottomBound.transformTopRows rowTransform_1597 hU
  have hcols := hrows.permuteColumns columnPerm_1597
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1597 MainTheory.Generated.BinaryBetaSixKernel.Representative.R065.Base.explicitTop)
          columnPerm_1597 = targetTop_1597 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1597 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 5 6)) 9 := by
  have htop : targetTop_1597 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1597

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 5, 7)`. -/
def targetTop_1598 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1;
     1, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1598 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1598 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1598 : BottomDetBound targetTop_1598 9 := by
  have hU : rowTransform_1598.det.natAbs = 1 := by
    have hdet : rowTransform_1598.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1598 hU
  have hcols := hrows.permuteColumns columnPerm_1598
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1598 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1598 = targetTop_1598 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1598 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 5 7)) 9 := by
  have htop : targetTop_1598 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1598

/-- Explicit target top block for canonical pattern `(3, 4, 5, 5, 6, 6)`. -/
def targetTop_1599 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1599 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1599 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1599 : BottomDetBound targetTop_1599 9 := by
  have hU : rowTransform_1599.det.natAbs = 1 := by
    have hdet : rowTransform_1599.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Aggregate.bottomBound.transformTopRows rowTransform_1599 hU
  have hcols := hrows.permuteColumns columnPerm_1599
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1599 MainTheory.Generated.BinaryBetaSixKernel.Representative.R066.Base.explicitTop)
          columnPerm_1599 = targetTop_1599 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1599 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 6 6)) 9 := by
  have htop : targetTop_1599 =
      topOfPattern (R := ℤ) (angle6 3 4 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1599

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard099
