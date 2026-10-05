-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R075.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard097

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 5, 6)`. -/
def targetTop_1552 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1552 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1552 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1552 : BottomDetBound targetTop_1552 9 := by
  have hU : rowTransform_1552.det.natAbs = 1 := by
    have hdet : rowTransform_1552.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1552 hU
  have hcols := hrows.permuteColumns columnPerm_1552
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1552 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1552 = targetTop_1552 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1552 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 5 6)) 9 := by
  have htop : targetTop_1552 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1552

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 5, 7)`. -/
def targetTop_1553 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1553 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1553 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1553 : BottomDetBound targetTop_1553 9 := by
  have hU : rowTransform_1553.det.natAbs = 1 := by
    have hdet : rowTransform_1553.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1553 hU
  have hcols := hrows.permuteColumns columnPerm_1553
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1553 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1553 = targetTop_1553 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1553 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 5 7)) 9 := by
  have htop : targetTop_1553 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1553

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 6, 6)`. -/
def targetTop_1554 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1554 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

def columnPerm_1554 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 3, 1, 2]
  invFun := ![2, 4, 5, 3, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1554 : BottomDetBound targetTop_1554 9 := by
  have hU : rowTransform_1554.det.natAbs = 1 := by
    have hdet : rowTransform_1554.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Aggregate.bottomBound.transformTopRows rowTransform_1554 hU
  have hcols := hrows.permuteColumns columnPerm_1554
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1554 MainTheory.Generated.BinaryBetaSixKernel.Representative.R067.Base.explicitTop)
          columnPerm_1554 = targetTop_1554 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1554 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 6 6)) 9 := by
  have htop : targetTop_1554 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1554

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 6, 7)`. -/
def targetTop_1555 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1555 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1555 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1555 : BottomDetBound targetTop_1555 9 := by
  have hU : rowTransform_1555.det.natAbs = 1 := by
    have hdet : rowTransform_1555.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Aggregate.bottomBound.transformTopRows rowTransform_1555 hU
  have hcols := hrows.permuteColumns columnPerm_1555
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1555 MainTheory.Generated.BinaryBetaSixKernel.Representative.R070.Base.explicitTop)
          columnPerm_1555 = targetTop_1555 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1555 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 6 7)) 9 := by
  have htop : targetTop_1555 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1555

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 7, 7)`. -/
def targetTop_1556 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1556 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1556 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1556 : BottomDetBound targetTop_1556 9 := by
  have hU : rowTransform_1556.det.natAbs = 1 := by
    have hdet : rowTransform_1556.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1556 hU
  have hcols := hrows.permuteColumns columnPerm_1556
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1556 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1556 = targetTop_1556 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1556 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 7 7)) 9 := by
  have htop : targetTop_1556 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1556

/-- Explicit target top block for canonical pattern `(3, 3, 4, 6, 6, 6)`. -/
def targetTop_1557 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1557 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1557 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1557 : BottomDetBound targetTop_1557 9 := by
  have hU : rowTransform_1557.det.natAbs = 1 := by
    have hdet : rowTransform_1557.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1557 hU
  have hcols := hrows.permuteColumns columnPerm_1557
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1557 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1557 = targetTop_1557 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1557 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 6 6 6)) 9 := by
  have htop : targetTop_1557 =
      topOfPattern (R := ℤ) (angle6 3 3 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1557

/-- Explicit target top block for canonical pattern `(3, 3, 4, 6, 6, 7)`. -/
def targetTop_1558 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1558 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1558 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1558 : BottomDetBound targetTop_1558 9 := by
  have hU : rowTransform_1558.det.natAbs = 1 := by
    have hdet : rowTransform_1558.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1558 hU
  have hcols := hrows.permuteColumns columnPerm_1558
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1558 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1558 = targetTop_1558 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1558 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 6 6 7)) 9 := by
  have htop : targetTop_1558 =
      topOfPattern (R := ℤ) (angle6 3 3 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1558

/-- Explicit target top block for canonical pattern `(3, 3, 4, 6, 7, 7)`. -/
def targetTop_1559 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1559 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1559 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1559 : BottomDetBound targetTop_1559 9 := by
  have hU : rowTransform_1559.det.natAbs = 1 := by
    have hdet : rowTransform_1559.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1559 hU
  have hcols := hrows.permuteColumns columnPerm_1559
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1559 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1559 = targetTop_1559 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1559 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 6 7 7)) 9 := by
  have htop : targetTop_1559 =
      topOfPattern (R := ℤ) (angle6 3 3 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1559

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 4, 7, 7, 7)`. -/
def targetTop_1560 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1560 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1560 :
    TopRowRelation targetTop_1560 relationCoefficients_1560 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1560, relationCoefficients_1560, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1560 : BottomDetBound targetTop_1560 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1560

theorem canonicalBound_1560 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 7 7 7)) 9 := by
  have htop : targetTop_1560 =
      topOfPattern (R := ℤ) (angle6 3 3 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1560

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 5, 5, 5, 5)`. -/
def targetTop_1561 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1561 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_1561 :
    TopRowRelation targetTop_1561 relationCoefficients_1561 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1561, relationCoefficients_1561, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1561 : BottomDetBound targetTop_1561 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1561

theorem canonicalBound_1561 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 5 5)) 9 := by
  have htop : targetTop_1561 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1561

/-- Explicit target top block for canonical pattern `(3, 3, 5, 5, 5, 6)`. -/
def targetTop_1562 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1562 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_1562 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1562 : BottomDetBound targetTop_1562 9 := by
  have hU : rowTransform_1562.det.natAbs = 1 := by
    have hdet : rowTransform_1562.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1562 hU
  have hcols := hrows.permuteColumns columnPerm_1562
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1562 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1562 = targetTop_1562 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1562 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 5 6)) 9 := by
  have htop : targetTop_1562 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1562

/-- Explicit target top block for canonical pattern `(3, 3, 5, 5, 5, 7)`. -/
def targetTop_1563 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1563 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1563 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1563 : BottomDetBound targetTop_1563 9 := by
  have hU : rowTransform_1563.det.natAbs = 1 := by
    have hdet : rowTransform_1563.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1563 hU
  have hcols := hrows.permuteColumns columnPerm_1563
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1563 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1563 = targetTop_1563 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1563 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 5 7)) 9 := by
  have htop : targetTop_1563 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1563

/-- Explicit target top block for canonical pattern `(3, 3, 5, 5, 6, 6)`. -/
def targetTop_1564 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1564 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1564 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1564 : BottomDetBound targetTop_1564 9 := by
  have hU : rowTransform_1564.det.natAbs = 1 := by
    have hdet : rowTransform_1564.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R075.Aggregate.bottomBound.transformTopRows rowTransform_1564 hU
  have hcols := hrows.permuteColumns columnPerm_1564
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1564 MainTheory.Generated.BinaryBetaSixKernel.Representative.R075.Base.explicitTop)
          columnPerm_1564 = targetTop_1564 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1564 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 6 6)) 9 := by
  have htop : targetTop_1564 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1564

/-- Explicit target top block for canonical pattern `(3, 3, 5, 5, 6, 7)`. -/
def targetTop_1565 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1565 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1565 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1565 : BottomDetBound targetTop_1565 9 := by
  have hU : rowTransform_1565.det.natAbs = 1 := by
    have hdet : rowTransform_1565.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Aggregate.bottomBound.transformTopRows rowTransform_1565 hU
  have hcols := hrows.permuteColumns columnPerm_1565
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1565 MainTheory.Generated.BinaryBetaSixKernel.Representative.R076.Base.explicitTop)
          columnPerm_1565 = targetTop_1565 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1565 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 6 7)) 9 := by
  have htop : targetTop_1565 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1565

/-- Explicit target top block for canonical pattern `(3, 3, 5, 5, 7, 7)`. -/
def targetTop_1566 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1566 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1566 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1566 : BottomDetBound targetTop_1566 9 := by
  have hU : rowTransform_1566.det.natAbs = 1 := by
    have hdet : rowTransform_1566.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1566 hU
  have hcols := hrows.permuteColumns columnPerm_1566
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1566 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1566 = targetTop_1566 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1566 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 5 7 7)) 9 := by
  have htop : targetTop_1566 =
      topOfPattern (R := ℤ) (angle6 3 3 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1566

/-- Explicit target top block for canonical pattern `(3, 3, 5, 6, 6, 6)`. -/
def targetTop_1567 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1567 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_1567 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1567 : BottomDetBound targetTop_1567 9 := by
  have hU : rowTransform_1567.det.natAbs = 1 := by
    have hdet : rowTransform_1567.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Aggregate.bottomBound.transformTopRows rowTransform_1567 hU
  have hcols := hrows.permuteColumns columnPerm_1567
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1567 MainTheory.Generated.BinaryBetaSixKernel.Representative.R073.Base.explicitTop)
          columnPerm_1567 = targetTop_1567 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1567 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 6 6 6)) 9 := by
  have htop : targetTop_1567 =
      topOfPattern (R := ℤ) (angle6 3 3 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1567

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard097
