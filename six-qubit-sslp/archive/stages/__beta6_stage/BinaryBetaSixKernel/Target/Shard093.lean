-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard093

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 5, 5, 5, 6, 6)`. -/
def targetTop_1488 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1488 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1488 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1488 : BottomDetBound targetTop_1488 9 := by
  have hU : rowTransform_1488.det.natAbs = 1 := by
    have hdet : rowTransform_1488.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1488 hU
  have hcols := hrows.permuteColumns columnPerm_1488
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1488 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1488 = targetTop_1488 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1488 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 6 6)) 9 := by
  have htop : targetTop_1488 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1488

/-- Explicit target top block for canonical pattern `(2, 5, 5, 5, 6, 7)`. -/
def targetTop_1489 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1489 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1489 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1489 : BottomDetBound targetTop_1489 9 := by
  have hU : rowTransform_1489.det.natAbs = 1 := by
    have hdet : rowTransform_1489.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_1489 hU
  have hcols := hrows.permuteColumns columnPerm_1489
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1489 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_1489 = targetTop_1489 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1489 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 6 7)) 9 := by
  have htop : targetTop_1489 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1489

/-- Explicit rank-deficient target for canonical pattern `(2, 5, 5, 5, 7, 7)`. -/
def targetTop_1490 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1490 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1490 :
    TopRowRelation targetTop_1490 relationCoefficients_1490 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1490, relationCoefficients_1490, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1490 : BottomDetBound targetTop_1490 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1490

theorem canonicalBound_1490 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 7 7)) 9 := by
  have htop : targetTop_1490 =
      topOfPattern (R := ℤ) (angle6 2 5 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1490

/-- Explicit target top block for canonical pattern `(2, 5, 5, 6, 6, 6)`. -/
def targetTop_1491 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1491 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     1, 1, 0]

def columnPerm_1491 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1491 : BottomDetBound targetTop_1491 9 := by
  have hU : rowTransform_1491.det.natAbs = 1 := by
    have hdet : rowTransform_1491.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1491 hU
  have hcols := hrows.permuteColumns columnPerm_1491
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1491 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1491 = targetTop_1491 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1491 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 6 6 6)) 9 := by
  have htop : targetTop_1491 =
      topOfPattern (R := ℤ) (angle6 2 5 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1491

/-- Explicit target top block for canonical pattern `(2, 5, 5, 6, 6, 7)`. -/
def targetTop_1492 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1492 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 1, 0]

def columnPerm_1492 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1492 : BottomDetBound targetTop_1492 9 := by
  have hU : rowTransform_1492.det.natAbs = 1 := by
    have hdet : rowTransform_1492.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Aggregate.bottomBound.transformTopRows rowTransform_1492 hU
  have hcols := hrows.permuteColumns columnPerm_1492
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1492 MainTheory.Generated.BinaryBetaSixKernel.Representative.R038.Base.explicitTop)
          columnPerm_1492 = targetTop_1492 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1492 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 6 6 7)) 9 := by
  have htop : targetTop_1492 =
      topOfPattern (R := ℤ) (angle6 2 5 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1492

/-- Explicit target top block for canonical pattern `(2, 5, 5, 6, 7, 7)`. -/
def targetTop_1493 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1493 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1493 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1493 : BottomDetBound targetTop_1493 9 := by
  have hU : rowTransform_1493.det.natAbs = 1 := by
    have hdet : rowTransform_1493.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Aggregate.bottomBound.transformTopRows rowTransform_1493 hU
  have hcols := hrows.permuteColumns columnPerm_1493
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1493 MainTheory.Generated.BinaryBetaSixKernel.Representative.R041.Base.explicitTop)
          columnPerm_1493 = targetTop_1493 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1493 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 6 7 7)) 9 := by
  have htop : targetTop_1493 =
      topOfPattern (R := ℤ) (angle6 2 5 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1493

/-- Explicit rank-deficient target for canonical pattern `(2, 5, 5, 7, 7, 7)`. -/
def targetTop_1494 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1494 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1494 :
    TopRowRelation targetTop_1494 relationCoefficients_1494 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1494, relationCoefficients_1494, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1494 : BottomDetBound targetTop_1494 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1494

theorem canonicalBound_1494 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 7 7 7)) 9 := by
  have htop : targetTop_1494 =
      topOfPattern (R := ℤ) (angle6 2 5 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1494

/-- Explicit target top block for canonical pattern `(2, 5, 6, 6, 6, 6)`. -/
def targetTop_1495 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1495 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1495 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1495 : BottomDetBound targetTop_1495 9 := by
  have hU : rowTransform_1495.det.natAbs = 1 := by
    have hdet : rowTransform_1495.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1495 hU
  have hcols := hrows.permuteColumns columnPerm_1495
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1495 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1495 = targetTop_1495 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1495 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 6 6 6 6)) 9 := by
  have htop : targetTop_1495 =
      topOfPattern (R := ℤ) (angle6 2 5 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1495

/-- Explicit target top block for canonical pattern `(2, 5, 6, 6, 6, 7)`. -/
def targetTop_1496 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1496 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1496 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1496 : BottomDetBound targetTop_1496 9 := by
  have hU : rowTransform_1496.det.natAbs = 1 := by
    have hdet : rowTransform_1496.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_1496 hU
  have hcols := hrows.permuteColumns columnPerm_1496
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1496 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_1496 = targetTop_1496 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1496 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 6 6 6 7)) 9 := by
  have htop : targetTop_1496 =
      topOfPattern (R := ℤ) (angle6 2 5 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1496

/-- Explicit target top block for canonical pattern `(2, 5, 6, 6, 7, 7)`. -/
def targetTop_1497 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1497 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_1497 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1497 : BottomDetBound targetTop_1497 9 := by
  have hU : rowTransform_1497.det.natAbs = 1 := by
    have hdet : rowTransform_1497.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Aggregate.bottomBound.transformTopRows rowTransform_1497 hU
  have hcols := hrows.permuteColumns columnPerm_1497
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1497 MainTheory.Generated.BinaryBetaSixKernel.Representative.R046.Base.explicitTop)
          columnPerm_1497 = targetTop_1497 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1497 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 6 6 7 7)) 9 := by
  have htop : targetTop_1497 =
      topOfPattern (R := ℤ) (angle6 2 5 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1497

/-- Explicit target top block for canonical pattern `(2, 5, 6, 7, 7, 7)`. -/
def targetTop_1498 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1498 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1498 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1498 : BottomDetBound targetTop_1498 9 := by
  have hU : rowTransform_1498.det.natAbs = 1 := by
    have hdet : rowTransform_1498.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Aggregate.bottomBound.transformTopRows rowTransform_1498 hU
  have hcols := hrows.permuteColumns columnPerm_1498
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1498 MainTheory.Generated.BinaryBetaSixKernel.Representative.R054.Base.explicitTop)
          columnPerm_1498 = targetTop_1498 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1498 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 6 7 7 7)) 9 := by
  have htop : targetTop_1498 =
      topOfPattern (R := ℤ) (angle6 2 5 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1498

/-- Explicit rank-deficient target for canonical pattern `(2, 5, 7, 7, 7, 7)`. -/
def targetTop_1499 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1499 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1499 :
    TopRowRelation targetTop_1499 relationCoefficients_1499 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1499, relationCoefficients_1499, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1499 : BottomDetBound targetTop_1499 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1499

theorem canonicalBound_1499 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 7 7 7 7)) 9 := by
  have htop : targetTop_1499 =
      topOfPattern (R := ℤ) (angle6 2 5 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1499

/-- Explicit rank-deficient target for canonical pattern `(2, 6, 6, 6, 6, 6)`. -/
def targetTop_1500 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1500 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_1500 :
    TopRowRelation targetTop_1500 relationCoefficients_1500 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1500, relationCoefficients_1500, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1500 : BottomDetBound targetTop_1500 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1500

theorem canonicalBound_1500 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 6 6 6 6)) 9 := by
  have htop : targetTop_1500 =
      topOfPattern (R := ℤ) (angle6 2 6 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1500

/-- Explicit target top block for canonical pattern `(2, 6, 6, 6, 6, 7)`. -/
def targetTop_1501 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1501 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1501 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1501 : BottomDetBound targetTop_1501 9 := by
  have hU : rowTransform_1501.det.natAbs = 1 := by
    have hdet : rowTransform_1501.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1501 hU
  have hcols := hrows.permuteColumns columnPerm_1501
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1501 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1501 = targetTop_1501 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1501 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 6 6 6 7)) 9 := by
  have htop : targetTop_1501 =
      topOfPattern (R := ℤ) (angle6 2 6 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1501

/-- Explicit target top block for canonical pattern `(2, 6, 6, 6, 7, 7)`. -/
def targetTop_1502 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1502 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     1, 1, 0]

def columnPerm_1502 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1502 : BottomDetBound targetTop_1502 9 := by
  have hU : rowTransform_1502.det.natAbs = 1 := by
    have hdet : rowTransform_1502.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1502 hU
  have hcols := hrows.permuteColumns columnPerm_1502
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1502 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1502 = targetTop_1502 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1502 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 6 6 7 7)) 9 := by
  have htop : targetTop_1502 =
      topOfPattern (R := ℤ) (angle6 2 6 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1502

/-- Explicit target top block for canonical pattern `(2, 6, 6, 7, 7, 7)`. -/
def targetTop_1503 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1503 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     1, 1, 0]

def columnPerm_1503 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1503 : BottomDetBound targetTop_1503 9 := by
  have hU : rowTransform_1503.det.natAbs = 1 := by
    have hdet : rowTransform_1503.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1503 hU
  have hcols := hrows.permuteColumns columnPerm_1503
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1503 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1503 = targetTop_1503 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1503 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 6 7 7 7)) 9 := by
  have htop : targetTop_1503 =
      topOfPattern (R := ℤ) (angle6 2 6 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1503

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard093
