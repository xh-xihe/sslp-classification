-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(2, 6, 7, 7, 7, 7)`. -/
def targetTop_1504 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1504 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_1504 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1504 : BottomDetBound targetTop_1504 9 := by
  have hU : rowTransform_1504.det.natAbs = 1 := by
    have hdet : rowTransform_1504.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1504 hU
  have hcols := hrows.permuteColumns columnPerm_1504
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1504 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1504 = targetTop_1504 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1504 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 7 7 7 7)) 9 := by
  have htop : targetTop_1504 =
      topOfPattern (R := ℤ) (angle6 2 6 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1504

/-- Explicit rank-deficient target for canonical pattern `(2, 7, 7, 7, 7, 7)`. -/
def targetTop_1505 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1505 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_1505 :
    TopRowRelation targetTop_1505 relationCoefficients_1505 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1505, relationCoefficients_1505, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1505 : BottomDetBound targetTop_1505 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1505

theorem canonicalBound_1505 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 7 7 7 7 7)) 9 := by
  have htop : targetTop_1505 =
      topOfPattern (R := ℤ) (angle6 2 7 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1505

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 3, 3)`. -/
def targetTop_1506 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1506 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1506 :
    TopRowRelation targetTop_1506 relationCoefficients_1506 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1506, relationCoefficients_1506, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1506 : BottomDetBound targetTop_1506 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1506

theorem canonicalBound_1506 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 3)) 9 := by
  have htop : targetTop_1506 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1506

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 3, 4)`. -/
def targetTop_1507 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1507 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1507 :
    TopRowRelation targetTop_1507 relationCoefficients_1507 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1507, relationCoefficients_1507, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1507 : BottomDetBound targetTop_1507 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1507

theorem canonicalBound_1507 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 4)) 9 := by
  have htop : targetTop_1507 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1507

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 3, 5)`. -/
def targetTop_1508 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1508 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_1508 :
    TopRowRelation targetTop_1508 relationCoefficients_1508 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1508, relationCoefficients_1508, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1508 : BottomDetBound targetTop_1508 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1508

theorem canonicalBound_1508 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 5)) 9 := by
  have htop : targetTop_1508 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1508

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 3, 6)`. -/
def targetTop_1509 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1509 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_1509 :
    TopRowRelation targetTop_1509 relationCoefficients_1509 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1509, relationCoefficients_1509, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1509 : BottomDetBound targetTop_1509 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1509

theorem canonicalBound_1509 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 6)) 9 := by
  have htop : targetTop_1509 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1509

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 3, 7)`. -/
def targetTop_1510 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1510 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1510 :
    TopRowRelation targetTop_1510 relationCoefficients_1510 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1510, relationCoefficients_1510, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1510 : BottomDetBound targetTop_1510 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1510

theorem canonicalBound_1510 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 7)) 9 := by
  have htop : targetTop_1510 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1510

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 4, 4)`. -/
def targetTop_1511 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1511 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1511 :
    TopRowRelation targetTop_1511 relationCoefficients_1511 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1511, relationCoefficients_1511, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1511 : BottomDetBound targetTop_1511 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1511

theorem canonicalBound_1511 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 4 4)) 9 := by
  have htop : targetTop_1511 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1511

/-- Explicit target top block for canonical pattern `(3, 3, 3, 3, 4, 5)`. -/
def targetTop_1512 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1512 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1512 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1512 : BottomDetBound targetTop_1512 9 := by
  have hU : rowTransform_1512.det.natAbs = 1 := by
    have hdet : rowTransform_1512.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1512 hU
  have hcols := hrows.permuteColumns columnPerm_1512
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1512 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1512 = targetTop_1512 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1512 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 4 5)) 9 := by
  have htop : targetTop_1512 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1512

/-- Explicit target top block for canonical pattern `(3, 3, 3, 3, 4, 6)`. -/
def targetTop_1513 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1513 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1513 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1513 : BottomDetBound targetTop_1513 9 := by
  have hU : rowTransform_1513.det.natAbs = 1 := by
    have hdet : rowTransform_1513.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1513 hU
  have hcols := hrows.permuteColumns columnPerm_1513
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1513 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1513 = targetTop_1513 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1513 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 4 6)) 9 := by
  have htop : targetTop_1513 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1513

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 4, 7)`. -/
def targetTop_1514 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1514 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1514 :
    TopRowRelation targetTop_1514 relationCoefficients_1514 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1514, relationCoefficients_1514, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1514 : BottomDetBound targetTop_1514 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1514

theorem canonicalBound_1514 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 4 7)) 9 := by
  have htop : targetTop_1514 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1514

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 5, 5)`. -/
def targetTop_1515 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1515 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_1515 :
    TopRowRelation targetTop_1515 relationCoefficients_1515 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1515, relationCoefficients_1515, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1515 : BottomDetBound targetTop_1515 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1515

theorem canonicalBound_1515 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 5 5)) 9 := by
  have htop : targetTop_1515 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1515

/-- Explicit target top block for canonical pattern `(3, 3, 3, 3, 5, 6)`. -/
def targetTop_1516 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1516 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_1516 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1516 : BottomDetBound targetTop_1516 9 := by
  have hU : rowTransform_1516.det.natAbs = 1 := by
    have hdet : rowTransform_1516.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Aggregate.bottomBound.transformTopRows rowTransform_1516 hU
  have hcols := hrows.permuteColumns columnPerm_1516
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1516 MainTheory.Generated.BinaryBetaSixKernel.Representative.R072.Base.explicitTop)
          columnPerm_1516 = targetTop_1516 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1516 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 5 6)) 9 := by
  have htop : targetTop_1516 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1516

/-- Explicit target top block for canonical pattern `(3, 3, 3, 3, 5, 7)`. -/
def targetTop_1517 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1517 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1517 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1517 : BottomDetBound targetTop_1517 9 := by
  have hU : rowTransform_1517.det.natAbs = 1 := by
    have hdet : rowTransform_1517.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1517 hU
  have hcols := hrows.permuteColumns columnPerm_1517
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1517 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1517 = targetTop_1517 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1517 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 5 7)) 9 := by
  have htop : targetTop_1517 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1517

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 3, 6, 6)`. -/
def targetTop_1518 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1518 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_1518 :
    TopRowRelation targetTop_1518 relationCoefficients_1518 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1518, relationCoefficients_1518, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1518 : BottomDetBound targetTop_1518 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1518

theorem canonicalBound_1518 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 6 6)) 9 := by
  have htop : targetTop_1518 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1518

/-- Explicit target top block for canonical pattern `(3, 3, 3, 3, 6, 7)`. -/
def targetTop_1519 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1519 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1519 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1519 : BottomDetBound targetTop_1519 9 := by
  have hU : rowTransform_1519.det.natAbs = 1 := by
    have hdet : rowTransform_1519.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_1519 hU
  have hcols := hrows.permuteColumns columnPerm_1519
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1519 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_1519 = targetTop_1519 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1519 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 6 7)) 9 := by
  have htop : targetTop_1519 =
      topOfPattern (R := ℤ) (angle6 3 3 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1519

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094
