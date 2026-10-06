-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(3, 3, 3, 5, 7, 7)`. -/
def targetTop_1536 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1536 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     0, 1, 1]

def columnPerm_1536 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1536 : BottomDetBound targetTop_1536 9 := by
  have hU : rowTransform_1536.det.natAbs = 1 := by
    have hdet : rowTransform_1536.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1536 hU
  have hcols := hrows.permuteColumns columnPerm_1536
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1536 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1536 = targetTop_1536 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1536 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 5 7 7)) 9 := by
  have htop : targetTop_1536 =
      topOfPattern (R := ℤ) (angle6 3 3 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1536

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 6, 6, 6)`. -/
def targetTop_1537 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1537 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_1537 :
    TopRowRelation targetTop_1537 relationCoefficients_1537 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1537, relationCoefficients_1537, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1537 : BottomDetBound targetTop_1537 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1537

theorem canonicalBound_1537 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 6 6 6)) 9 := by
  have htop : targetTop_1537 =
      topOfPattern (R := ℤ) (angle6 3 3 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1537

/-- Explicit target top block for canonical pattern `(3, 3, 3, 6, 6, 7)`. -/
def targetTop_1538 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1538 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1538 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1538 : BottomDetBound targetTop_1538 9 := by
  have hU : rowTransform_1538.det.natAbs = 1 := by
    have hdet : rowTransform_1538.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1538 hU
  have hcols := hrows.permuteColumns columnPerm_1538
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1538 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1538 = targetTop_1538 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1538 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 6 6 7)) 9 := by
  have htop : targetTop_1538 =
      topOfPattern (R := ℤ) (angle6 3 3 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1538

/-- Explicit target top block for canonical pattern `(3, 3, 3, 6, 7, 7)`. -/
def targetTop_1539 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1539 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     0, 1, 1]

def columnPerm_1539 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1539 : BottomDetBound targetTop_1539 9 := by
  have hU : rowTransform_1539.det.natAbs = 1 := by
    have hdet : rowTransform_1539.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1539 hU
  have hcols := hrows.permuteColumns columnPerm_1539
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1539 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1539 = targetTop_1539 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1539 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 6 7 7)) 9 := by
  have htop : targetTop_1539 =
      topOfPattern (R := ℤ) (angle6 3 3 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1539

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 3, 7, 7, 7)`. -/
def targetTop_1540 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1540 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1540 :
    TopRowRelation targetTop_1540 relationCoefficients_1540 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1540, relationCoefficients_1540, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1540 : BottomDetBound targetTop_1540 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1540

theorem canonicalBound_1540 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 7 7 7)) 9 := by
  have htop : targetTop_1540 =
      topOfPattern (R := ℤ) (angle6 3 3 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1540

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 4, 4, 4, 4)`. -/
def targetTop_1541 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1541 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1541 :
    TopRowRelation targetTop_1541 relationCoefficients_1541 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1541, relationCoefficients_1541, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1541 : BottomDetBound targetTop_1541 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1541

theorem canonicalBound_1541 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 4 4)) 9 := by
  have htop : targetTop_1541 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1541

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 4, 5)`. -/
def targetTop_1542 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1542 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1542 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1542 : BottomDetBound targetTop_1542 9 := by
  have hU : rowTransform_1542.det.natAbs = 1 := by
    have hdet : rowTransform_1542.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1542 hU
  have hcols := hrows.permuteColumns columnPerm_1542
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1542 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1542 = targetTop_1542 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1542 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 4 5)) 9 := by
  have htop : targetTop_1542 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1542

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 4, 6)`. -/
def targetTop_1543 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1543 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_1543 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1543 : BottomDetBound targetTop_1543 9 := by
  have hU : rowTransform_1543.det.natAbs = 1 := by
    have hdet : rowTransform_1543.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1543 hU
  have hcols := hrows.permuteColumns columnPerm_1543
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1543 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1543 = targetTop_1543 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1543 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 4 6)) 9 := by
  have htop : targetTop_1543 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1543

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 4, 4, 4, 7)`. -/
def targetTop_1544 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1544 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1544 :
    TopRowRelation targetTop_1544 relationCoefficients_1544 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1544, relationCoefficients_1544, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1544 : BottomDetBound targetTop_1544 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1544

theorem canonicalBound_1544 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 4 7)) 9 := by
  have htop : targetTop_1544 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1544

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 5, 5)`. -/
def targetTop_1545 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1545 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1545 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1545 : BottomDetBound targetTop_1545 9 := by
  have hU : rowTransform_1545.det.natAbs = 1 := by
    have hdet : rowTransform_1545.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1545 hU
  have hcols := hrows.permuteColumns columnPerm_1545
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1545 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1545 = targetTop_1545 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1545 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 5 5)) 9 := by
  have htop : targetTop_1545 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1545

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 5, 6)`. -/
def targetTop_1546 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 0;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1546 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_1546 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1546 : BottomDetBound targetTop_1546 9 := by
  have hU : rowTransform_1546.det.natAbs = 1 := by
    have hdet : rowTransform_1546.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Aggregate.bottomBound.transformTopRows rowTransform_1546 hU
  have hcols := hrows.permuteColumns columnPerm_1546
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1546 MainTheory.Generated.BinaryBetaSixKernel.Representative.R052.Base.explicitTop)
          columnPerm_1546 = targetTop_1546 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1546 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 5 6)) 9 := by
  have htop : targetTop_1546 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1546

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 5, 7)`. -/
def targetTop_1547 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1547 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_1547 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1547 : BottomDetBound targetTop_1547 9 := by
  have hU : rowTransform_1547.det.natAbs = 1 := by
    have hdet : rowTransform_1547.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1547 hU
  have hcols := hrows.permuteColumns columnPerm_1547
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1547 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1547 = targetTop_1547 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1547 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 5 7)) 9 := by
  have htop : targetTop_1547 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1547

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 6, 6)`. -/
def targetTop_1548 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1548 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1548 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1548 : BottomDetBound targetTop_1548 9 := by
  have hU : rowTransform_1548.det.natAbs = 1 := by
    have hdet : rowTransform_1548.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Aggregate.bottomBound.transformTopRows rowTransform_1548 hU
  have hcols := hrows.permuteColumns columnPerm_1548
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1548 MainTheory.Generated.BinaryBetaSixKernel.Representative.R037.Base.explicitTop)
          columnPerm_1548 = targetTop_1548 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1548 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 6 6)) 9 := by
  have htop : targetTop_1548 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1548

/-- Explicit target top block for canonical pattern `(3, 3, 4, 4, 6, 7)`. -/
def targetTop_1549 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1549 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_1549 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1549 : BottomDetBound targetTop_1549 9 := by
  have hU : rowTransform_1549.det.natAbs = 1 := by
    have hdet : rowTransform_1549.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Aggregate.bottomBound.transformTopRows rowTransform_1549 hU
  have hcols := hrows.permuteColumns columnPerm_1549
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1549 MainTheory.Generated.BinaryBetaSixKernel.Representative.R036.Base.explicitTop)
          columnPerm_1549 = targetTop_1549 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1549 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 6 7)) 9 := by
  have htop : targetTop_1549 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1549

/-- Explicit rank-deficient target for canonical pattern `(3, 3, 4, 4, 7, 7)`. -/
def targetTop_1550 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 1, 1;
     1, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_1550 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_1550 :
    TopRowRelation targetTop_1550 relationCoefficients_1550 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_1550, relationCoefficients_1550, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_1550 : BottomDetBound targetTop_1550 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_1550

theorem canonicalBound_1550 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 7 7)) 9 := by
  have htop : targetTop_1550 =
      topOfPattern (R := ℤ) (angle6 3 3 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1550

/-- Explicit target top block for canonical pattern `(3, 3, 4, 5, 5, 5)`. -/
def targetTop_1551 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_1551 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_1551 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_1551 : BottomDetBound targetTop_1551 9 := by
  have hU : rowTransform_1551.det.natAbs = 1 := by
    have hdet : rowTransform_1551.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_1551 hU
  have hcols := hrows.permuteColumns columnPerm_1551
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_1551 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_1551 = targetTop_1551 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_1551 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 5 5)) 9 := by
  have htop : targetTop_1551 =
      topOfPattern (R := ℤ) (angle6 3 3 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_1551

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096
