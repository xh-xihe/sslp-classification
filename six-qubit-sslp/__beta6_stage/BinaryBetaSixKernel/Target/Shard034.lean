-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 6)`. -/
def targetTop_0544 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0544 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0544 :
    TopRowRelation targetTop_0544 relationCoefficients_0544 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0544, relationCoefficients_0544, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0544 : BottomDetBound targetTop_0544 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0544

theorem canonicalBound_0544 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 6)) 9 := by
  have htop : targetTop_0544 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0544

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 2, 7)`. -/
def targetTop_0545 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0545 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0545 :
    TopRowRelation targetTop_0545 relationCoefficients_0545 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0545, relationCoefficients_0545, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0545 : BottomDetBound targetTop_0545 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0545

theorem canonicalBound_0545 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 7)) 9 := by
  have htop : targetTop_0545 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0545

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 3, 3)`. -/
def targetTop_0546 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0546 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0546 :
    TopRowRelation targetTop_0546 relationCoefficients_0546 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0546, relationCoefficients_0546, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0546 : BottomDetBound targetTop_0546 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0546

theorem canonicalBound_0546 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 3)) 9 := by
  have htop : targetTop_0546 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0546

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 3, 4)`. -/
def targetTop_0547 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0547 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0547 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0547 : BottomDetBound targetTop_0547 9 := by
  have hU : rowTransform_0547.det.natAbs = 1 := by
    have hdet : rowTransform_0547.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0547 hU
  have hcols := hrows.permuteColumns columnPerm_0547
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0547 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0547 = targetTop_0547 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0547 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 4)) 9 := by
  have htop : targetTop_0547 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0547

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 3, 5)`. -/
def targetTop_0548 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0548 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0548 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0548 : BottomDetBound targetTop_0548 9 := by
  have hU : rowTransform_0548.det.natAbs = 1 := by
    have hdet : rowTransform_0548.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0548 hU
  have hcols := hrows.permuteColumns columnPerm_0548
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0548 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0548 = targetTop_0548 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0548 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 5)) 9 := by
  have htop : targetTop_0548 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0548

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 3, 6)`. -/
def targetTop_0549 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0549 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0549 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0549 : BottomDetBound targetTop_0549 9 := by
  have hU : rowTransform_0549.det.natAbs = 1 := by
    have hdet : rowTransform_0549.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0549 hU
  have hcols := hrows.permuteColumns columnPerm_0549
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0549 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0549 = targetTop_0549 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0549 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 6)) 9 := by
  have htop : targetTop_0549 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0549

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 3, 7)`. -/
def targetTop_0550 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0550 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0550 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0550 : BottomDetBound targetTop_0550 9 := by
  have hU : rowTransform_0550.det.natAbs = 1 := by
    have hdet : rowTransform_0550.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0550 hU
  have hcols := hrows.permuteColumns columnPerm_0550
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0550 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0550 = targetTop_0550 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0550 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 7)) 9 := by
  have htop : targetTop_0550 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0550

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 4, 4)`. -/
def targetTop_0551 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0551 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0551 :
    TopRowRelation targetTop_0551 relationCoefficients_0551 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0551, relationCoefficients_0551, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0551 : BottomDetBound targetTop_0551 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0551

theorem canonicalBound_0551 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 4 4)) 9 := by
  have htop : targetTop_0551 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0551

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 4, 5)`. -/
def targetTop_0552 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0552 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0552 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0552 : BottomDetBound targetTop_0552 9 := by
  have hU : rowTransform_0552.det.natAbs = 1 := by
    have hdet : rowTransform_0552.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0552 hU
  have hcols := hrows.permuteColumns columnPerm_0552
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0552 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0552 = targetTop_0552 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0552 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 4 5)) 9 := by
  have htop : targetTop_0552 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0552

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 4, 6)`. -/
def targetTop_0553 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0553 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0553 :
    TopRowRelation targetTop_0553 relationCoefficients_0553 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0553, relationCoefficients_0553, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0553 : BottomDetBound targetTop_0553 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0553

theorem canonicalBound_0553 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 4 6)) 9 := by
  have htop : targetTop_0553 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0553

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 4, 7)`. -/
def targetTop_0554 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0554 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0554 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0554 : BottomDetBound targetTop_0554 9 := by
  have hU : rowTransform_0554.det.natAbs = 1 := by
    have hdet : rowTransform_0554.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0554 hU
  have hcols := hrows.permuteColumns columnPerm_0554
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0554 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0554 = targetTop_0554 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0554 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 4 7)) 9 := by
  have htop : targetTop_0554 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0554

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 5, 5)`. -/
def targetTop_0555 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0555 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0555 :
    TopRowRelation targetTop_0555 relationCoefficients_0555 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0555, relationCoefficients_0555, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0555 : BottomDetBound targetTop_0555 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0555

theorem canonicalBound_0555 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 5 5)) 9 := by
  have htop : targetTop_0555 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0555

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 5, 6)`. -/
def targetTop_0556 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0556 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0556 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0556 : BottomDetBound targetTop_0556 9 := by
  have hU : rowTransform_0556.det.natAbs = 1 := by
    have hdet : rowTransform_0556.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0556 hU
  have hcols := hrows.permuteColumns columnPerm_0556
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0556 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0556 = targetTop_0556 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0556 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 5 6)) 9 := by
  have htop : targetTop_0556 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0556

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 5, 7)`. -/
def targetTop_0557 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0557 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0557 :
    TopRowRelation targetTop_0557 relationCoefficients_0557 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0557, relationCoefficients_0557, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0557 : BottomDetBound targetTop_0557 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0557

theorem canonicalBound_0557 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 5 7)) 9 := by
  have htop : targetTop_0557 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0557

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 2, 2, 6, 6)`. -/
def targetTop_0558 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0558 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0558 :
    TopRowRelation targetTop_0558 relationCoefficients_0558 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0558, relationCoefficients_0558, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0558 : BottomDetBound targetTop_0558 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0558

theorem canonicalBound_0558 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 6 6)) 9 := by
  have htop : targetTop_0558 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0558

/-- Explicit target top block for canonical pattern `(0, 2, 2, 2, 6, 7)`. -/
def targetTop_0559 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0559 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0559 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0559 : BottomDetBound targetTop_0559 9 := by
  have hU : rowTransform_0559.det.natAbs = 1 := by
    have hdet : rowTransform_0559.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0559 hU
  have hcols := hrows.permuteColumns columnPerm_0559
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0559 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0559 = targetTop_0559 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0559 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 6 7)) 9 := by
  have htop : targetTop_0559 =
      topOfPattern (R := ℤ) (angle6 0 2 2 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0559

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034
