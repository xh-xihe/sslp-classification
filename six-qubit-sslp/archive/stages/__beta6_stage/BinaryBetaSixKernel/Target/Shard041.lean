-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 5, 5, 7, 7)`. -/
def targetTop_0656 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0656 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0656 :
    TopRowRelation targetTop_0656 relationCoefficients_0656 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0656, relationCoefficients_0656, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0656 : BottomDetBound targetTop_0656 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0656

theorem canonicalBound_0656 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 5 7 7)) 9 := by
  have htop : targetTop_0656 =
      topOfPattern (R := ℤ) (angle6 0 2 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0656

/-- Explicit target top block for canonical pattern `(0, 2, 5, 6, 6, 6)`. -/
def targetTop_0657 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0657 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0657 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0657 : BottomDetBound targetTop_0657 9 := by
  have hU : rowTransform_0657.det.natAbs = 1 := by
    have hdet : rowTransform_0657.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0657 hU
  have hcols := hrows.permuteColumns columnPerm_0657
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0657 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0657 = targetTop_0657 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0657 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 6 6 6)) 9 := by
  have htop : targetTop_0657 =
      topOfPattern (R := ℤ) (angle6 0 2 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0657

/-- Explicit target top block for canonical pattern `(0, 2, 5, 6, 6, 7)`. -/
def targetTop_0658 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0658 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0658 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0658 : BottomDetBound targetTop_0658 9 := by
  have hU : rowTransform_0658.det.natAbs = 1 := by
    have hdet : rowTransform_0658.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0658 hU
  have hcols := hrows.permuteColumns columnPerm_0658
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0658 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0658 = targetTop_0658 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0658 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 6 6 7)) 9 := by
  have htop : targetTop_0658 =
      topOfPattern (R := ℤ) (angle6 0 2 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0658

/-- Explicit target top block for canonical pattern `(0, 2, 5, 6, 7, 7)`. -/
def targetTop_0659 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0659 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0659 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0659 : BottomDetBound targetTop_0659 9 := by
  have hU : rowTransform_0659.det.natAbs = 1 := by
    have hdet : rowTransform_0659.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0659 hU
  have hcols := hrows.permuteColumns columnPerm_0659
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0659 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0659 = targetTop_0659 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0659 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 6 7 7)) 9 := by
  have htop : targetTop_0659 =
      topOfPattern (R := ℤ) (angle6 0 2 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0659

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 5, 7, 7, 7)`. -/
def targetTop_0660 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0660 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0660 :
    TopRowRelation targetTop_0660 relationCoefficients_0660 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0660, relationCoefficients_0660, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0660 : BottomDetBound targetTop_0660 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0660

theorem canonicalBound_0660 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 7 7 7)) 9 := by
  have htop : targetTop_0660 =
      topOfPattern (R := ℤ) (angle6 0 2 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0660

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 6, 6, 6, 6)`. -/
def targetTop_0661 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0661 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0661 :
    TopRowRelation targetTop_0661 relationCoefficients_0661 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0661, relationCoefficients_0661, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0661 : BottomDetBound targetTop_0661 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0661

theorem canonicalBound_0661 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 6 6 6 6)) 9 := by
  have htop : targetTop_0661 =
      topOfPattern (R := ℤ) (angle6 0 2 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0661

/-- Explicit target top block for canonical pattern `(0, 2, 6, 6, 6, 7)`. -/
def targetTop_0662 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0662 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0662 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0662 : BottomDetBound targetTop_0662 9 := by
  have hU : rowTransform_0662.det.natAbs = 1 := by
    have hdet : rowTransform_0662.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0662 hU
  have hcols := hrows.permuteColumns columnPerm_0662
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0662 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0662 = targetTop_0662 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0662 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 6 6 6 7)) 9 := by
  have htop : targetTop_0662 =
      topOfPattern (R := ℤ) (angle6 0 2 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0662

/-- Explicit target top block for canonical pattern `(0, 2, 6, 6, 7, 7)`. -/
def targetTop_0663 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0663 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     1, 1, 0]

def columnPerm_0663 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0663 : BottomDetBound targetTop_0663 9 := by
  have hU : rowTransform_0663.det.natAbs = 1 := by
    have hdet : rowTransform_0663.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0663 hU
  have hcols := hrows.permuteColumns columnPerm_0663
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0663 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0663 = targetTop_0663 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0663 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 6 6 7 7)) 9 := by
  have htop : targetTop_0663 =
      topOfPattern (R := ℤ) (angle6 0 2 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0663

/-- Explicit target top block for canonical pattern `(0, 2, 6, 7, 7, 7)`. -/
def targetTop_0664 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0664 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0664 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0664 : BottomDetBound targetTop_0664 9 := by
  have hU : rowTransform_0664.det.natAbs = 1 := by
    have hdet : rowTransform_0664.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0664 hU
  have hcols := hrows.permuteColumns columnPerm_0664
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0664 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0664 = targetTop_0664 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0664 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 6 7 7 7)) 9 := by
  have htop : targetTop_0664 =
      topOfPattern (R := ℤ) (angle6 0 2 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0664

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 7, 7, 7, 7)`. -/
def targetTop_0665 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0665 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0665 :
    TopRowRelation targetTop_0665 relationCoefficients_0665 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0665, relationCoefficients_0665, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0665 : BottomDetBound targetTop_0665 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0665

theorem canonicalBound_0665 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 7 7 7 7)) 9 := by
  have htop : targetTop_0665 =
      topOfPattern (R := ℤ) (angle6 0 2 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0665

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 3, 3)`. -/
def targetTop_0666 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0666 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0666 :
    TopRowRelation targetTop_0666 relationCoefficients_0666 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0666, relationCoefficients_0666, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0666 : BottomDetBound targetTop_0666 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0666

theorem canonicalBound_0666 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 3)) 9 := by
  have htop : targetTop_0666 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0666

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 3, 4)`. -/
def targetTop_0667 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0667 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0667 :
    TopRowRelation targetTop_0667 relationCoefficients_0667 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0667, relationCoefficients_0667, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0667 : BottomDetBound targetTop_0667 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0667

theorem canonicalBound_0667 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 4)) 9 := by
  have htop : targetTop_0667 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0667

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 3, 5)`. -/
def targetTop_0668 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0668 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0668 :
    TopRowRelation targetTop_0668 relationCoefficients_0668 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0668, relationCoefficients_0668, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0668 : BottomDetBound targetTop_0668 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0668

theorem canonicalBound_0668 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 5)) 9 := by
  have htop : targetTop_0668 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0668

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 3, 6)`. -/
def targetTop_0669 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0669 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0669 :
    TopRowRelation targetTop_0669 relationCoefficients_0669 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0669, relationCoefficients_0669, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0669 : BottomDetBound targetTop_0669 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0669

theorem canonicalBound_0669 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 6)) 9 := by
  have htop : targetTop_0669 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0669

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 3, 7)`. -/
def targetTop_0670 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0670 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0670 :
    TopRowRelation targetTop_0670 relationCoefficients_0670 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0670, relationCoefficients_0670, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0670 : BottomDetBound targetTop_0670 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0670

theorem canonicalBound_0670 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 7)) 9 := by
  have htop : targetTop_0670 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0670

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 4, 4)`. -/
def targetTop_0671 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0671 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0671 :
    TopRowRelation targetTop_0671 relationCoefficients_0671 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0671, relationCoefficients_0671, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0671 : BottomDetBound targetTop_0671 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0671

theorem canonicalBound_0671 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 4 4)) 9 := by
  have htop : targetTop_0671 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0671

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041
