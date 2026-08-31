-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard047

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 6, 6, 6)`. -/
def targetTop_0752 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0752 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0752 :
    TopRowRelation targetTop_0752 relationCoefficients_0752 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0752, relationCoefficients_0752, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0752 : BottomDetBound targetTop_0752 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0752

theorem canonicalBound_0752 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 6 6 6)) 9 := by
  have htop : targetTop_0752 =
      topOfPattern (R := ℤ) (angle6 0 4 4 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0752

/-- Explicit target top block for canonical pattern `(0, 4, 4, 6, 6, 7)`. -/
def targetTop_0753 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0753 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0753 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0753 : BottomDetBound targetTop_0753 9 := by
  have hU : rowTransform_0753.det.natAbs = 1 := by
    have hdet : rowTransform_0753.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0753 hU
  have hcols := hrows.permuteColumns columnPerm_0753
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0753 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0753 = targetTop_0753 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0753 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 6 6 7)) 9 := by
  have htop : targetTop_0753 =
      topOfPattern (R := ℤ) (angle6 0 4 4 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0753

/-- Explicit target top block for canonical pattern `(0, 4, 4, 6, 7, 7)`. -/
def targetTop_0754 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0754 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0754 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0754 : BottomDetBound targetTop_0754 9 := by
  have hU : rowTransform_0754.det.natAbs = 1 := by
    have hdet : rowTransform_0754.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0754 hU
  have hcols := hrows.permuteColumns columnPerm_0754
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0754 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0754 = targetTop_0754 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0754 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 6 7 7)) 9 := by
  have htop : targetTop_0754 =
      topOfPattern (R := ℤ) (angle6 0 4 4 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0754

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 7, 7, 7)`. -/
def targetTop_0755 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0755 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0755 :
    TopRowRelation targetTop_0755 relationCoefficients_0755 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0755, relationCoefficients_0755, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0755 : BottomDetBound targetTop_0755 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0755

theorem canonicalBound_0755 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 7 7 7)) 9 := by
  have htop : targetTop_0755 =
      topOfPattern (R := ℤ) (angle6 0 4 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0755

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 5, 5, 5, 5)`. -/
def targetTop_0756 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0756 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0756 :
    TopRowRelation targetTop_0756 relationCoefficients_0756 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0756, relationCoefficients_0756, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0756 : BottomDetBound targetTop_0756 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0756

theorem canonicalBound_0756 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 5 5)) 9 := by
  have htop : targetTop_0756 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0756

/-- Explicit target top block for canonical pattern `(0, 4, 5, 5, 5, 6)`. -/
def targetTop_0757 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0757 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0757 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0757 : BottomDetBound targetTop_0757 9 := by
  have hU : rowTransform_0757.det.natAbs = 1 := by
    have hdet : rowTransform_0757.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0757 hU
  have hcols := hrows.permuteColumns columnPerm_0757
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0757 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0757 = targetTop_0757 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0757 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 5 6)) 9 := by
  have htop : targetTop_0757 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0757

/-- Explicit target top block for canonical pattern `(0, 4, 5, 5, 5, 7)`. -/
def targetTop_0758 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0758 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0758 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0758 : BottomDetBound targetTop_0758 9 := by
  have hU : rowTransform_0758.det.natAbs = 1 := by
    have hdet : rowTransform_0758.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0758 hU
  have hcols := hrows.permuteColumns columnPerm_0758
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0758 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0758 = targetTop_0758 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0758 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 5 7)) 9 := by
  have htop : targetTop_0758 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0758

/-- Explicit target top block for canonical pattern `(0, 4, 5, 5, 6, 6)`. -/
def targetTop_0759 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0759 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 1, 1]

def columnPerm_0759 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0759 : BottomDetBound targetTop_0759 9 := by
  have hU : rowTransform_0759.det.natAbs = 1 := by
    have hdet : rowTransform_0759.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0759 hU
  have hcols := hrows.permuteColumns columnPerm_0759
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0759 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0759 = targetTop_0759 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0759 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 6 6)) 9 := by
  have htop : targetTop_0759 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0759

/-- Explicit target top block for canonical pattern `(0, 4, 5, 5, 6, 7)`. -/
def targetTop_0760 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0760 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_0760 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0760 : BottomDetBound targetTop_0760 9 := by
  have hU : rowTransform_0760.det.natAbs = 1 := by
    have hdet : rowTransform_0760.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0760 hU
  have hcols := hrows.permuteColumns columnPerm_0760
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0760 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0760 = targetTop_0760 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0760 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 6 7)) 9 := by
  have htop : targetTop_0760 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0760

/-- Explicit target top block for canonical pattern `(0, 4, 5, 5, 7, 7)`. -/
def targetTop_0761 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0761 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     1, 1, 1]

def columnPerm_0761 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0761 : BottomDetBound targetTop_0761 9 := by
  have hU : rowTransform_0761.det.natAbs = 1 := by
    have hdet : rowTransform_0761.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0761 hU
  have hcols := hrows.permuteColumns columnPerm_0761
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0761 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0761 = targetTop_0761 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0761 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 5 7 7)) 9 := by
  have htop : targetTop_0761 =
      topOfPattern (R := ℤ) (angle6 0 4 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0761

/-- Explicit target top block for canonical pattern `(0, 4, 5, 6, 6, 6)`. -/
def targetTop_0762 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0762 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_0762 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0762 : BottomDetBound targetTop_0762 9 := by
  have hU : rowTransform_0762.det.natAbs = 1 := by
    have hdet : rowTransform_0762.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0762 hU
  have hcols := hrows.permuteColumns columnPerm_0762
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0762 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0762 = targetTop_0762 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0762 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 6 6 6)) 9 := by
  have htop : targetTop_0762 =
      topOfPattern (R := ℤ) (angle6 0 4 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0762

/-- Explicit target top block for canonical pattern `(0, 4, 5, 6, 6, 7)`. -/
def targetTop_0763 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0763 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     1, 1, 0]

def columnPerm_0763 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0763 : BottomDetBound targetTop_0763 9 := by
  have hU : rowTransform_0763.det.natAbs = 1 := by
    have hdet : rowTransform_0763.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0763 hU
  have hcols := hrows.permuteColumns columnPerm_0763
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0763 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0763 = targetTop_0763 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0763 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 6 6 7)) 9 := by
  have htop : targetTop_0763 =
      topOfPattern (R := ℤ) (angle6 0 4 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0763

/-- Explicit target top block for canonical pattern `(0, 4, 5, 6, 7, 7)`. -/
def targetTop_0764 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0764 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 0, 0;
     1, 1, 0]

def columnPerm_0764 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0764 : BottomDetBound targetTop_0764 9 := by
  have hU : rowTransform_0764.det.natAbs = 1 := by
    have hdet : rowTransform_0764.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0764 hU
  have hcols := hrows.permuteColumns columnPerm_0764
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0764 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0764 = targetTop_0764 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0764 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 6 7 7)) 9 := by
  have htop : targetTop_0764 =
      topOfPattern (R := ℤ) (angle6 0 4 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0764

/-- Explicit target top block for canonical pattern `(0, 4, 5, 7, 7, 7)`. -/
def targetTop_0765 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0765 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     1, 1, 1]

def columnPerm_0765 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0765 : BottomDetBound targetTop_0765 9 := by
  have hU : rowTransform_0765.det.natAbs = 1 := by
    have hdet : rowTransform_0765.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0765 hU
  have hcols := hrows.permuteColumns columnPerm_0765
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0765 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0765 = targetTop_0765 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0765 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 5 7 7 7)) 9 := by
  have htop : targetTop_0765 =
      topOfPattern (R := ℤ) (angle6 0 4 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0765

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 6, 6, 6, 6)`. -/
def targetTop_0766 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0766 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0766 :
    TopRowRelation targetTop_0766 relationCoefficients_0766 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0766, relationCoefficients_0766, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0766 : BottomDetBound targetTop_0766 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0766

theorem canonicalBound_0766 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 6 6 6 6)) 9 := by
  have htop : targetTop_0766 =
      topOfPattern (R := ℤ) (angle6 0 4 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0766

/-- Explicit target top block for canonical pattern `(0, 4, 6, 6, 6, 7)`. -/
def targetTop_0767 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0767 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     1, 1, 1]

def columnPerm_0767 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0767 : BottomDetBound targetTop_0767 9 := by
  have hU : rowTransform_0767.det.natAbs = 1 := by
    have hdet : rowTransform_0767.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0767 hU
  have hcols := hrows.permuteColumns columnPerm_0767
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0767 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0767 = targetTop_0767 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0767 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 6 6 6 7)) 9 := by
  have htop : targetTop_0767 =
      topOfPattern (R := ℤ) (angle6 0 4 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0767

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard047
