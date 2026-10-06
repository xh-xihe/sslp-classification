-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 3, 3, 3, 4, 5)`. -/
def targetTop_0672 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0672 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0672 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0672 : BottomDetBound targetTop_0672 9 := by
  have hU : rowTransform_0672.det.natAbs = 1 := by
    have hdet : rowTransform_0672.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0672 hU
  have hcols := hrows.permuteColumns columnPerm_0672
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0672 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0672 = targetTop_0672 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0672 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 4 5)) 9 := by
  have htop : targetTop_0672 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0672

/-- Explicit target top block for canonical pattern `(0, 3, 3, 3, 4, 6)`. -/
def targetTop_0673 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0673 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0673 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0673 : BottomDetBound targetTop_0673 9 := by
  have hU : rowTransform_0673.det.natAbs = 1 := by
    have hdet : rowTransform_0673.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0673 hU
  have hcols := hrows.permuteColumns columnPerm_0673
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0673 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0673 = targetTop_0673 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0673 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 4 6)) 9 := by
  have htop : targetTop_0673 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0673

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 4, 7)`. -/
def targetTop_0674 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0674 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0674 :
    TopRowRelation targetTop_0674 relationCoefficients_0674 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0674, relationCoefficients_0674, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0674 : BottomDetBound targetTop_0674 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0674

theorem canonicalBound_0674 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 4 7)) 9 := by
  have htop : targetTop_0674 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0674

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 5, 5)`. -/
def targetTop_0675 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0675 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0675 :
    TopRowRelation targetTop_0675 relationCoefficients_0675 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0675, relationCoefficients_0675, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0675 : BottomDetBound targetTop_0675 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0675

theorem canonicalBound_0675 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 5 5)) 9 := by
  have htop : targetTop_0675 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0675

/-- Explicit target top block for canonical pattern `(0, 3, 3, 3, 5, 6)`. -/
def targetTop_0676 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0676 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0676 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0676 : BottomDetBound targetTop_0676 9 := by
  have hU : rowTransform_0676.det.natAbs = 1 := by
    have hdet : rowTransform_0676.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Aggregate.bottomBound.transformTopRows rowTransform_0676 hU
  have hcols := hrows.permuteColumns columnPerm_0676
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0676 MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Base.explicitTop)
          columnPerm_0676 = targetTop_0676 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0676 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 5 6)) 9 := by
  have htop : targetTop_0676 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0676

/-- Explicit target top block for canonical pattern `(0, 3, 3, 3, 5, 7)`. -/
def targetTop_0677 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0677 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0677 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0677 : BottomDetBound targetTop_0677 9 := by
  have hU : rowTransform_0677.det.natAbs = 1 := by
    have hdet : rowTransform_0677.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0677 hU
  have hcols := hrows.permuteColumns columnPerm_0677
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0677 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0677 = targetTop_0677 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0677 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 5 7)) 9 := by
  have htop : targetTop_0677 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0677

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 6, 6)`. -/
def targetTop_0678 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0678 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0678 :
    TopRowRelation targetTop_0678 relationCoefficients_0678 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0678, relationCoefficients_0678, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0678 : BottomDetBound targetTop_0678 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0678

theorem canonicalBound_0678 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 6 6)) 9 := by
  have htop : targetTop_0678 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0678

/-- Explicit target top block for canonical pattern `(0, 3, 3, 3, 6, 7)`. -/
def targetTop_0679 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0679 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0679 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0679 : BottomDetBound targetTop_0679 9 := by
  have hU : rowTransform_0679.det.natAbs = 1 := by
    have hdet : rowTransform_0679.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0679 hU
  have hcols := hrows.permuteColumns columnPerm_0679
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0679 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0679 = targetTop_0679 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0679 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 6 7)) 9 := by
  have htop : targetTop_0679 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0679

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 3, 7, 7)`. -/
def targetTop_0680 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0680 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0680 :
    TopRowRelation targetTop_0680 relationCoefficients_0680 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0680, relationCoefficients_0680, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0680 : BottomDetBound targetTop_0680 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0680

theorem canonicalBound_0680 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 7 7)) 9 := by
  have htop : targetTop_0680 =
      topOfPattern (R := ℤ) (angle6 0 3 3 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0680

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 4, 4, 4)`. -/
def targetTop_0681 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0681 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0681 :
    TopRowRelation targetTop_0681 relationCoefficients_0681 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0681, relationCoefficients_0681, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0681 : BottomDetBound targetTop_0681 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0681

theorem canonicalBound_0681 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 4 4)) 9 := by
  have htop : targetTop_0681 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0681

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 4, 5)`. -/
def targetTop_0682 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0682 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0682 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0682 : BottomDetBound targetTop_0682 9 := by
  have hU : rowTransform_0682.det.natAbs = 1 := by
    have hdet : rowTransform_0682.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0682 hU
  have hcols := hrows.permuteColumns columnPerm_0682
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0682 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0682 = targetTop_0682 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0682 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 4 5)) 9 := by
  have htop : targetTop_0682 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0682

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 4, 6)`. -/
def targetTop_0683 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0683 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0683 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0683 : BottomDetBound targetTop_0683 9 := by
  have hU : rowTransform_0683.det.natAbs = 1 := by
    have hdet : rowTransform_0683.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0683 hU
  have hcols := hrows.permuteColumns columnPerm_0683
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0683 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0683 = targetTop_0683 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0683 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 4 6)) 9 := by
  have htop : targetTop_0683 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0683

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 3, 4, 4, 7)`. -/
def targetTop_0684 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0684 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0684 :
    TopRowRelation targetTop_0684 relationCoefficients_0684 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0684, relationCoefficients_0684, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0684 : BottomDetBound targetTop_0684 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0684

theorem canonicalBound_0684 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 4 7)) 9 := by
  have htop : targetTop_0684 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0684

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 5, 5)`. -/
def targetTop_0685 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0685 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0685 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0685 : BottomDetBound targetTop_0685 9 := by
  have hU : rowTransform_0685.det.natAbs = 1 := by
    have hdet : rowTransform_0685.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0685 hU
  have hcols := hrows.permuteColumns columnPerm_0685
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0685 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0685 = targetTop_0685 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0685 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 5 5)) 9 := by
  have htop : targetTop_0685 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0685

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 5, 6)`. -/
def targetTop_0686 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0686 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0686 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0686 : BottomDetBound targetTop_0686 9 := by
  have hU : rowTransform_0686.det.natAbs = 1 := by
    have hdet : rowTransform_0686.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Aggregate.bottomBound.transformTopRows rowTransform_0686 hU
  have hcols := hrows.permuteColumns columnPerm_0686
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0686 MainTheory.Generated.BinaryBetaSixKernel.Representative.R023.Base.explicitTop)
          columnPerm_0686 = targetTop_0686 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0686 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 5 6)) 9 := by
  have htop : targetTop_0686 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0686

/-- Explicit target top block for canonical pattern `(0, 3, 3, 4, 5, 7)`. -/
def targetTop_0687 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0687 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0687 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0687 : BottomDetBound targetTop_0687 9 := by
  have hU : rowTransform_0687.det.natAbs = 1 := by
    have hdet : rowTransform_0687.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0687 hU
  have hcols := hrows.permuteColumns columnPerm_0687
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0687 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0687 = targetTop_0687 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0687 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 4 5 7)) 9 := by
  have htop : targetTop_0687 =
      topOfPattern (R := ℤ) (angle6 0 3 3 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0687

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042
