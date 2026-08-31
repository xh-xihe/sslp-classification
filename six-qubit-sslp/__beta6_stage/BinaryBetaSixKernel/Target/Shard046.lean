-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard046

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 4, 4)`. -/
def targetTop_0736 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0736 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0736 :
    TopRowRelation targetTop_0736 relationCoefficients_0736 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0736, relationCoefficients_0736, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0736 : BottomDetBound targetTop_0736 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0736

theorem canonicalBound_0736 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 4 4)) 9 := by
  have htop : targetTop_0736 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0736

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 4, 5)`. -/
def targetTop_0737 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0737 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0737 :
    TopRowRelation targetTop_0737 relationCoefficients_0737 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0737, relationCoefficients_0737, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0737 : BottomDetBound targetTop_0737 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0737

theorem canonicalBound_0737 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 4 5)) 9 := by
  have htop : targetTop_0737 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0737

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 4, 6)`. -/
def targetTop_0738 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0738 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0738 :
    TopRowRelation targetTop_0738 relationCoefficients_0738 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0738, relationCoefficients_0738, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0738 : BottomDetBound targetTop_0738 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0738

theorem canonicalBound_0738 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 4 6)) 9 := by
  have htop : targetTop_0738 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0738

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 4, 7)`. -/
def targetTop_0739 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0739 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0739 :
    TopRowRelation targetTop_0739 relationCoefficients_0739 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0739, relationCoefficients_0739, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0739 : BottomDetBound targetTop_0739 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0739

theorem canonicalBound_0739 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 4 7)) 9 := by
  have htop : targetTop_0739 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0739

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 5, 5)`. -/
def targetTop_0740 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0740 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0740 :
    TopRowRelation targetTop_0740 relationCoefficients_0740 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0740, relationCoefficients_0740, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0740 : BottomDetBound targetTop_0740 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0740

theorem canonicalBound_0740 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 5 5)) 9 := by
  have htop : targetTop_0740 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0740

/-- Explicit target top block for canonical pattern `(0, 4, 4, 4, 5, 6)`. -/
def targetTop_0741 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0741 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0741 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0741 : BottomDetBound targetTop_0741 9 := by
  have hU : rowTransform_0741.det.natAbs = 1 := by
    have hdet : rowTransform_0741.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0741 hU
  have hcols := hrows.permuteColumns columnPerm_0741
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0741 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0741 = targetTop_0741 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0741 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 5 6)) 9 := by
  have htop : targetTop_0741 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0741

/-- Explicit target top block for canonical pattern `(0, 4, 4, 4, 5, 7)`. -/
def targetTop_0742 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0742 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0742 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0742 : BottomDetBound targetTop_0742 9 := by
  have hU : rowTransform_0742.det.natAbs = 1 := by
    have hdet : rowTransform_0742.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0742 hU
  have hcols := hrows.permuteColumns columnPerm_0742
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0742 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0742 = targetTop_0742 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0742 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 5 7)) 9 := by
  have htop : targetTop_0742 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0742

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 6, 6)`. -/
def targetTop_0743 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0743 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0743 :
    TopRowRelation targetTop_0743 relationCoefficients_0743 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0743, relationCoefficients_0743, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0743 : BottomDetBound targetTop_0743 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0743

theorem canonicalBound_0743 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 6 6)) 9 := by
  have htop : targetTop_0743 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0743

/-- Explicit target top block for canonical pattern `(0, 4, 4, 4, 6, 7)`. -/
def targetTop_0744 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0744 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0744 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0744 : BottomDetBound targetTop_0744 9 := by
  have hU : rowTransform_0744.det.natAbs = 1 := by
    have hdet : rowTransform_0744.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0744 hU
  have hcols := hrows.permuteColumns columnPerm_0744
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0744 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0744 = targetTop_0744 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0744 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 6 7)) 9 := by
  have htop : targetTop_0744 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0744

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 4, 7, 7)`. -/
def targetTop_0745 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0745 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0745 :
    TopRowRelation targetTop_0745 relationCoefficients_0745 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0745, relationCoefficients_0745, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0745 : BottomDetBound targetTop_0745 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0745

theorem canonicalBound_0745 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 4 7 7)) 9 := by
  have htop : targetTop_0745 =
      topOfPattern (R := ℤ) (angle6 0 4 4 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0745

/-- Explicit rank-deficient target for canonical pattern `(0, 4, 4, 5, 5, 5)`. -/
def targetTop_0746 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0746 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0746 :
    TopRowRelation targetTop_0746 relationCoefficients_0746 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0746, relationCoefficients_0746, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0746 : BottomDetBound targetTop_0746 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0746

theorem canonicalBound_0746 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 5 5)) 9 := by
  have htop : targetTop_0746 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0746

/-- Explicit target top block for canonical pattern `(0, 4, 4, 5, 5, 6)`. -/
def targetTop_0747 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0747 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0747 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0747 : BottomDetBound targetTop_0747 9 := by
  have hU : rowTransform_0747.det.natAbs = 1 := by
    have hdet : rowTransform_0747.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0747 hU
  have hcols := hrows.permuteColumns columnPerm_0747
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0747 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0747 = targetTop_0747 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0747 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 5 6)) 9 := by
  have htop : targetTop_0747 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0747

/-- Explicit target top block for canonical pattern `(0, 4, 4, 5, 5, 7)`. -/
def targetTop_0748 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0748 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0748 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0748 : BottomDetBound targetTop_0748 9 := by
  have hU : rowTransform_0748.det.natAbs = 1 := by
    have hdet : rowTransform_0748.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0748 hU
  have hcols := hrows.permuteColumns columnPerm_0748
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0748 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0748 = targetTop_0748 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0748 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 5 7)) 9 := by
  have htop : targetTop_0748 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0748

/-- Explicit target top block for canonical pattern `(0, 4, 4, 5, 6, 6)`. -/
def targetTop_0749 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0749 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 1, 1]

def columnPerm_0749 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0749 : BottomDetBound targetTop_0749 9 := by
  have hU : rowTransform_0749.det.natAbs = 1 := by
    have hdet : rowTransform_0749.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0749 hU
  have hcols := hrows.permuteColumns columnPerm_0749
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0749 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0749 = targetTop_0749 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0749 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 6 6)) 9 := by
  have htop : targetTop_0749 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0749

/-- Explicit target top block for canonical pattern `(0, 4, 4, 5, 6, 7)`. -/
def targetTop_0750 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0750 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_0750 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0750 : BottomDetBound targetTop_0750 9 := by
  have hU : rowTransform_0750.det.natAbs = 1 := by
    have hdet : rowTransform_0750.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0750 hU
  have hcols := hrows.permuteColumns columnPerm_0750
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0750 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0750 = targetTop_0750 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0750 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 6 7)) 9 := by
  have htop : targetTop_0750 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0750

/-- Explicit target top block for canonical pattern `(0, 4, 4, 5, 7, 7)`. -/
def targetTop_0751 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0751 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 1, 0;
     1, 1, 1]

def columnPerm_0751 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0751 : BottomDetBound targetTop_0751 9 := by
  have hU : rowTransform_0751.det.natAbs = 1 := by
    have hdet : rowTransform_0751.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0751 hU
  have hcols := hrows.permuteColumns columnPerm_0751
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0751 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0751 = targetTop_0751 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0751 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 4 5 7 7)) 9 := by
  have htop : targetTop_0751 =
      topOfPattern (R := ℤ) (angle6 0 4 4 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0751

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard046
