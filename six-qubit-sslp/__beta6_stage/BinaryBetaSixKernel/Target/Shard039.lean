-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 6, 6)`. -/
def targetTop_0624 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0624 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0624 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0624 : BottomDetBound targetTop_0624 9 := by
  have hU : rowTransform_0624.det.natAbs = 1 := by
    have hdet : rowTransform_0624.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Aggregate.bottomBound.transformTopRows rowTransform_0624 hU
  have hcols := hrows.permuteColumns columnPerm_0624
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0624 MainTheory.Generated.BinaryBetaSixKernel.Representative.R022.Base.explicitTop)
          columnPerm_0624 = targetTop_0624 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0624 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 6 6)) 9 := by
  have htop : targetTop_0624 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0624

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 6, 7)`. -/
def targetTop_0625 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0625 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0625 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0625 : BottomDetBound targetTop_0625 9 := by
  have hU : rowTransform_0625.det.natAbs = 1 := by
    have hdet : rowTransform_0625.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Aggregate.bottomBound.transformTopRows rowTransform_0625 hU
  have hcols := hrows.permuteColumns columnPerm_0625
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0625 MainTheory.Generated.BinaryBetaSixKernel.Representative.R024.Base.explicitTop)
          columnPerm_0625 = targetTop_0625 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0625 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 6 7)) 9 := by
  have htop : targetTop_0625 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0625

/-- Explicit target top block for canonical pattern `(0, 2, 3, 5, 7, 7)`. -/
def targetTop_0626 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0626 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0626 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0626 : BottomDetBound targetTop_0626 9 := by
  have hU : rowTransform_0626.det.natAbs = 1 := by
    have hdet : rowTransform_0626.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Aggregate.bottomBound.transformTopRows rowTransform_0626 hU
  have hcols := hrows.permuteColumns columnPerm_0626
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0626 MainTheory.Generated.BinaryBetaSixKernel.Representative.R016.Base.explicitTop)
          columnPerm_0626 = targetTop_0626 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0626 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 5 7 7)) 9 := by
  have htop : targetTop_0626 =
      topOfPattern (R := ℤ) (angle6 0 2 3 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0626

/-- Explicit target top block for canonical pattern `(0, 2, 3, 6, 6, 6)`. -/
def targetTop_0627 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0627 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_0627 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0627 : BottomDetBound targetTop_0627 9 := by
  have hU : rowTransform_0627.det.natAbs = 1 := by
    have hdet : rowTransform_0627.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0627 hU
  have hcols := hrows.permuteColumns columnPerm_0627
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0627 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0627 = targetTop_0627 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0627 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 6 6 6)) 9 := by
  have htop : targetTop_0627 =
      topOfPattern (R := ℤ) (angle6 0 2 3 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0627

/-- Explicit target top block for canonical pattern `(0, 2, 3, 6, 6, 7)`. -/
def targetTop_0628 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0628 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 0]

def columnPerm_0628 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0628 : BottomDetBound targetTop_0628 9 := by
  have hU : rowTransform_0628.det.natAbs = 1 := by
    have hdet : rowTransform_0628.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0628 hU
  have hcols := hrows.permuteColumns columnPerm_0628
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0628 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0628 = targetTop_0628 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0628 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 6 6 7)) 9 := by
  have htop : targetTop_0628 =
      topOfPattern (R := ℤ) (angle6 0 2 3 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0628

/-- Explicit target top block for canonical pattern `(0, 2, 3, 6, 7, 7)`. -/
def targetTop_0629 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0629 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     1, 1, 0;
     1, 0, 0]

def columnPerm_0629 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0629 : BottomDetBound targetTop_0629 9 := by
  have hU : rowTransform_0629.det.natAbs = 1 := by
    have hdet : rowTransform_0629.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0629 hU
  have hcols := hrows.permuteColumns columnPerm_0629
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0629 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0629 = targetTop_0629 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0629 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 6 7 7)) 9 := by
  have htop : targetTop_0629 =
      topOfPattern (R := ℤ) (angle6 0 2 3 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0629

/-- Explicit target top block for canonical pattern `(0, 2, 3, 7, 7, 7)`. -/
def targetTop_0630 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0630 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_0630 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0630 : BottomDetBound targetTop_0630 9 := by
  have hU : rowTransform_0630.det.natAbs = 1 := by
    have hdet : rowTransform_0630.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0630 hU
  have hcols := hrows.permuteColumns columnPerm_0630
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0630 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0630 = targetTop_0630 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0630 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 3 7 7 7)) 9 := by
  have htop : targetTop_0630 =
      topOfPattern (R := ℤ) (angle6 0 2 3 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0630

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 4, 4, 4, 4)`. -/
def targetTop_0631 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0631 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0631 :
    TopRowRelation targetTop_0631 relationCoefficients_0631 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0631, relationCoefficients_0631, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0631 : BottomDetBound targetTop_0631 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0631

theorem canonicalBound_0631 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 4 4)) 9 := by
  have htop : targetTop_0631 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0631

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 4, 5)`. -/
def targetTop_0632 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0632 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0632 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0632 : BottomDetBound targetTop_0632 9 := by
  have hU : rowTransform_0632.det.natAbs = 1 := by
    have hdet : rowTransform_0632.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0632 hU
  have hcols := hrows.permuteColumns columnPerm_0632
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0632 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0632 = targetTop_0632 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0632 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 4 5)) 9 := by
  have htop : targetTop_0632 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0632

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 4, 4, 4, 6)`. -/
def targetTop_0633 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0633 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0633 :
    TopRowRelation targetTop_0633 relationCoefficients_0633 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0633, relationCoefficients_0633, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0633 : BottomDetBound targetTop_0633 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0633

theorem canonicalBound_0633 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 4 6)) 9 := by
  have htop : targetTop_0633 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0633

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 4, 7)`. -/
def targetTop_0634 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0634 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0634 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0634 : BottomDetBound targetTop_0634 9 := by
  have hU : rowTransform_0634.det.natAbs = 1 := by
    have hdet : rowTransform_0634.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0634 hU
  have hcols := hrows.permuteColumns columnPerm_0634
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0634 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0634 = targetTop_0634 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0634 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 4 7)) 9 := by
  have htop : targetTop_0634 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0634

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 5, 5)`. -/
def targetTop_0635 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0635 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 0]

def columnPerm_0635 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0635 : BottomDetBound targetTop_0635 9 := by
  have hU : rowTransform_0635.det.natAbs = 1 := by
    have hdet : rowTransform_0635.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0635 hU
  have hcols := hrows.permuteColumns columnPerm_0635
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0635 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0635 = targetTop_0635 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0635 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 5 5)) 9 := by
  have htop : targetTop_0635 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0635

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 5, 6)`. -/
def targetTop_0636 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0636 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0636 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0636 : BottomDetBound targetTop_0636 9 := by
  have hU : rowTransform_0636.det.natAbs = 1 := by
    have hdet : rowTransform_0636.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0636 hU
  have hcols := hrows.permuteColumns columnPerm_0636
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0636 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0636 = targetTop_0636 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0636 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 5 6)) 9 := by
  have htop : targetTop_0636 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0636

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 5, 7)`. -/
def targetTop_0637 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0637 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0637 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0637 : BottomDetBound targetTop_0637 9 := by
  have hU : rowTransform_0637.det.natAbs = 1 := by
    have hdet : rowTransform_0637.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0637 hU
  have hcols := hrows.permuteColumns columnPerm_0637
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0637 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0637 = targetTop_0637 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0637 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 5 7)) 9 := by
  have htop : targetTop_0637 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0637

/-- Explicit rank-deficient target for canonical pattern `(0, 2, 4, 4, 6, 6)`. -/
def targetTop_0638 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0638 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0638 :
    TopRowRelation targetTop_0638 relationCoefficients_0638 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0638, relationCoefficients_0638, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0638 : BottomDetBound targetTop_0638 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0638

theorem canonicalBound_0638 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 6 6)) 9 := by
  have htop : targetTop_0638 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0638

/-- Explicit target top block for canonical pattern `(0, 2, 4, 4, 6, 7)`. -/
def targetTop_0639 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0639 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0639 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0639 : BottomDetBound targetTop_0639 9 := by
  have hU : rowTransform_0639.det.natAbs = 1 := by
    have hdet : rowTransform_0639.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0639 hU
  have hcols := hrows.permuteColumns columnPerm_0639
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0639 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0639 = targetTop_0639 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0639 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 6 7)) 9 := by
  have htop : targetTop_0639 =
      topOfPattern (R := ℤ) (angle6 0 2 4 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0639

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039
