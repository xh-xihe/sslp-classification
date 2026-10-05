-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R028.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard045

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 4, 7, 7, 7)`. -/
def targetTop_0720 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0720 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0720 :
    TopRowRelation targetTop_0720 relationCoefficients_0720 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0720, relationCoefficients_0720, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0720 : BottomDetBound targetTop_0720 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0720

theorem canonicalBound_0720 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 4 7 7 7)) 9 := by
  have htop : targetTop_0720 =
      topOfPattern (R := ℤ) (angle6 0 3 4 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0720

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 5, 5, 5, 5)`. -/
def targetTop_0721 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0721 : Fin 3 → ℤ :=
  ![1, (-1), (-1)]

theorem topRelation_0721 :
    TopRowRelation targetTop_0721 relationCoefficients_0721 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0721, relationCoefficients_0721, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0721 : BottomDetBound targetTop_0721 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0721

theorem canonicalBound_0721 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 5 5)) 9 := by
  have htop : targetTop_0721 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0721

/-- Explicit target top block for canonical pattern `(0, 3, 5, 5, 5, 6)`. -/
def targetTop_0722 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0722 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0722 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0722 : BottomDetBound targetTop_0722 9 := by
  have hU : rowTransform_0722.det.natAbs = 1 := by
    have hdet : rowTransform_0722.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Aggregate.bottomBound.transformTopRows rowTransform_0722 hU
  have hcols := hrows.permuteColumns columnPerm_0722
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0722 MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Base.explicitTop)
          columnPerm_0722 = targetTop_0722 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0722 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 5 6)) 9 := by
  have htop : targetTop_0722 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0722

/-- Explicit target top block for canonical pattern `(0, 3, 5, 5, 5, 7)`. -/
def targetTop_0723 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0723 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0723 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0723 : BottomDetBound targetTop_0723 9 := by
  have hU : rowTransform_0723.det.natAbs = 1 := by
    have hdet : rowTransform_0723.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0723 hU
  have hcols := hrows.permuteColumns columnPerm_0723
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0723 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0723 = targetTop_0723 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0723 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 5 7)) 9 := by
  have htop : targetTop_0723 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0723

/-- Explicit target top block for canonical pattern `(0, 3, 5, 5, 6, 6)`. -/
def targetTop_0724 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0724 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0724 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0724 : BottomDetBound targetTop_0724 9 := by
  have hU : rowTransform_0724.det.natAbs = 1 := by
    have hdet : rowTransform_0724.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Aggregate.bottomBound.transformTopRows rowTransform_0724 hU
  have hcols := hrows.permuteColumns columnPerm_0724
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0724 MainTheory.Generated.BinaryBetaSixKernel.Representative.R026.Base.explicitTop)
          columnPerm_0724 = targetTop_0724 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0724 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 6 6)) 9 := by
  have htop : targetTop_0724 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0724

/-- Explicit target top block for canonical pattern `(0, 3, 5, 5, 6, 7)`. -/
def targetTop_0725 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0725 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0725 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0725 : BottomDetBound targetTop_0725 9 := by
  have hU : rowTransform_0725.det.natAbs = 1 := by
    have hdet : rowTransform_0725.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Aggregate.bottomBound.transformTopRows rowTransform_0725 hU
  have hcols := hrows.permuteColumns columnPerm_0725
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0725 MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Base.explicitTop)
          columnPerm_0725 = targetTop_0725 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0725 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 6 7)) 9 := by
  have htop : targetTop_0725 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0725

/-- Explicit target top block for canonical pattern `(0, 3, 5, 5, 7, 7)`. -/
def targetTop_0726 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0726 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     1, 1, 0]

def columnPerm_0726 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0726 : BottomDetBound targetTop_0726 9 := by
  have hU : rowTransform_0726.det.natAbs = 1 := by
    have hdet : rowTransform_0726.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0726 hU
  have hcols := hrows.permuteColumns columnPerm_0726
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0726 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0726 = targetTop_0726 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0726 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 5 7 7)) 9 := by
  have htop : targetTop_0726 =
      topOfPattern (R := ℤ) (angle6 0 3 5 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0726

/-- Explicit target top block for canonical pattern `(0, 3, 5, 6, 6, 6)`. -/
def targetTop_0727 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0727 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0727 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0727 : BottomDetBound targetTop_0727 9 := by
  have hU : rowTransform_0727.det.natAbs = 1 := by
    have hdet : rowTransform_0727.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Aggregate.bottomBound.transformTopRows rowTransform_0727 hU
  have hcols := hrows.permuteColumns columnPerm_0727
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0727 MainTheory.Generated.BinaryBetaSixKernel.Representative.R025.Base.explicitTop)
          columnPerm_0727 = targetTop_0727 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0727 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 6 6 6)) 9 := by
  have htop : targetTop_0727 =
      topOfPattern (R := ℤ) (angle6 0 3 5 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0727

/-- Explicit target top block for canonical pattern `(0, 3, 5, 6, 6, 7)`. -/
def targetTop_0728 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0728 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0728 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0728 : BottomDetBound targetTop_0728 9 := by
  have hU : rowTransform_0728.det.natAbs = 1 := by
    have hdet : rowTransform_0728.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Aggregate.bottomBound.transformTopRows rowTransform_0728 hU
  have hcols := hrows.permuteColumns columnPerm_0728
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0728 MainTheory.Generated.BinaryBetaSixKernel.Representative.R027.Base.explicitTop)
          columnPerm_0728 = targetTop_0728 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0728 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 6 6 7)) 9 := by
  have htop : targetTop_0728 =
      topOfPattern (R := ℤ) (angle6 0 3 5 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0728

/-- Explicit target top block for canonical pattern `(0, 3, 5, 6, 7, 7)`. -/
def targetTop_0729 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0729 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0729 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0729 : BottomDetBound targetTop_0729 9 := by
  have hU : rowTransform_0729.det.natAbs = 1 := by
    have hdet : rowTransform_0729.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R028.Aggregate.bottomBound.transformTopRows rowTransform_0729 hU
  have hcols := hrows.permuteColumns columnPerm_0729
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0729 MainTheory.Generated.BinaryBetaSixKernel.Representative.R028.Base.explicitTop)
          columnPerm_0729 = targetTop_0729 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0729 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 6 7 7)) 9 := by
  have htop : targetTop_0729 =
      topOfPattern (R := ℤ) (angle6 0 3 5 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0729

/-- Explicit target top block for canonical pattern `(0, 3, 5, 7, 7, 7)`. -/
def targetTop_0730 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0730 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0730 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0730 : BottomDetBound targetTop_0730 9 := by
  have hU : rowTransform_0730.det.natAbs = 1 := by
    have hdet : rowTransform_0730.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0730 hU
  have hcols := hrows.permuteColumns columnPerm_0730
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0730 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0730 = targetTop_0730 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0730 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 5 7 7 7)) 9 := by
  have htop : targetTop_0730 =
      topOfPattern (R := ℤ) (angle6 0 3 5 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0730

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 6, 6, 6, 6)`. -/
def targetTop_0731 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0731 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0731 :
    TopRowRelation targetTop_0731 relationCoefficients_0731 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0731, relationCoefficients_0731, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0731 : BottomDetBound targetTop_0731 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0731

theorem canonicalBound_0731 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 6 6 6 6)) 9 := by
  have htop : targetTop_0731 =
      topOfPattern (R := ℤ) (angle6 0 3 6 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0731

/-- Explicit target top block for canonical pattern `(0, 3, 6, 6, 6, 7)`. -/
def targetTop_0732 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0732 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0732 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0732 : BottomDetBound targetTop_0732 9 := by
  have hU : rowTransform_0732.det.natAbs = 1 := by
    have hdet : rowTransform_0732.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0732 hU
  have hcols := hrows.permuteColumns columnPerm_0732
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0732 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0732 = targetTop_0732 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0732 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 6 6 6 7)) 9 := by
  have htop : targetTop_0732 =
      topOfPattern (R := ℤ) (angle6 0 3 6 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0732

/-- Explicit target top block for canonical pattern `(0, 3, 6, 6, 7, 7)`. -/
def targetTop_0733 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0733 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     1, 1, 0]

def columnPerm_0733 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0733 : BottomDetBound targetTop_0733 9 := by
  have hU : rowTransform_0733.det.natAbs = 1 := by
    have hdet : rowTransform_0733.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0733 hU
  have hcols := hrows.permuteColumns columnPerm_0733
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0733 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0733 = targetTop_0733 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0733 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 6 6 7 7)) 9 := by
  have htop : targetTop_0733 =
      topOfPattern (R := ℤ) (angle6 0 3 6 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0733

/-- Explicit target top block for canonical pattern `(0, 3, 6, 7, 7, 7)`. -/
def targetTop_0734 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0734 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     1, 1, 1;
     1, 0, 1]

def columnPerm_0734 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0734 : BottomDetBound targetTop_0734 9 := by
  have hU : rowTransform_0734.det.natAbs = 1 := by
    have hdet : rowTransform_0734.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0734 hU
  have hcols := hrows.permuteColumns columnPerm_0734
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0734 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0734 = targetTop_0734 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0734 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 6 7 7 7)) 9 := by
  have htop : targetTop_0734 =
      topOfPattern (R := ℤ) (angle6 0 3 6 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0734

/-- Explicit rank-deficient target for canonical pattern `(0, 3, 7, 7, 7, 7)`. -/
def targetTop_0735 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 1, 1, 1, 1;
     0, 0, 1, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0735 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0735 :
    TopRowRelation targetTop_0735 relationCoefficients_0735 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0735, relationCoefficients_0735, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0735 : BottomDetBound targetTop_0735 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0735

theorem canonicalBound_0735 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 7 7 7 7)) 9 := by
  have htop : targetTop_0735 =
      topOfPattern (R := ℤ) (angle6 0 3 7 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0735

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard045
