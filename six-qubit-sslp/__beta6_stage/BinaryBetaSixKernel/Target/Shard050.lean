-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 2, 3)`. -/
def targetTop_0800 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0800 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0800 :
    TopRowRelation targetTop_0800 relationCoefficients_0800 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0800, relationCoefficients_0800, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0800 : BottomDetBound targetTop_0800 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0800

theorem canonicalBound_0800 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 3)) 9 := by
  have htop : targetTop_0800 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0800

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 2, 4)`. -/
def targetTop_0801 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0801 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0801 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0801 : BottomDetBound targetTop_0801 9 := by
  have hU : rowTransform_0801.det.natAbs = 1 := by
    have hdet : rowTransform_0801.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0801 hU
  have hcols := hrows.permuteColumns columnPerm_0801
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0801 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0801 = targetTop_0801 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0801 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 4)) 9 := by
  have htop : targetTop_0801 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0801

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 2, 5)`. -/
def targetTop_0802 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0802 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0802 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0802 : BottomDetBound targetTop_0802 9 := by
  have hU : rowTransform_0802.det.natAbs = 1 := by
    have hdet : rowTransform_0802.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0802 hU
  have hcols := hrows.permuteColumns columnPerm_0802
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0802 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0802 = targetTop_0802 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0802 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 5)) 9 := by
  have htop : targetTop_0802 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0802

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 2, 6)`. -/
def targetTop_0803 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0803 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0803 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0803 : BottomDetBound targetTop_0803 9 := by
  have hU : rowTransform_0803.det.natAbs = 1 := by
    have hdet : rowTransform_0803.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0803 hU
  have hcols := hrows.permuteColumns columnPerm_0803
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0803 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0803 = targetTop_0803 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0803 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 6)) 9 := by
  have htop : targetTop_0803 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0803

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 2, 7)`. -/
def targetTop_0804 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0804 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0804 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0804 : BottomDetBound targetTop_0804 9 := by
  have hU : rowTransform_0804.det.natAbs = 1 := by
    have hdet : rowTransform_0804.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0804 hU
  have hcols := hrows.permuteColumns columnPerm_0804
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0804 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0804 = targetTop_0804 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0804 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 7)) 9 := by
  have htop : targetTop_0804 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0804

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 3, 3)`. -/
def targetTop_0805 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0805 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0805 :
    TopRowRelation targetTop_0805 relationCoefficients_0805 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0805, relationCoefficients_0805, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0805 : BottomDetBound targetTop_0805 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0805

theorem canonicalBound_0805 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 3 3)) 9 := by
  have htop : targetTop_0805 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0805

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 3, 4)`. -/
def targetTop_0806 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0806 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0806 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0806 : BottomDetBound targetTop_0806 9 := by
  have hU : rowTransform_0806.det.natAbs = 1 := by
    have hdet : rowTransform_0806.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0806 hU
  have hcols := hrows.permuteColumns columnPerm_0806
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0806 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0806 = targetTop_0806 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0806 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 3 4)) 9 := by
  have htop : targetTop_0806 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0806

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 3, 5)`. -/
def targetTop_0807 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0807 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0807 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0807 : BottomDetBound targetTop_0807 9 := by
  have hU : rowTransform_0807.det.natAbs = 1 := by
    have hdet : rowTransform_0807.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0807 hU
  have hcols := hrows.permuteColumns columnPerm_0807
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0807 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0807 = targetTop_0807 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0807 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 3 5)) 9 := by
  have htop : targetTop_0807 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0807

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 3, 6)`. -/
def targetTop_0808 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0808 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0808 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0808 : BottomDetBound targetTop_0808 9 := by
  have hU : rowTransform_0808.det.natAbs = 1 := by
    have hdet : rowTransform_0808.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0808 hU
  have hcols := hrows.permuteColumns columnPerm_0808
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0808 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0808 = targetTop_0808 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0808 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 3 6)) 9 := by
  have htop : targetTop_0808 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0808

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 3, 7)`. -/
def targetTop_0809 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0809 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0809 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0809 : BottomDetBound targetTop_0809 9 := by
  have hU : rowTransform_0809.det.natAbs = 1 := by
    have hdet : rowTransform_0809.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0809 hU
  have hcols := hrows.permuteColumns columnPerm_0809
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0809 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0809 = targetTop_0809 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0809 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 3 7)) 9 := by
  have htop : targetTop_0809 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0809

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 4, 4)`. -/
def targetTop_0810 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0810 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0810 :
    TopRowRelation targetTop_0810 relationCoefficients_0810 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0810, relationCoefficients_0810, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0810 : BottomDetBound targetTop_0810 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0810

theorem canonicalBound_0810 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 4 4)) 9 := by
  have htop : targetTop_0810 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0810

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 4, 5)`. -/
def targetTop_0811 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0811 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0811 :
    TopRowRelation targetTop_0811 relationCoefficients_0811 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0811, relationCoefficients_0811, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0811 : BottomDetBound targetTop_0811 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0811

theorem canonicalBound_0811 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 4 5)) 9 := by
  have htop : targetTop_0811 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0811

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 4, 6)`. -/
def targetTop_0812 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0812 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0812 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0812 : BottomDetBound targetTop_0812 9 := by
  have hU : rowTransform_0812.det.natAbs = 1 := by
    have hdet : rowTransform_0812.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0812 hU
  have hcols := hrows.permuteColumns columnPerm_0812
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0812 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0812 = targetTop_0812 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0812 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 4 6)) 9 := by
  have htop : targetTop_0812 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0812

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 4, 7)`. -/
def targetTop_0813 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0813 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0813 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0813 : BottomDetBound targetTop_0813 9 := by
  have hU : rowTransform_0813.det.natAbs = 1 := by
    have hdet : rowTransform_0813.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0813 hU
  have hcols := hrows.permuteColumns columnPerm_0813
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0813 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0813 = targetTop_0813 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0813 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 4 7)) 9 := by
  have htop : targetTop_0813 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0813

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 1, 5, 5)`. -/
def targetTop_0814 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0814 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0814 :
    TopRowRelation targetTop_0814 relationCoefficients_0814 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0814, relationCoefficients_0814, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0814 : BottomDetBound targetTop_0814 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0814

theorem canonicalBound_0814 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 5 5)) 9 := by
  have htop : targetTop_0814 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0814

/-- Explicit target top block for canonical pattern `(1, 1, 1, 1, 5, 6)`. -/
def targetTop_0815 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0815 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0815 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0815 : BottomDetBound targetTop_0815 9 := by
  have hU : rowTransform_0815.det.natAbs = 1 := by
    have hdet : rowTransform_0815.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Aggregate.bottomBound.transformTopRows rowTransform_0815 hU
  have hcols := hrows.permuteColumns columnPerm_0815
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0815 MainTheory.Generated.BinaryBetaSixKernel.Representative.R029.Base.explicitTop)
          columnPerm_0815 = targetTop_0815 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0815 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 5 6)) 9 := by
  have htop : targetTop_0815 =
      topOfPattern (R := ℤ) (angle6 1 1 1 1 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0815

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050
