-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 4, 5)`. -/
def targetTop_0832 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0832 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0832 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0832 : BottomDetBound targetTop_0832 9 := by
  have hU : rowTransform_0832.det.natAbs = 1 := by
    have hdet : rowTransform_0832.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0832 hU
  have hcols := hrows.permuteColumns columnPerm_0832
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0832 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0832 = targetTop_0832 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0832 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 4 5)) 9 := by
  have htop : targetTop_0832 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0832

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 4, 6)`. -/
def targetTop_0833 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0833 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0833 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0833 : BottomDetBound targetTop_0833 9 := by
  have hU : rowTransform_0833.det.natAbs = 1 := by
    have hdet : rowTransform_0833.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_0833 hU
  have hcols := hrows.permuteColumns columnPerm_0833
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0833 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_0833 = targetTop_0833 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0833 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 4 6)) 9 := by
  have htop : targetTop_0833 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0833

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 4, 7)`. -/
def targetTop_0834 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0834 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0834 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0834 : BottomDetBound targetTop_0834 9 := by
  have hU : rowTransform_0834.det.natAbs = 1 := by
    have hdet : rowTransform_0834.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Aggregate.bottomBound.transformTopRows rowTransform_0834 hU
  have hcols := hrows.permuteColumns columnPerm_0834
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0834 MainTheory.Generated.BinaryBetaSixKernel.Representative.R033.Base.explicitTop)
          columnPerm_0834 = targetTop_0834 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0834 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 4 7)) 9 := by
  have htop : targetTop_0834 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0834

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 5, 5)`. -/
def targetTop_0835 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0835 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0835 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0835 : BottomDetBound targetTop_0835 9 := by
  have hU : rowTransform_0835.det.natAbs = 1 := by
    have hdet : rowTransform_0835.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0835 hU
  have hcols := hrows.permuteColumns columnPerm_0835
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0835 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0835 = targetTop_0835 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0835 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 5 5)) 9 := by
  have htop : targetTop_0835 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0835

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 5, 6)`. -/
def targetTop_0836 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0836 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0836 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0836 : BottomDetBound targetTop_0836 9 := by
  have hU : rowTransform_0836.det.natAbs = 1 := by
    have hdet : rowTransform_0836.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Aggregate.bottomBound.transformTopRows rowTransform_0836 hU
  have hcols := hrows.permuteColumns columnPerm_0836
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0836 MainTheory.Generated.BinaryBetaSixKernel.Representative.R034.Base.explicitTop)
          columnPerm_0836 = targetTop_0836 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0836 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 5 6)) 9 := by
  have htop : targetTop_0836 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0836

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 5, 7)`. -/
def targetTop_0837 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0837 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0837 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0837 : BottomDetBound targetTop_0837 9 := by
  have hU : rowTransform_0837.det.natAbs = 1 := by
    have hdet : rowTransform_0837.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Aggregate.bottomBound.transformTopRows rowTransform_0837 hU
  have hcols := hrows.permuteColumns columnPerm_0837
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0837 MainTheory.Generated.BinaryBetaSixKernel.Representative.R032.Base.explicitTop)
          columnPerm_0837 = targetTop_0837 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0837 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 5 7)) 9 := by
  have htop : targetTop_0837 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0837

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 6, 6)`. -/
def targetTop_0838 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0838 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0838 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0838 : BottomDetBound targetTop_0838 9 := by
  have hU : rowTransform_0838.det.natAbs = 1 := by
    have hdet : rowTransform_0838.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0838 hU
  have hcols := hrows.permuteColumns columnPerm_0838
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0838 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0838 = targetTop_0838 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0838 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 6 6)) 9 := by
  have htop : targetTop_0838 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0838

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 6, 7)`. -/
def targetTop_0839 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0839 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0839 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0839 : BottomDetBound targetTop_0839 9 := by
  have hU : rowTransform_0839.det.natAbs = 1 := by
    have hdet : rowTransform_0839.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0839 hU
  have hcols := hrows.permuteColumns columnPerm_0839
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0839 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0839 = targetTop_0839 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0839 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 6 7)) 9 := by
  have htop : targetTop_0839 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0839

/-- Explicit target top block for canonical pattern `(1, 1, 1, 2, 7, 7)`. -/
def targetTop_0840 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0840 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0840 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0840 : BottomDetBound targetTop_0840 9 := by
  have hU : rowTransform_0840.det.natAbs = 1 := by
    have hdet : rowTransform_0840.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0840 hU
  have hcols := hrows.permuteColumns columnPerm_0840
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0840 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0840 = targetTop_0840 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0840 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 7 7)) 9 := by
  have htop : targetTop_0840 =
      topOfPattern (R := ℤ) (angle6 1 1 1 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0840

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 3, 3, 3)`. -/
def targetTop_0841 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0841 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0841 :
    TopRowRelation targetTop_0841 relationCoefficients_0841 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0841, relationCoefficients_0841, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0841 : BottomDetBound targetTop_0841 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0841

theorem canonicalBound_0841 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 3)) 9 := by
  have htop : targetTop_0841 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0841

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 3, 4)`. -/
def targetTop_0842 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0842 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0842 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0842 : BottomDetBound targetTop_0842 9 := by
  have hU : rowTransform_0842.det.natAbs = 1 := by
    have hdet : rowTransform_0842.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0842 hU
  have hcols := hrows.permuteColumns columnPerm_0842
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0842 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0842 = targetTop_0842 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0842 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 4)) 9 := by
  have htop : targetTop_0842 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0842

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 3, 5)`. -/
def targetTop_0843 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0843 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0843 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0843 : BottomDetBound targetTop_0843 9 := by
  have hU : rowTransform_0843.det.natAbs = 1 := by
    have hdet : rowTransform_0843.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0843 hU
  have hcols := hrows.permuteColumns columnPerm_0843
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0843 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0843 = targetTop_0843 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0843 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 5)) 9 := by
  have htop : targetTop_0843 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0843

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 3, 6)`. -/
def targetTop_0844 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0844 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0844 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0844 : BottomDetBound targetTop_0844 9 := by
  have hU : rowTransform_0844.det.natAbs = 1 := by
    have hdet : rowTransform_0844.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0844 hU
  have hcols := hrows.permuteColumns columnPerm_0844
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0844 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0844 = targetTop_0844 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0844 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 6)) 9 := by
  have htop : targetTop_0844 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0844

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 3, 7)`. -/
def targetTop_0845 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0845 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0845 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0845 : BottomDetBound targetTop_0845 9 := by
  have hU : rowTransform_0845.det.natAbs = 1 := by
    have hdet : rowTransform_0845.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0845 hU
  have hcols := hrows.permuteColumns columnPerm_0845
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0845 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0845 = targetTop_0845 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0845 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 7)) 9 := by
  have htop : targetTop_0845 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0845

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 4, 4)`. -/
def targetTop_0846 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0846 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0846 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0846 : BottomDetBound targetTop_0846 9 := by
  have hU : rowTransform_0846.det.natAbs = 1 := by
    have hdet : rowTransform_0846.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0846 hU
  have hcols := hrows.permuteColumns columnPerm_0846
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0846 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0846 = targetTop_0846 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0846 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 4 4)) 9 := by
  have htop : targetTop_0846 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0846

/-- Explicit target top block for canonical pattern `(1, 1, 1, 3, 4, 5)`. -/
def targetTop_0847 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0847 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 0]

def columnPerm_0847 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0847 : BottomDetBound targetTop_0847 9 := by
  have hU : rowTransform_0847.det.natAbs = 1 := by
    have hdet : rowTransform_0847.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0847 hU
  have hcols := hrows.permuteColumns columnPerm_0847
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0847 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0847 = targetTop_0847 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0847 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 4 5)) 9 := by
  have htop : targetTop_0847 =
      topOfPattern (R := ℤ) (angle6 1 1 1 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0847

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052
