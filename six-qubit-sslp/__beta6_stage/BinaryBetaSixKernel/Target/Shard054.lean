-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 6, 7)`. -/
def targetTop_0864 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0864 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0864 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0864 : BottomDetBound targetTop_0864 9 := by
  have hU : rowTransform_0864.det.natAbs = 1 := by
    have hdet : rowTransform_0864.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0864 hU
  have hcols := hrows.permuteColumns columnPerm_0864
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0864 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0864 = targetTop_0864 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0864 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 6 7)) 9 := by
  have htop : targetTop_0864 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0864

/-- Explicit target top block for canonical pattern `(1, 1, 1, 4, 7, 7)`. -/
def targetTop_0865 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0865 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0865 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0865 : BottomDetBound targetTop_0865 9 := by
  have hU : rowTransform_0865.det.natAbs = 1 := by
    have hdet : rowTransform_0865.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0865 hU
  have hcols := hrows.permuteColumns columnPerm_0865
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0865 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0865 = targetTop_0865 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0865 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 4 7 7)) 9 := by
  have htop : targetTop_0865 =
      topOfPattern (R := ℤ) (angle6 1 1 1 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0865

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 5, 5, 5)`. -/
def targetTop_0866 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0866 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0866 :
    TopRowRelation targetTop_0866 relationCoefficients_0866 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0866, relationCoefficients_0866, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0866 : BottomDetBound targetTop_0866 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0866

theorem canonicalBound_0866 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 5 5)) 9 := by
  have htop : targetTop_0866 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0866

/-- Explicit target top block for canonical pattern `(1, 1, 1, 5, 5, 6)`. -/
def targetTop_0867 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0867 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0867 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0867 : BottomDetBound targetTop_0867 9 := by
  have hU : rowTransform_0867.det.natAbs = 1 := by
    have hdet : rowTransform_0867.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0867 hU
  have hcols := hrows.permuteColumns columnPerm_0867
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0867 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0867 = targetTop_0867 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0867 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 5 6)) 9 := by
  have htop : targetTop_0867 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0867

/-- Explicit target top block for canonical pattern `(1, 1, 1, 5, 5, 7)`. -/
def targetTop_0868 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0868 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0868 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0868 : BottomDetBound targetTop_0868 9 := by
  have hU : rowTransform_0868.det.natAbs = 1 := by
    have hdet : rowTransform_0868.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0868 hU
  have hcols := hrows.permuteColumns columnPerm_0868
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0868 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0868 = targetTop_0868 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0868 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 5 7)) 9 := by
  have htop : targetTop_0868 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0868

/-- Explicit target top block for canonical pattern `(1, 1, 1, 5, 6, 6)`. -/
def targetTop_0869 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0869 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0869 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0869 : BottomDetBound targetTop_0869 9 := by
  have hU : rowTransform_0869.det.natAbs = 1 := by
    have hdet : rowTransform_0869.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0869 hU
  have hcols := hrows.permuteColumns columnPerm_0869
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0869 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0869 = targetTop_0869 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0869 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 6 6)) 9 := by
  have htop : targetTop_0869 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0869

/-- Explicit target top block for canonical pattern `(1, 1, 1, 5, 6, 7)`. -/
def targetTop_0870 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0870 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0870 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0870 : BottomDetBound targetTop_0870 9 := by
  have hU : rowTransform_0870.det.natAbs = 1 := by
    have hdet : rowTransform_0870.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Aggregate.bottomBound.transformTopRows rowTransform_0870 hU
  have hcols := hrows.permuteColumns columnPerm_0870
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0870 MainTheory.Generated.BinaryBetaSixKernel.Representative.R031.Base.explicitTop)
          columnPerm_0870 = targetTop_0870 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0870 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 6 7)) 9 := by
  have htop : targetTop_0870 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0870

/-- Explicit target top block for canonical pattern `(1, 1, 1, 5, 7, 7)`. -/
def targetTop_0871 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0871 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0871 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0871 : BottomDetBound targetTop_0871 9 := by
  have hU : rowTransform_0871.det.natAbs = 1 := by
    have hdet : rowTransform_0871.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0871 hU
  have hcols := hrows.permuteColumns columnPerm_0871
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0871 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0871 = targetTop_0871 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0871 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 5 7 7)) 9 := by
  have htop : targetTop_0871 =
      topOfPattern (R := ℤ) (angle6 1 1 1 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0871

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 6, 6, 6)`. -/
def targetTop_0872 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0872 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0872 :
    TopRowRelation targetTop_0872 relationCoefficients_0872 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0872, relationCoefficients_0872, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0872 : BottomDetBound targetTop_0872 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0872

theorem canonicalBound_0872 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 6 6 6)) 9 := by
  have htop : targetTop_0872 =
      topOfPattern (R := ℤ) (angle6 1 1 1 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0872

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 6, 6, 7)`. -/
def targetTop_0873 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0873 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0873 :
    TopRowRelation targetTop_0873 relationCoefficients_0873 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0873, relationCoefficients_0873, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0873 : BottomDetBound targetTop_0873 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0873

theorem canonicalBound_0873 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 6 6 7)) 9 := by
  have htop : targetTop_0873 =
      topOfPattern (R := ℤ) (angle6 1 1 1 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0873

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 6, 7, 7)`. -/
def targetTop_0874 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0874 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0874 :
    TopRowRelation targetTop_0874 relationCoefficients_0874 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0874, relationCoefficients_0874, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0874 : BottomDetBound targetTop_0874 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0874

theorem canonicalBound_0874 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 6 7 7)) 9 := by
  have htop : targetTop_0874 =
      topOfPattern (R := ℤ) (angle6 1 1 1 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0874

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 1, 7, 7, 7)`. -/
def targetTop_0875 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0875 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0875 :
    TopRowRelation targetTop_0875 relationCoefficients_0875 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0875, relationCoefficients_0875, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0875 : BottomDetBound targetTop_0875 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0875

theorem canonicalBound_0875 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 7 7 7)) 9 := by
  have htop : targetTop_0875 =
      topOfPattern (R := ℤ) (angle6 1 1 1 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0875

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 2, 2, 2, 2)`. -/
def targetTop_0876 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0876 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0876 :
    TopRowRelation targetTop_0876 relationCoefficients_0876 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0876, relationCoefficients_0876, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0876 : BottomDetBound targetTop_0876 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0876

theorem canonicalBound_0876 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 2)) 9 := by
  have htop : targetTop_0876 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0876

/-- Explicit rank-deficient target for canonical pattern `(1, 1, 2, 2, 2, 3)`. -/
def targetTop_0877 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0877 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0877 :
    TopRowRelation targetTop_0877 relationCoefficients_0877 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0877, relationCoefficients_0877, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0877 : BottomDetBound targetTop_0877 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0877

theorem canonicalBound_0877 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 3)) 9 := by
  have htop : targetTop_0877 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0877

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 2, 4)`. -/
def targetTop_0878 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0878 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0878 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0878 : BottomDetBound targetTop_0878 9 := by
  have hU : rowTransform_0878.det.natAbs = 1 := by
    have hdet : rowTransform_0878.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0878 hU
  have hcols := hrows.permuteColumns columnPerm_0878
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0878 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0878 = targetTop_0878 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0878 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 4)) 9 := by
  have htop : targetTop_0878 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0878

/-- Explicit target top block for canonical pattern `(1, 1, 2, 2, 2, 5)`. -/
def targetTop_0879 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0879 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0879 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0879 : BottomDetBound targetTop_0879 9 := by
  have hU : rowTransform_0879.det.natAbs = 1 := by
    have hdet : rowTransform_0879.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Aggregate.bottomBound.transformTopRows rowTransform_0879 hU
  have hcols := hrows.permuteColumns columnPerm_0879
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0879 MainTheory.Generated.BinaryBetaSixKernel.Representative.R030.Base.explicitTop)
          columnPerm_0879 = targetTop_0879 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0879 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 5)) 9 := by
  have htop : targetTop_0879 =
      topOfPattern (R := ℤ) (angle6 1 1 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0879

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054
