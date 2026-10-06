-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 2, 7)`. -/
def targetTop_0048 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0048 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0048 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0048 : BottomDetBound targetTop_0048 9 := by
  have hU : rowTransform_0048.det.natAbs = 1 := by
    have hdet : rowTransform_0048.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0048 hU
  have hcols := hrows.permuteColumns columnPerm_0048
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0048 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0048 = targetTop_0048 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0048 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 7)) 9 := by
  have htop : targetTop_0048 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0048

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 3, 3)`. -/
def targetTop_0049 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0049 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0049 :
    TopRowRelation targetTop_0049 relationCoefficients_0049 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0049, relationCoefficients_0049, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0049 : BottomDetBound targetTop_0049 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0049

theorem canonicalBound_0049 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 3)) 9 := by
  have htop : targetTop_0049 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0049

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 3, 4)`. -/
def targetTop_0050 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0050 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0050 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0050 : BottomDetBound targetTop_0050 9 := by
  have hU : rowTransform_0050.det.natAbs = 1 := by
    have hdet : rowTransform_0050.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0050 hU
  have hcols := hrows.permuteColumns columnPerm_0050
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0050 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0050 = targetTop_0050 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0050 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 4)) 9 := by
  have htop : targetTop_0050 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0050

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 3, 5)`. -/
def targetTop_0051 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0051 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0051 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0051 : BottomDetBound targetTop_0051 9 := by
  have hU : rowTransform_0051.det.natAbs = 1 := by
    have hdet : rowTransform_0051.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0051 hU
  have hcols := hrows.permuteColumns columnPerm_0051
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0051 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0051 = targetTop_0051 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0051 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 5)) 9 := by
  have htop : targetTop_0051 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0051

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 3, 6)`. -/
def targetTop_0052 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0052 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0052 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0052 : BottomDetBound targetTop_0052 9 := by
  have hU : rowTransform_0052.det.natAbs = 1 := by
    have hdet : rowTransform_0052.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0052 hU
  have hcols := hrows.permuteColumns columnPerm_0052
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0052 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0052 = targetTop_0052 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0052 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 6)) 9 := by
  have htop : targetTop_0052 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0052

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 3, 7)`. -/
def targetTop_0053 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0053 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0053 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0053 : BottomDetBound targetTop_0053 9 := by
  have hU : rowTransform_0053.det.natAbs = 1 := by
    have hdet : rowTransform_0053.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0053 hU
  have hcols := hrows.permuteColumns columnPerm_0053
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0053 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0053 = targetTop_0053 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0053 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 3 7)) 9 := by
  have htop : targetTop_0053 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0053

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 4, 4)`. -/
def targetTop_0054 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0054 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0054 :
    TopRowRelation targetTop_0054 relationCoefficients_0054 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0054, relationCoefficients_0054, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0054 : BottomDetBound targetTop_0054 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0054

theorem canonicalBound_0054 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 4 4)) 9 := by
  have htop : targetTop_0054 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0054

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 4, 5)`. -/
def targetTop_0055 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0055 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0055 :
    TopRowRelation targetTop_0055 relationCoefficients_0055 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0055, relationCoefficients_0055, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0055 : BottomDetBound targetTop_0055 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0055

theorem canonicalBound_0055 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 4 5)) 9 := by
  have htop : targetTop_0055 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0055

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 4, 6)`. -/
def targetTop_0056 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0056 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0056 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0056 : BottomDetBound targetTop_0056 9 := by
  have hU : rowTransform_0056.det.natAbs = 1 := by
    have hdet : rowTransform_0056.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0056 hU
  have hcols := hrows.permuteColumns columnPerm_0056
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0056 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0056 = targetTop_0056 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0056 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 4 6)) 9 := by
  have htop : targetTop_0056 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0056

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 4, 7)`. -/
def targetTop_0057 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0057 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0057 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0057 : BottomDetBound targetTop_0057 9 := by
  have hU : rowTransform_0057.det.natAbs = 1 := by
    have hdet : rowTransform_0057.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0057 hU
  have hcols := hrows.permuteColumns columnPerm_0057
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0057 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0057 = targetTop_0057 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0057 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 4 7)) 9 := by
  have htop : targetTop_0057 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0057

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 5, 5)`. -/
def targetTop_0058 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0058 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0058 :
    TopRowRelation targetTop_0058 relationCoefficients_0058 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0058, relationCoefficients_0058, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0058 : BottomDetBound targetTop_0058 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0058

theorem canonicalBound_0058 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 5 5)) 9 := by
  have htop : targetTop_0058 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0058

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 5, 6)`. -/
def targetTop_0059 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0059 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0059 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0059 : BottomDetBound targetTop_0059 9 := by
  have hU : rowTransform_0059.det.natAbs = 1 := by
    have hdet : rowTransform_0059.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0059 hU
  have hcols := hrows.permuteColumns columnPerm_0059
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0059 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0059 = targetTop_0059 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0059 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 5 6)) 9 := by
  have htop : targetTop_0059 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0059

/-- Explicit target top block for canonical pattern `(0, 0, 0, 1, 5, 7)`. -/
def targetTop_0060 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0060 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0060 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0060 : BottomDetBound targetTop_0060 9 := by
  have hU : rowTransform_0060.det.natAbs = 1 := by
    have hdet : rowTransform_0060.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0060 hU
  have hcols := hrows.permuteColumns columnPerm_0060
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0060 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0060 = targetTop_0060 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0060 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 5 7)) 9 := by
  have htop : targetTop_0060 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0060

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 6, 6)`. -/
def targetTop_0061 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0061 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0061 :
    TopRowRelation targetTop_0061 relationCoefficients_0061 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0061, relationCoefficients_0061, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0061 : BottomDetBound targetTop_0061 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0061

theorem canonicalBound_0061 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 6 6)) 9 := by
  have htop : targetTop_0061 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0061

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 6, 7)`. -/
def targetTop_0062 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0062 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0062 :
    TopRowRelation targetTop_0062 relationCoefficients_0062 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0062, relationCoefficients_0062, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0062 : BottomDetBound targetTop_0062 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0062

theorem canonicalBound_0062 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 6 7)) 9 := by
  have htop : targetTop_0062 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0062

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 1, 7, 7)`. -/
def targetTop_0063 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0063 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0063 :
    TopRowRelation targetTop_0063 relationCoefficients_0063 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0063, relationCoefficients_0063, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0063 : BottomDetBound targetTop_0063 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0063

theorem canonicalBound_0063 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 7 7)) 9 := by
  have htop : targetTop_0063 =
      topOfPattern (R := ℤ) (angle6 0 0 0 1 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0063

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003
