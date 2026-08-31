-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 2, 3)`. -/
def targetTop_0128 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0128 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0128 :
    TopRowRelation targetTop_0128 relationCoefficients_0128 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0128, relationCoefficients_0128, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0128 : BottomDetBound targetTop_0128 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0128

theorem canonicalBound_0128 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 3)) 9 := by
  have htop : targetTop_0128 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0128

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 2, 4)`. -/
def targetTop_0129 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0129 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0129 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0129 : BottomDetBound targetTop_0129 9 := by
  have hU : rowTransform_0129.det.natAbs = 1 := by
    have hdet : rowTransform_0129.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0129 hU
  have hcols := hrows.permuteColumns columnPerm_0129
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0129 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0129 = targetTop_0129 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0129 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 4)) 9 := by
  have htop : targetTop_0129 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0129

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 2, 5)`. -/
def targetTop_0130 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0130 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0130 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0130 : BottomDetBound targetTop_0130 9 := by
  have hU : rowTransform_0130.det.natAbs = 1 := by
    have hdet : rowTransform_0130.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0130 hU
  have hcols := hrows.permuteColumns columnPerm_0130
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0130 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0130 = targetTop_0130 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0130 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 5)) 9 := by
  have htop : targetTop_0130 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0130

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 2, 6)`. -/
def targetTop_0131 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0131 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0131 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0131 : BottomDetBound targetTop_0131 9 := by
  have hU : rowTransform_0131.det.natAbs = 1 := by
    have hdet : rowTransform_0131.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0131 hU
  have hcols := hrows.permuteColumns columnPerm_0131
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0131 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0131 = targetTop_0131 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0131 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 6)) 9 := by
  have htop : targetTop_0131 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0131

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 2, 7)`. -/
def targetTop_0132 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0132 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0132 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0132 : BottomDetBound targetTop_0132 9 := by
  have hU : rowTransform_0132.det.natAbs = 1 := by
    have hdet : rowTransform_0132.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0132 hU
  have hcols := hrows.permuteColumns columnPerm_0132
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0132 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0132 = targetTop_0132 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0132 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 7)) 9 := by
  have htop : targetTop_0132 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0132

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 3, 3)`. -/
def targetTop_0133 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0133 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0133 :
    TopRowRelation targetTop_0133 relationCoefficients_0133 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0133, relationCoefficients_0133, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0133 : BottomDetBound targetTop_0133 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0133

theorem canonicalBound_0133 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 3)) 9 := by
  have htop : targetTop_0133 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0133

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 3, 4)`. -/
def targetTop_0134 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0134 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0134 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0134 : BottomDetBound targetTop_0134 9 := by
  have hU : rowTransform_0134.det.natAbs = 1 := by
    have hdet : rowTransform_0134.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0134 hU
  have hcols := hrows.permuteColumns columnPerm_0134
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0134 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0134 = targetTop_0134 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0134 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 4)) 9 := by
  have htop : targetTop_0134 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0134

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 3, 5)`. -/
def targetTop_0135 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0135 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0135 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0135 : BottomDetBound targetTop_0135 9 := by
  have hU : rowTransform_0135.det.natAbs = 1 := by
    have hdet : rowTransform_0135.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0135 hU
  have hcols := hrows.permuteColumns columnPerm_0135
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0135 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0135 = targetTop_0135 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0135 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 5)) 9 := by
  have htop : targetTop_0135 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0135

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 3, 6)`. -/
def targetTop_0136 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0136 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0136 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0136 : BottomDetBound targetTop_0136 9 := by
  have hU : rowTransform_0136.det.natAbs = 1 := by
    have hdet : rowTransform_0136.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0136 hU
  have hcols := hrows.permuteColumns columnPerm_0136
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0136 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0136 = targetTop_0136 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0136 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 6)) 9 := by
  have htop : targetTop_0136 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0136

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 3, 7)`. -/
def targetTop_0137 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0137 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0137 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0137 : BottomDetBound targetTop_0137 9 := by
  have hU : rowTransform_0137.det.natAbs = 1 := by
    have hdet : rowTransform_0137.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0137 hU
  have hcols := hrows.permuteColumns columnPerm_0137
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0137 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0137 = targetTop_0137 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0137 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 7)) 9 := by
  have htop : targetTop_0137 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0137

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 4, 4)`. -/
def targetTop_0138 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0138 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0138 :
    TopRowRelation targetTop_0138 relationCoefficients_0138 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0138, relationCoefficients_0138, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0138 : BottomDetBound targetTop_0138 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0138

theorem canonicalBound_0138 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 4 4)) 9 := by
  have htop : targetTop_0138 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0138

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 4, 5)`. -/
def targetTop_0139 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0139 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0139 :
    TopRowRelation targetTop_0139 relationCoefficients_0139 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0139, relationCoefficients_0139, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0139 : BottomDetBound targetTop_0139 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0139

theorem canonicalBound_0139 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 4 5)) 9 := by
  have htop : targetTop_0139 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0139

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 4, 6)`. -/
def targetTop_0140 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0140 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0140 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0140 : BottomDetBound targetTop_0140 9 := by
  have hU : rowTransform_0140.det.natAbs = 1 := by
    have hdet : rowTransform_0140.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0140 hU
  have hcols := hrows.permuteColumns columnPerm_0140
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0140 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0140 = targetTop_0140 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0140 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 4 6)) 9 := by
  have htop : targetTop_0140 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0140

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 4, 7)`. -/
def targetTop_0141 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0141 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0141 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0141 : BottomDetBound targetTop_0141 9 := by
  have hU : rowTransform_0141.det.natAbs = 1 := by
    have hdet : rowTransform_0141.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0141 hU
  have hcols := hrows.permuteColumns columnPerm_0141
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0141 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0141 = targetTop_0141 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0141 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 4 7)) 9 := by
  have htop : targetTop_0141 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0141

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 5, 5)`. -/
def targetTop_0142 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0142 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0142 :
    TopRowRelation targetTop_0142 relationCoefficients_0142 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0142, relationCoefficients_0142, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0142 : BottomDetBound targetTop_0142 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0142

theorem canonicalBound_0142 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 5 5)) 9 := by
  have htop : targetTop_0142 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0142

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 5, 6)`. -/
def targetTop_0143 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0143 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0143 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0143 : BottomDetBound targetTop_0143 9 := by
  have hU : rowTransform_0143.det.natAbs = 1 := by
    have hdet : rowTransform_0143.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0143 hU
  have hcols := hrows.permuteColumns columnPerm_0143
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0143 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0143 = targetTop_0143 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0143 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 5 6)) 9 := by
  have htop : targetTop_0143 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0143

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008
