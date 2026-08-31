-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 2)`. -/
def targetTop_0064 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0064 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0064 :
    TopRowRelation targetTop_0064 relationCoefficients_0064 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0064, relationCoefficients_0064, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0064 : BottomDetBound targetTop_0064 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0064

theorem canonicalBound_0064 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 2)) 9 := by
  have htop : targetTop_0064 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0064

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 3)`. -/
def targetTop_0065 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0065 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0065 :
    TopRowRelation targetTop_0065 relationCoefficients_0065 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0065, relationCoefficients_0065, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0065 : BottomDetBound targetTop_0065 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0065

theorem canonicalBound_0065 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 3)) 9 := by
  have htop : targetTop_0065 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0065

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 4)`. -/
def targetTop_0066 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0066 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0066 :
    TopRowRelation targetTop_0066 relationCoefficients_0066 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0066, relationCoefficients_0066, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0066 : BottomDetBound targetTop_0066 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0066

theorem canonicalBound_0066 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 4)) 9 := by
  have htop : targetTop_0066 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0066

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 5)`. -/
def targetTop_0067 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0067 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0067 :
    TopRowRelation targetTop_0067 relationCoefficients_0067 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0067, relationCoefficients_0067, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0067 : BottomDetBound targetTop_0067 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0067

theorem canonicalBound_0067 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 5)) 9 := by
  have htop : targetTop_0067 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0067

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 6)`. -/
def targetTop_0068 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0068 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0068 :
    TopRowRelation targetTop_0068 relationCoefficients_0068 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0068, relationCoefficients_0068, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0068 : BottomDetBound targetTop_0068 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0068

theorem canonicalBound_0068 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 6)) 9 := by
  have htop : targetTop_0068 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0068

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 2, 7)`. -/
def targetTop_0069 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0069 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0069 :
    TopRowRelation targetTop_0069 relationCoefficients_0069 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0069, relationCoefficients_0069, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0069 : BottomDetBound targetTop_0069 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0069

theorem canonicalBound_0069 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 2 7)) 9 := by
  have htop : targetTop_0069 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0069

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 3, 3)`. -/
def targetTop_0070 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0070 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0070 :
    TopRowRelation targetTop_0070 relationCoefficients_0070 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0070, relationCoefficients_0070, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0070 : BottomDetBound targetTop_0070 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0070

theorem canonicalBound_0070 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 3)) 9 := by
  have htop : targetTop_0070 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0070

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 3, 4)`. -/
def targetTop_0071 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0071 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0071 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0071 : BottomDetBound targetTop_0071 9 := by
  have hU : rowTransform_0071.det.natAbs = 1 := by
    have hdet : rowTransform_0071.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0071 hU
  have hcols := hrows.permuteColumns columnPerm_0071
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0071 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0071 = targetTop_0071 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0071 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 4)) 9 := by
  have htop : targetTop_0071 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0071

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 3, 5)`. -/
def targetTop_0072 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0072 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0072 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0072 : BottomDetBound targetTop_0072 9 := by
  have hU : rowTransform_0072.det.natAbs = 1 := by
    have hdet : rowTransform_0072.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0072 hU
  have hcols := hrows.permuteColumns columnPerm_0072
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0072 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0072 = targetTop_0072 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0072 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 5)) 9 := by
  have htop : targetTop_0072 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0072

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 3, 6)`. -/
def targetTop_0073 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0073 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0073 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0073 : BottomDetBound targetTop_0073 9 := by
  have hU : rowTransform_0073.det.natAbs = 1 := by
    have hdet : rowTransform_0073.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0073 hU
  have hcols := hrows.permuteColumns columnPerm_0073
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0073 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0073 = targetTop_0073 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0073 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 6)) 9 := by
  have htop : targetTop_0073 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0073

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 3, 7)`. -/
def targetTop_0074 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0074 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0074 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0074 : BottomDetBound targetTop_0074 9 := by
  have hU : rowTransform_0074.det.natAbs = 1 := by
    have hdet : rowTransform_0074.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0074 hU
  have hcols := hrows.permuteColumns columnPerm_0074
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0074 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0074 = targetTop_0074 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0074 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 3 7)) 9 := by
  have htop : targetTop_0074 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0074

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 4, 4)`. -/
def targetTop_0075 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0075 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0075 :
    TopRowRelation targetTop_0075 relationCoefficients_0075 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0075, relationCoefficients_0075, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0075 : BottomDetBound targetTop_0075 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0075

theorem canonicalBound_0075 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 4)) 9 := by
  have htop : targetTop_0075 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0075

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 4, 5)`. -/
def targetTop_0076 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0076 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0076 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0076 : BottomDetBound targetTop_0076 9 := by
  have hU : rowTransform_0076.det.natAbs = 1 := by
    have hdet : rowTransform_0076.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0076 hU
  have hcols := hrows.permuteColumns columnPerm_0076
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0076 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0076 = targetTop_0076 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0076 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 5)) 9 := by
  have htop : targetTop_0076 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0076

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 4, 6)`. -/
def targetTop_0077 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0077 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0077 :
    TopRowRelation targetTop_0077 relationCoefficients_0077 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0077, relationCoefficients_0077, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0077 : BottomDetBound targetTop_0077 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0077

theorem canonicalBound_0077 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 6)) 9 := by
  have htop : targetTop_0077 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0077

/-- Explicit target top block for canonical pattern `(0, 0, 0, 2, 4, 7)`. -/
def targetTop_0078 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0078 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0078 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0078 : BottomDetBound targetTop_0078 9 := by
  have hU : rowTransform_0078.det.natAbs = 1 := by
    have hdet : rowTransform_0078.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0078 hU
  have hcols := hrows.permuteColumns columnPerm_0078
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0078 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0078 = targetTop_0078 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0078 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 7)) 9 := by
  have htop : targetTop_0078 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0078

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 2, 5, 5)`. -/
def targetTop_0079 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0079 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0079 :
    TopRowRelation targetTop_0079 relationCoefficients_0079 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0079, relationCoefficients_0079, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0079 : BottomDetBound targetTop_0079 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0079

theorem canonicalBound_0079 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 5 5)) 9 := by
  have htop : targetTop_0079 =
      topOfPattern (R := ℤ) (angle6 0 0 0 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0079

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004
