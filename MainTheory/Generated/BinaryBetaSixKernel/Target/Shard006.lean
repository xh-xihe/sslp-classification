-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 0, 3, 5, 7)`. -/
def targetTop_0096 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0096 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0096 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0096 : BottomDetBound targetTop_0096 9 := by
  have hU : rowTransform_0096.det.natAbs = 1 := by
    have hdet : rowTransform_0096.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0096 hU
  have hcols := hrows.permuteColumns columnPerm_0096
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0096 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0096 = targetTop_0096 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0096 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 5 7)) 9 := by
  have htop : targetTop_0096 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0096

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 6, 6)`. -/
def targetTop_0097 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0097 : Fin 3 → ℤ :=
  ![1, (-1), 1]

theorem topRelation_0097 :
    TopRowRelation targetTop_0097 relationCoefficients_0097 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0097, relationCoefficients_0097, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0097 : BottomDetBound targetTop_0097 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0097

theorem canonicalBound_0097 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 6 6)) 9 := by
  have htop : targetTop_0097 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0097

/-- Explicit target top block for canonical pattern `(0, 0, 0, 3, 6, 7)`. -/
def targetTop_0098 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0098 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 1, 1]

def columnPerm_0098 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0098 : BottomDetBound targetTop_0098 9 := by
  have hU : rowTransform_0098.det.natAbs = 1 := by
    have hdet : rowTransform_0098.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0098 hU
  have hcols := hrows.permuteColumns columnPerm_0098
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0098 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0098 = targetTop_0098 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0098 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 6 7)) 9 := by
  have htop : targetTop_0098 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0098

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 3, 7, 7)`. -/
def targetTop_0099 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0099 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0099 :
    TopRowRelation targetTop_0099 relationCoefficients_0099 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0099, relationCoefficients_0099, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0099 : BottomDetBound targetTop_0099 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0099

theorem canonicalBound_0099 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 7 7)) 9 := by
  have htop : targetTop_0099 =
      topOfPattern (R := ℤ) (angle6 0 0 0 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0099

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 4, 4)`. -/
def targetTop_0100 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0100 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0100 :
    TopRowRelation targetTop_0100 relationCoefficients_0100 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0100, relationCoefficients_0100, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0100 : BottomDetBound targetTop_0100 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0100

theorem canonicalBound_0100 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 4 4)) 9 := by
  have htop : targetTop_0100 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0100

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 4, 5)`. -/
def targetTop_0101 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0101 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0101 :
    TopRowRelation targetTop_0101 relationCoefficients_0101 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0101, relationCoefficients_0101, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0101 : BottomDetBound targetTop_0101 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0101

theorem canonicalBound_0101 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 4 5)) 9 := by
  have htop : targetTop_0101 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0101

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 4, 6)`. -/
def targetTop_0102 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0102 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0102 :
    TopRowRelation targetTop_0102 relationCoefficients_0102 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0102, relationCoefficients_0102, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0102 : BottomDetBound targetTop_0102 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0102

theorem canonicalBound_0102 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 4 6)) 9 := by
  have htop : targetTop_0102 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0102

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 4, 7)`. -/
def targetTop_0103 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0103 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0103 :
    TopRowRelation targetTop_0103 relationCoefficients_0103 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0103, relationCoefficients_0103, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0103 : BottomDetBound targetTop_0103 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0103

theorem canonicalBound_0103 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 4 7)) 9 := by
  have htop : targetTop_0103 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0103

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 5, 5)`. -/
def targetTop_0104 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0104 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0104 :
    TopRowRelation targetTop_0104 relationCoefficients_0104 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0104, relationCoefficients_0104, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0104 : BottomDetBound targetTop_0104 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0104

theorem canonicalBound_0104 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 5 5)) 9 := by
  have htop : targetTop_0104 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0104

/-- Explicit target top block for canonical pattern `(0, 0, 0, 4, 5, 6)`. -/
def targetTop_0105 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0105 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0105 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0105 : BottomDetBound targetTop_0105 9 := by
  have hU : rowTransform_0105.det.natAbs = 1 := by
    have hdet : rowTransform_0105.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0105 hU
  have hcols := hrows.permuteColumns columnPerm_0105
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0105 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0105 = targetTop_0105 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0105 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 5 6)) 9 := by
  have htop : targetTop_0105 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0105

/-- Explicit target top block for canonical pattern `(0, 0, 0, 4, 5, 7)`. -/
def targetTop_0106 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0106 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 1, 1]

def columnPerm_0106 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0106 : BottomDetBound targetTop_0106 9 := by
  have hU : rowTransform_0106.det.natAbs = 1 := by
    have hdet : rowTransform_0106.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0106 hU
  have hcols := hrows.permuteColumns columnPerm_0106
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0106 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0106 = targetTop_0106 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0106 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 5 7)) 9 := by
  have htop : targetTop_0106 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0106

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 6, 6)`. -/
def targetTop_0107 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0107 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0107 :
    TopRowRelation targetTop_0107 relationCoefficients_0107 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0107, relationCoefficients_0107, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0107 : BottomDetBound targetTop_0107 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0107

theorem canonicalBound_0107 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 6 6)) 9 := by
  have htop : targetTop_0107 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0107

/-- Explicit target top block for canonical pattern `(0, 0, 0, 4, 6, 7)`. -/
def targetTop_0108 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0108 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 1, 1]

def columnPerm_0108 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0108 : BottomDetBound targetTop_0108 9 := by
  have hU : rowTransform_0108.det.natAbs = 1 := by
    have hdet : rowTransform_0108.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Aggregate.bottomBound.transformTopRows rowTransform_0108 hU
  have hcols := hrows.permuteColumns columnPerm_0108
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0108 MainTheory.Generated.BinaryBetaSixKernel.Representative.R000.Base.explicitTop)
          columnPerm_0108 = targetTop_0108 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0108 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 6 7)) 9 := by
  have htop : targetTop_0108 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0108

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 4, 7, 7)`. -/
def targetTop_0109 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0109 : Fin 3 → ℤ :=
  ![1, (-1), 0]

theorem topRelation_0109 :
    TopRowRelation targetTop_0109 relationCoefficients_0109 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0109, relationCoefficients_0109, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0109 : BottomDetBound targetTop_0109 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0109

theorem canonicalBound_0109 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 7 7)) 9 := by
  have htop : targetTop_0109 =
      topOfPattern (R := ℤ) (angle6 0 0 0 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0109

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 5, 5, 5)`. -/
def targetTop_0110 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0110 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0110 :
    TopRowRelation targetTop_0110 relationCoefficients_0110 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0110, relationCoefficients_0110, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0110 : BottomDetBound targetTop_0110 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0110

theorem canonicalBound_0110 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 5 5)) 9 := by
  have htop : targetTop_0110 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0110

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 0, 5, 5, 6)`. -/
def targetTop_0111 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0111 : Fin 3 → ℤ :=
  ![1, 1, (-1)]

theorem topRelation_0111 :
    TopRowRelation targetTop_0111 relationCoefficients_0111 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0111, relationCoefficients_0111, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0111 : BottomDetBound targetTop_0111 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0111

theorem canonicalBound_0111 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 5 6)) 9 := by
  have htop : targetTop_0111 =
      topOfPattern (R := ℤ) (angle6 0 0 0 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0111

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006
