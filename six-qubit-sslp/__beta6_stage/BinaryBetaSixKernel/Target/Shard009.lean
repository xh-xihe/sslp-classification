-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 1, 1, 5, 7)`. -/
def targetTop_0144 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0144 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0144 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0144 : BottomDetBound targetTop_0144 9 := by
  have hU : rowTransform_0144.det.natAbs = 1 := by
    have hdet : rowTransform_0144.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0144 hU
  have hcols := hrows.permuteColumns columnPerm_0144
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0144 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0144 = targetTop_0144 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0144 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 5 7)) 9 := by
  have htop : targetTop_0144 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0144

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 6, 6)`. -/
def targetTop_0145 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0145 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0145 :
    TopRowRelation targetTop_0145 relationCoefficients_0145 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0145, relationCoefficients_0145, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0145 : BottomDetBound targetTop_0145 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0145

theorem canonicalBound_0145 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 6 6)) 9 := by
  have htop : targetTop_0145 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0145

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 6, 7)`. -/
def targetTop_0146 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0146 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0146 :
    TopRowRelation targetTop_0146 relationCoefficients_0146 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0146, relationCoefficients_0146, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0146 : BottomDetBound targetTop_0146 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0146

theorem canonicalBound_0146 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 6 7)) 9 := by
  have htop : targetTop_0146 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0146

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 1, 7, 7)`. -/
def targetTop_0147 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0147 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0147 :
    TopRowRelation targetTop_0147 relationCoefficients_0147 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0147, relationCoefficients_0147, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0147 : BottomDetBound targetTop_0147 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0147

theorem canonicalBound_0147 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 7 7)) 9 := by
  have htop : targetTop_0147 =
      topOfPattern (R := ℤ) (angle6 0 0 1 1 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0147

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 2, 2, 2)`. -/
def targetTop_0148 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0148 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0148 :
    TopRowRelation targetTop_0148 relationCoefficients_0148 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0148, relationCoefficients_0148, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0148 : BottomDetBound targetTop_0148 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0148

theorem canonicalBound_0148 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 2)) 9 := by
  have htop : targetTop_0148 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0148

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 2, 2, 3)`. -/
def targetTop_0149 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0149 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0149 :
    TopRowRelation targetTop_0149 relationCoefficients_0149 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0149, relationCoefficients_0149, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0149 : BottomDetBound targetTop_0149 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0149

theorem canonicalBound_0149 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 3)) 9 := by
  have htop : targetTop_0149 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0149

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 2, 4)`. -/
def targetTop_0150 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0150 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0150 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0150 : BottomDetBound targetTop_0150 9 := by
  have hU : rowTransform_0150.det.natAbs = 1 := by
    have hdet : rowTransform_0150.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0150 hU
  have hcols := hrows.permuteColumns columnPerm_0150
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0150 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0150 = targetTop_0150 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0150 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 4)) 9 := by
  have htop : targetTop_0150 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0150

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 2, 5)`. -/
def targetTop_0151 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0151 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0151 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0151 : BottomDetBound targetTop_0151 9 := by
  have hU : rowTransform_0151.det.natAbs = 1 := by
    have hdet : rowTransform_0151.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0151 hU
  have hcols := hrows.permuteColumns columnPerm_0151
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0151 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0151 = targetTop_0151 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0151 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 5)) 9 := by
  have htop : targetTop_0151 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0151

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 2, 6)`. -/
def targetTop_0152 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0152 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0152 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0152 : BottomDetBound targetTop_0152 9 := by
  have hU : rowTransform_0152.det.natAbs = 1 := by
    have hdet : rowTransform_0152.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0152 hU
  have hcols := hrows.permuteColumns columnPerm_0152
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0152 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0152 = targetTop_0152 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0152 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 6)) 9 := by
  have htop : targetTop_0152 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0152

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 2, 7)`. -/
def targetTop_0153 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0153 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0153 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0153 : BottomDetBound targetTop_0153 9 := by
  have hU : rowTransform_0153.det.natAbs = 1 := by
    have hdet : rowTransform_0153.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0153 hU
  have hcols := hrows.permuteColumns columnPerm_0153
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0153 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0153 = targetTop_0153 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0153 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 7)) 9 := by
  have htop : targetTop_0153 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0153

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 2, 3, 3)`. -/
def targetTop_0154 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0154 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0154 :
    TopRowRelation targetTop_0154 relationCoefficients_0154 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0154, relationCoefficients_0154, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0154 : BottomDetBound targetTop_0154 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0154

theorem canonicalBound_0154 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 3)) 9 := by
  have htop : targetTop_0154 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0154

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 3, 4)`. -/
def targetTop_0155 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0155 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0155 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0155 : BottomDetBound targetTop_0155 9 := by
  have hU : rowTransform_0155.det.natAbs = 1 := by
    have hdet : rowTransform_0155.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0155 hU
  have hcols := hrows.permuteColumns columnPerm_0155
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0155 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0155 = targetTop_0155 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0155 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 4)) 9 := by
  have htop : targetTop_0155 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0155

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 3, 5)`. -/
def targetTop_0156 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0156 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0156 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0156 : BottomDetBound targetTop_0156 9 := by
  have hU : rowTransform_0156.det.natAbs = 1 := by
    have hdet : rowTransform_0156.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0156 hU
  have hcols := hrows.permuteColumns columnPerm_0156
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0156 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0156 = targetTop_0156 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0156 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 5)) 9 := by
  have htop : targetTop_0156 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0156

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 3, 6)`. -/
def targetTop_0157 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0157 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0157 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0157 : BottomDetBound targetTop_0157 9 := by
  have hU : rowTransform_0157.det.natAbs = 1 := by
    have hdet : rowTransform_0157.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0157 hU
  have hcols := hrows.permuteColumns columnPerm_0157
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0157 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0157 = targetTop_0157 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0157 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 6)) 9 := by
  have htop : targetTop_0157 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0157

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 3, 7)`. -/
def targetTop_0158 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0158 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0158 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0158 : BottomDetBound targetTop_0158 9 := by
  have hU : rowTransform_0158.det.natAbs = 1 := by
    have hdet : rowTransform_0158.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0158 hU
  have hcols := hrows.permuteColumns columnPerm_0158
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0158 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0158 = targetTop_0158 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0158 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 3 7)) 9 := by
  have htop : targetTop_0158 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0158

/-- Explicit target top block for canonical pattern `(0, 0, 1, 2, 4, 4)`. -/
def targetTop_0159 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0159 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0159 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0159 : BottomDetBound targetTop_0159 9 := by
  have hU : rowTransform_0159.det.natAbs = 1 := by
    have hdet : rowTransform_0159.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0159 hU
  have hcols := hrows.permuteColumns columnPerm_0159
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0159 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0159 = targetTop_0159 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0159 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 4 4)) 9 := by
  have htop : targetTop_0159 =
      topOfPattern (R := ℤ) (angle6 0 0 1 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0159

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009
