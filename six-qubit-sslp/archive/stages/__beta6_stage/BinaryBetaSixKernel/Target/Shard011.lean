-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 4, 6)`. -/
def targetTop_0176 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0176 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, (-1);
     0, 1, 0;
     0, 0, 1]

def columnPerm_0176 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0176 : BottomDetBound targetTop_0176 9 := by
  have hU : rowTransform_0176.det.natAbs = 1 := by
    have hdet : rowTransform_0176.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0176 hU
  have hcols := hrows.permuteColumns columnPerm_0176
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0176 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0176 = targetTop_0176 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0176 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 6)) 9 := by
  have htop : targetTop_0176 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0176

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 4, 7)`. -/
def targetTop_0177 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0177 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0177 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0177 : BottomDetBound targetTop_0177 9 := by
  have hU : rowTransform_0177.det.natAbs = 1 := by
    have hdet : rowTransform_0177.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0177 hU
  have hcols := hrows.permuteColumns columnPerm_0177
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0177 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0177 = targetTop_0177 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0177 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 7)) 9 := by
  have htop : targetTop_0177 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0177

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 5, 5)`. -/
def targetTop_0178 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0178 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     1, 0, 0]

def columnPerm_0178 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0178 : BottomDetBound targetTop_0178 9 := by
  have hU : rowTransform_0178.det.natAbs = 1 := by
    have hdet : rowTransform_0178.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0178 hU
  have hcols := hrows.permuteColumns columnPerm_0178
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0178 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0178 = targetTop_0178 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0178 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 5 5)) 9 := by
  have htop : targetTop_0178 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0178

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 5, 6)`. -/
def targetTop_0179 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 0;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0179 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0179 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0179 : BottomDetBound targetTop_0179 9 := by
  have hU : rowTransform_0179.det.natAbs = 1 := by
    have hdet : rowTransform_0179.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate.bottomBound.transformTopRows rowTransform_0179 hU
  have hcols := hrows.permuteColumns columnPerm_0179
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0179 MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Base.explicitTop)
          columnPerm_0179 = targetTop_0179 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0179 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 5 6)) 9 := by
  have htop : targetTop_0179 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0179

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 5, 7)`. -/
def targetTop_0180 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0180 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0180 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0180 : BottomDetBound targetTop_0180 9 := by
  have hU : rowTransform_0180.det.natAbs = 1 := by
    have hdet : rowTransform_0180.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0180 hU
  have hcols := hrows.permuteColumns columnPerm_0180
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0180 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0180 = targetTop_0180 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0180 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 5 7)) 9 := by
  have htop : targetTop_0180 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0180

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 6, 6)`. -/
def targetTop_0181 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0181 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0181 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0181 : BottomDetBound targetTop_0181 9 := by
  have hU : rowTransform_0181.det.natAbs = 1 := by
    have hdet : rowTransform_0181.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0181 hU
  have hcols := hrows.permuteColumns columnPerm_0181
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0181 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0181 = targetTop_0181 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0181 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 6 6)) 9 := by
  have htop : targetTop_0181 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0181

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 6, 7)`. -/
def targetTop_0182 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0182 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 1, 0]

def columnPerm_0182 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0182 : BottomDetBound targetTop_0182 9 := by
  have hU : rowTransform_0182.det.natAbs = 1 := by
    have hdet : rowTransform_0182.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0182 hU
  have hcols := hrows.permuteColumns columnPerm_0182
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0182 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0182 = targetTop_0182 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0182 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 6 7)) 9 := by
  have htop : targetTop_0182 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0182

/-- Explicit target top block for canonical pattern `(0, 0, 1, 3, 7, 7)`. -/
def targetTop_0183 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0183 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     1, 0, 1;
     1, 0, 0]

def columnPerm_0183 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0183 : BottomDetBound targetTop_0183 9 := by
  have hU : rowTransform_0183.det.natAbs = 1 := by
    have hdet : rowTransform_0183.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0183 hU
  have hcols := hrows.permuteColumns columnPerm_0183
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0183 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0183 = targetTop_0183 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0183 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 7 7)) 9 := by
  have htop : targetTop_0183 =
      topOfPattern (R := ℤ) (angle6 0 0 1 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0183

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 4, 4, 4)`. -/
def targetTop_0184 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0184 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0184 :
    TopRowRelation targetTop_0184 relationCoefficients_0184 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0184, relationCoefficients_0184, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0184 : BottomDetBound targetTop_0184 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0184

theorem canonicalBound_0184 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 4 4)) 9 := by
  have htop : targetTop_0184 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0184

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 4, 4, 5)`. -/
def targetTop_0185 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0185 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0185 :
    TopRowRelation targetTop_0185 relationCoefficients_0185 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0185, relationCoefficients_0185, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0185 : BottomDetBound targetTop_0185 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0185

theorem canonicalBound_0185 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 4 5)) 9 := by
  have htop : targetTop_0185 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0185

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 4, 6)`. -/
def targetTop_0186 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0186 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0186 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0186 : BottomDetBound targetTop_0186 9 := by
  have hU : rowTransform_0186.det.natAbs = 1 := by
    have hdet : rowTransform_0186.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0186 hU
  have hcols := hrows.permuteColumns columnPerm_0186
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0186 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0186 = targetTop_0186 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0186 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 4 6)) 9 := by
  have htop : targetTop_0186 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0186

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 4, 7)`. -/
def targetTop_0187 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0187 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     0, 0, 1;
     1, 0, 1]

def columnPerm_0187 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0187 : BottomDetBound targetTop_0187 9 := by
  have hU : rowTransform_0187.det.natAbs = 1 := by
    have hdet : rowTransform_0187.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0187 hU
  have hcols := hrows.permuteColumns columnPerm_0187
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0187 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0187 = targetTop_0187 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0187 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 4 7)) 9 := by
  have htop : targetTop_0187 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0187

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 1, 4, 5, 5)`. -/
def targetTop_0188 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0188 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0188 :
    TopRowRelation targetTop_0188 relationCoefficients_0188 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0188, relationCoefficients_0188, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0188 : BottomDetBound targetTop_0188 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0188

theorem canonicalBound_0188 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 5 5)) 9 := by
  have htop : targetTop_0188 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0188

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 5, 6)`. -/
def targetTop_0189 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0189 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0189 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0189 : BottomDetBound targetTop_0189 9 := by
  have hU : rowTransform_0189.det.natAbs = 1 := by
    have hdet : rowTransform_0189.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0189 hU
  have hcols := hrows.permuteColumns columnPerm_0189
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0189 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0189 = targetTop_0189 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0189 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 5 6)) 9 := by
  have htop : targetTop_0189 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0189

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 5, 7)`. -/
def targetTop_0190 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0190 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0190 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0190 : BottomDetBound targetTop_0190 9 := by
  have hU : rowTransform_0190.det.natAbs = 1 := by
    have hdet : rowTransform_0190.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0190 hU
  have hcols := hrows.permuteColumns columnPerm_0190
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0190 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0190 = targetTop_0190 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0190 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 5 7)) 9 := by
  have htop : targetTop_0190 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0190

/-- Explicit target top block for canonical pattern `(0, 0, 1, 4, 6, 6)`. -/
def targetTop_0191 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0191 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     1, 0, 1]

def columnPerm_0191 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0191 : BottomDetBound targetTop_0191 9 := by
  have hU : rowTransform_0191.det.natAbs = 1 := by
    have hdet : rowTransform_0191.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0191 hU
  have hcols := hrows.permuteColumns columnPerm_0191
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0191 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0191 = targetTop_0191 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0191 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 6 6)) 9 := by
  have htop : targetTop_0191 =
      topOfPattern (R := ℤ) (angle6 0 0 1 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0191

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011
