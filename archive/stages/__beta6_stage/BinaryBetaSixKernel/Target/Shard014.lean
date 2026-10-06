-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 2, 7, 7)`. -/
def targetTop_0224 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0224 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0224 :
    TopRowRelation targetTop_0224 relationCoefficients_0224 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0224, relationCoefficients_0224, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0224 : BottomDetBound targetTop_0224 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0224

theorem canonicalBound_0224 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 7 7)) 9 := by
  have htop : targetTop_0224 =
      topOfPattern (R := ℤ) (angle6 0 0 2 2 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0224

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 3, 3, 3)`. -/
def targetTop_0225 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0225 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0225 :
    TopRowRelation targetTop_0225 relationCoefficients_0225 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0225, relationCoefficients_0225, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0225 : BottomDetBound targetTop_0225 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0225

theorem canonicalBound_0225 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 3)) 9 := by
  have htop : targetTop_0225 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0225

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 3, 4)`. -/
def targetTop_0226 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0226 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0226 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0226 : BottomDetBound targetTop_0226 9 := by
  have hU : rowTransform_0226.det.natAbs = 1 := by
    have hdet : rowTransform_0226.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0226 hU
  have hcols := hrows.permuteColumns columnPerm_0226
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0226 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0226 = targetTop_0226 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0226 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 4)) 9 := by
  have htop : targetTop_0226 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0226

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 3, 5)`. -/
def targetTop_0227 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0227 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0227 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0227 : BottomDetBound targetTop_0227 9 := by
  have hU : rowTransform_0227.det.natAbs = 1 := by
    have hdet : rowTransform_0227.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0227 hU
  have hcols := hrows.permuteColumns columnPerm_0227
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0227 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0227 = targetTop_0227 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0227 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 5)) 9 := by
  have htop : targetTop_0227 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0227

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 3, 6)`. -/
def targetTop_0228 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0228 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0228 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0228 : BottomDetBound targetTop_0228 9 := by
  have hU : rowTransform_0228.det.natAbs = 1 := by
    have hdet : rowTransform_0228.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0228 hU
  have hcols := hrows.permuteColumns columnPerm_0228
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0228 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0228 = targetTop_0228 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0228 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 6)) 9 := by
  have htop : targetTop_0228 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0228

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 3, 7)`. -/
def targetTop_0229 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0229 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     0, 0, 1]

def columnPerm_0229 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0229 : BottomDetBound targetTop_0229 9 := by
  have hU : rowTransform_0229.det.natAbs = 1 := by
    have hdet : rowTransform_0229.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0229 hU
  have hcols := hrows.permuteColumns columnPerm_0229
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0229 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0229 = targetTop_0229 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0229 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 7)) 9 := by
  have htop : targetTop_0229 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0229

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 4, 4)`. -/
def targetTop_0230 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0230 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0230 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0230 : BottomDetBound targetTop_0230 9 := by
  have hU : rowTransform_0230.det.natAbs = 1 := by
    have hdet : rowTransform_0230.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0230 hU
  have hcols := hrows.permuteColumns columnPerm_0230
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0230 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0230 = targetTop_0230 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0230 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 4 4)) 9 := by
  have htop : targetTop_0230 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0230

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 4, 5)`. -/
def targetTop_0231 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0231 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, (-1);
     0, 0, 1]

def columnPerm_0231 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0231 : BottomDetBound targetTop_0231 9 := by
  have hU : rowTransform_0231.det.natAbs = 1 := by
    have hdet : rowTransform_0231.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0231 hU
  have hcols := hrows.permuteColumns columnPerm_0231
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0231 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0231 = targetTop_0231 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0231 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 4 5)) 9 := by
  have htop : targetTop_0231 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0231

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 4, 6)`. -/
def targetTop_0232 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0232 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0232 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0232 : BottomDetBound targetTop_0232 9 := by
  have hU : rowTransform_0232.det.natAbs = 1 := by
    have hdet : rowTransform_0232.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0232 hU
  have hcols := hrows.permuteColumns columnPerm_0232
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0232 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0232 = targetTop_0232 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0232 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 4 6)) 9 := by
  have htop : targetTop_0232 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0232

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 4, 7)`. -/
def targetTop_0233 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0233 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0233 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0233 : BottomDetBound targetTop_0233 9 := by
  have hU : rowTransform_0233.det.natAbs = 1 := by
    have hdet : rowTransform_0233.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0233 hU
  have hcols := hrows.permuteColumns columnPerm_0233
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0233 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0233 = targetTop_0233 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0233 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 4 7)) 9 := by
  have htop : targetTop_0233 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0233

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 5, 5)`. -/
def targetTop_0234 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0234 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     1, 0, 0]

def columnPerm_0234 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0234 : BottomDetBound targetTop_0234 9 := by
  have hU : rowTransform_0234.det.natAbs = 1 := by
    have hdet : rowTransform_0234.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0234 hU
  have hcols := hrows.permuteColumns columnPerm_0234
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0234 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0234 = targetTop_0234 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0234 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 5 5)) 9 := by
  have htop : targetTop_0234 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0234

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 5, 6)`. -/
def targetTop_0235 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0235 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0235 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0235 : BottomDetBound targetTop_0235 9 := by
  have hU : rowTransform_0235.det.natAbs = 1 := by
    have hdet : rowTransform_0235.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Aggregate.bottomBound.transformTopRows rowTransform_0235 hU
  have hcols := hrows.permuteColumns columnPerm_0235
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0235 MainTheory.Generated.BinaryBetaSixKernel.Representative.R006.Base.explicitTop)
          columnPerm_0235 = targetTop_0235 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0235 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 5 6)) 9 := by
  have htop : targetTop_0235 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0235

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 5, 7)`. -/
def targetTop_0236 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0236 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 1, 0]

def columnPerm_0236 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0236 : BottomDetBound targetTop_0236 9 := by
  have hU : rowTransform_0236.det.natAbs = 1 := by
    have hdet : rowTransform_0236.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0236 hU
  have hcols := hrows.permuteColumns columnPerm_0236
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0236 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0236 = targetTop_0236 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0236 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 5 7)) 9 := by
  have htop : targetTop_0236 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0236

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 6, 6)`. -/
def targetTop_0237 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0237 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_0237 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0237 : BottomDetBound targetTop_0237 9 := by
  have hU : rowTransform_0237.det.natAbs = 1 := by
    have hdet : rowTransform_0237.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0237 hU
  have hcols := hrows.permuteColumns columnPerm_0237
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0237 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0237 = targetTop_0237 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0237 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 6 6)) 9 := by
  have htop : targetTop_0237 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0237

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 6, 7)`. -/
def targetTop_0238 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0238 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 1, 0;
     0, 0, 1]

def columnPerm_0238 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0238 : BottomDetBound targetTop_0238 9 := by
  have hU : rowTransform_0238.det.natAbs = 1 := by
    have hdet : rowTransform_0238.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Aggregate.bottomBound.transformTopRows rowTransform_0238 hU
  have hcols := hrows.permuteColumns columnPerm_0238
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0238 MainTheory.Generated.BinaryBetaSixKernel.Representative.R005.Base.explicitTop)
          columnPerm_0238 = targetTop_0238 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0238 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 6 7)) 9 := by
  have htop : targetTop_0238 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0238

/-- Explicit target top block for canonical pattern `(0, 0, 2, 3, 7, 7)`. -/
def targetTop_0239 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0239 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     1, 1, 1;
     1, 0, 0]

def columnPerm_0239 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0239 : BottomDetBound targetTop_0239 9 := by
  have hU : rowTransform_0239.det.natAbs = 1 := by
    have hdet : rowTransform_0239.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0239 hU
  have hcols := hrows.permuteColumns columnPerm_0239
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0239 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0239 = targetTop_0239 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0239 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 7 7)) 9 := by
  have htop : targetTop_0239 =
      topOfPattern (R := ℤ) (angle6 0 0 2 3 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0239

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014
