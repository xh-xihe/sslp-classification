-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 4, 4, 4)`. -/
def targetTop_0240 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0240 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0240 :
    TopRowRelation targetTop_0240 relationCoefficients_0240 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0240, relationCoefficients_0240, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0240 : BottomDetBound targetTop_0240 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0240

theorem canonicalBound_0240 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 4 4)) 9 := by
  have htop : targetTop_0240 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0240

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 4, 5)`. -/
def targetTop_0241 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0241 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0241 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0241 : BottomDetBound targetTop_0241 9 := by
  have hU : rowTransform_0241.det.natAbs = 1 := by
    have hdet : rowTransform_0241.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0241 hU
  have hcols := hrows.permuteColumns columnPerm_0241
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0241 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0241 = targetTop_0241 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0241 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 4 5)) 9 := by
  have htop : targetTop_0241 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0241

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 4, 4, 6)`. -/
def targetTop_0242 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0242 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0242 :
    TopRowRelation targetTop_0242 relationCoefficients_0242 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0242, relationCoefficients_0242, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0242 : BottomDetBound targetTop_0242 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0242

theorem canonicalBound_0242 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 4 6)) 9 := by
  have htop : targetTop_0242 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0242

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 4, 7)`. -/
def targetTop_0243 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0243 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0243 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0243 : BottomDetBound targetTop_0243 9 := by
  have hU : rowTransform_0243.det.natAbs = 1 := by
    have hdet : rowTransform_0243.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0243 hU
  have hcols := hrows.permuteColumns columnPerm_0243
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0243 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0243 = targetTop_0243 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0243 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 4 7)) 9 := by
  have htop : targetTop_0243 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0243

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 5, 5)`. -/
def targetTop_0244 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0244 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     1, 0, 1]

def columnPerm_0244 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0244 : BottomDetBound targetTop_0244 9 := by
  have hU : rowTransform_0244.det.natAbs = 1 := by
    have hdet : rowTransform_0244.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0244 hU
  have hcols := hrows.permuteColumns columnPerm_0244
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0244 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0244 = targetTop_0244 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0244 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 5 5)) 9 := by
  have htop : targetTop_0244 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0244

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 5, 6)`. -/
def targetTop_0245 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0245 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0245 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0245 : BottomDetBound targetTop_0245 9 := by
  have hU : rowTransform_0245.det.natAbs = 1 := by
    have hdet : rowTransform_0245.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0245 hU
  have hcols := hrows.permuteColumns columnPerm_0245
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0245 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0245 = targetTop_0245 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0245 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 5 6)) 9 := by
  have htop : targetTop_0245 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0245

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 5, 7)`. -/
def targetTop_0246 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0246 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 1, 1]

def columnPerm_0246 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0246 : BottomDetBound targetTop_0246 9 := by
  have hU : rowTransform_0246.det.natAbs = 1 := by
    have hdet : rowTransform_0246.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0246 hU
  have hcols := hrows.permuteColumns columnPerm_0246
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0246 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0246 = targetTop_0246 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0246 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 5 7)) 9 := by
  have htop : targetTop_0246 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0246

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 4, 6, 6)`. -/
def targetTop_0247 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0247 : Fin 3 → ℤ :=
  ![1, 0, 0]

theorem topRelation_0247 :
    TopRowRelation targetTop_0247 relationCoefficients_0247 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0247, relationCoefficients_0247, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0247 : BottomDetBound targetTop_0247 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0247

theorem canonicalBound_0247 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 6 6)) 9 := by
  have htop : targetTop_0247 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0247

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 6, 7)`. -/
def targetTop_0248 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0248 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0248 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0248 : BottomDetBound targetTop_0248 9 := by
  have hU : rowTransform_0248.det.natAbs = 1 := by
    have hdet : rowTransform_0248.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0248 hU
  have hcols := hrows.permuteColumns columnPerm_0248
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0248 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0248 = targetTop_0248 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0248 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 6 7)) 9 := by
  have htop : targetTop_0248 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0248

/-- Explicit target top block for canonical pattern `(0, 0, 2, 4, 7, 7)`. -/
def targetTop_0249 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0249 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0249 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0249 : BottomDetBound targetTop_0249 9 := by
  have hU : rowTransform_0249.det.natAbs = 1 := by
    have hdet : rowTransform_0249.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0249 hU
  have hcols := hrows.permuteColumns columnPerm_0249
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0249 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0249 = targetTop_0249 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0249 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 7 7)) 9 := by
  have htop : targetTop_0249 =
      topOfPattern (R := ℤ) (angle6 0 0 2 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0249

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 5, 5, 5)`. -/
def targetTop_0250 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0250 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0250 :
    TopRowRelation targetTop_0250 relationCoefficients_0250 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0250, relationCoefficients_0250, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0250 : BottomDetBound targetTop_0250 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0250

theorem canonicalBound_0250 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 5 5)) 9 := by
  have htop : targetTop_0250 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0250

/-- Explicit target top block for canonical pattern `(0, 0, 2, 5, 5, 6)`. -/
def targetTop_0251 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 0;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0251 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     1, 0, 1]

def columnPerm_0251 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0251 : BottomDetBound targetTop_0251 9 := by
  have hU : rowTransform_0251.det.natAbs = 1 := by
    have hdet : rowTransform_0251.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0251 hU
  have hcols := hrows.permuteColumns columnPerm_0251
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0251 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0251 = targetTop_0251 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0251 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 5 6)) 9 := by
  have htop : targetTop_0251 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0251

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 5, 5, 7)`. -/
def targetTop_0252 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0252 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0252 :
    TopRowRelation targetTop_0252 relationCoefficients_0252 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0252, relationCoefficients_0252, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0252 : BottomDetBound targetTop_0252 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0252

theorem canonicalBound_0252 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 5 7)) 9 := by
  have htop : targetTop_0252 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0252

/-- Explicit target top block for canonical pattern `(0, 0, 2, 5, 6, 6)`. -/
def targetTop_0253 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0253 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 1, 0;
     1, 0, 1]

def columnPerm_0253 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0253 : BottomDetBound targetTop_0253 9 := by
  have hU : rowTransform_0253.det.natAbs = 1 := by
    have hdet : rowTransform_0253.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Aggregate.bottomBound.transformTopRows rowTransform_0253 hU
  have hcols := hrows.permuteColumns columnPerm_0253
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0253 MainTheory.Generated.BinaryBetaSixKernel.Representative.R002.Base.explicitTop)
          columnPerm_0253 = targetTop_0253 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0253 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 6 6)) 9 := by
  have htop : targetTop_0253 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0253

/-- Explicit target top block for canonical pattern `(0, 0, 2, 5, 6, 7)`. -/
def targetTop_0254 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 0, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0254 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 1, 1]

def columnPerm_0254 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0254 : BottomDetBound targetTop_0254 9 := by
  have hU : rowTransform_0254.det.natAbs = 1 := by
    have hdet : rowTransform_0254.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Aggregate.bottomBound.transformTopRows rowTransform_0254 hU
  have hcols := hrows.permuteColumns columnPerm_0254
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0254 MainTheory.Generated.BinaryBetaSixKernel.Representative.R003.Base.explicitTop)
          columnPerm_0254 = targetTop_0254 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0254 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 6 7)) 9 := by
  have htop : targetTop_0254 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0254

/-- Explicit rank-deficient target for canonical pattern `(0, 0, 2, 5, 7, 7)`. -/
def targetTop_0255 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0255 : Fin 3 → ℤ :=
  ![1, 0, (-1)]

theorem topRelation_0255 :
    TopRowRelation targetTop_0255 relationCoefficients_0255 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0255, relationCoefficients_0255, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0255 : BottomDetBound targetTop_0255 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0255

theorem canonicalBound_0255 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 7 7)) 9 := by
  have htop : targetTop_0255 =
      topOfPattern (R := ℤ) (angle6 0 0 2 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0255

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015
