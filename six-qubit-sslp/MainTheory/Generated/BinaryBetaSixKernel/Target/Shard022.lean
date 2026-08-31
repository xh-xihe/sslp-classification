-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 5, 5)`. -/
def targetTop_0352 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0352 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0352 :
    TopRowRelation targetTop_0352 relationCoefficients_0352 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0352, relationCoefficients_0352, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0352 : BottomDetBound targetTop_0352 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0352

theorem canonicalBound_0352 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 5 5)) 9 := by
  have htop : targetTop_0352 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0352

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 5, 6)`. -/
def targetTop_0353 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0353 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0353 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0353 : BottomDetBound targetTop_0353 9 := by
  have hU : rowTransform_0353.det.natAbs = 1 := by
    have hdet : rowTransform_0353.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0353 hU
  have hcols := hrows.permuteColumns columnPerm_0353
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0353 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0353 = targetTop_0353 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0353 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 5 6)) 9 := by
  have htop : targetTop_0353 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0353

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 5, 7)`. -/
def targetTop_0354 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0354 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0354 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0354 : BottomDetBound targetTop_0354 9 := by
  have hU : rowTransform_0354.det.natAbs = 1 := by
    have hdet : rowTransform_0354.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0354 hU
  have hcols := hrows.permuteColumns columnPerm_0354
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0354 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0354 = targetTop_0354 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0354 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 5 7)) 9 := by
  have htop : targetTop_0354 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0354

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 6, 6)`. -/
def targetTop_0355 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0355 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0355 :
    TopRowRelation targetTop_0355 relationCoefficients_0355 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0355, relationCoefficients_0355, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0355 : BottomDetBound targetTop_0355 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0355

theorem canonicalBound_0355 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 6 6)) 9 := by
  have htop : targetTop_0355 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0355

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 6, 7)`. -/
def targetTop_0356 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0356 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0356 :
    TopRowRelation targetTop_0356 relationCoefficients_0356 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0356, relationCoefficients_0356, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0356 : BottomDetBound targetTop_0356 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0356

theorem canonicalBound_0356 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 6 7)) 9 := by
  have htop : targetTop_0356 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0356

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 7, 7)`. -/
def targetTop_0357 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0357 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0357 :
    TopRowRelation targetTop_0357 relationCoefficients_0357 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0357, relationCoefficients_0357, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0357 : BottomDetBound targetTop_0357 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0357

theorem canonicalBound_0357 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 7 7)) 9 := by
  have htop : targetTop_0357 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0357

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 2, 2, 2)`. -/
def targetTop_0358 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0358 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0358 :
    TopRowRelation targetTop_0358 relationCoefficients_0358 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0358, relationCoefficients_0358, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0358 : BottomDetBound targetTop_0358 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0358

theorem canonicalBound_0358 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 2)) 9 := by
  have htop : targetTop_0358 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0358

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 2, 2, 3)`. -/
def targetTop_0359 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0359 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0359 :
    TopRowRelation targetTop_0359 relationCoefficients_0359 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0359, relationCoefficients_0359, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0359 : BottomDetBound targetTop_0359 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0359

theorem canonicalBound_0359 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 3)) 9 := by
  have htop : targetTop_0359 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0359

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 2, 4)`. -/
def targetTop_0360 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0360 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0360 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0360 : BottomDetBound targetTop_0360 9 := by
  have hU : rowTransform_0360.det.natAbs = 1 := by
    have hdet : rowTransform_0360.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0360 hU
  have hcols := hrows.permuteColumns columnPerm_0360
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0360 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0360 = targetTop_0360 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0360 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 4)) 9 := by
  have htop : targetTop_0360 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0360

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 2, 5)`. -/
def targetTop_0361 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0361 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0361 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0361 : BottomDetBound targetTop_0361 9 := by
  have hU : rowTransform_0361.det.natAbs = 1 := by
    have hdet : rowTransform_0361.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0361 hU
  have hcols := hrows.permuteColumns columnPerm_0361
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0361 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0361 = targetTop_0361 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0361 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 5)) 9 := by
  have htop : targetTop_0361 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0361

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 2, 6)`. -/
def targetTop_0362 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0362 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0362 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0362 : BottomDetBound targetTop_0362 9 := by
  have hU : rowTransform_0362.det.natAbs = 1 := by
    have hdet : rowTransform_0362.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0362 hU
  have hcols := hrows.permuteColumns columnPerm_0362
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0362 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0362 = targetTop_0362 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0362 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 6)) 9 := by
  have htop : targetTop_0362 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0362

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 2, 7)`. -/
def targetTop_0363 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0363 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0363 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0363 : BottomDetBound targetTop_0363 9 := by
  have hU : rowTransform_0363.det.natAbs = 1 := by
    have hdet : rowTransform_0363.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0363 hU
  have hcols := hrows.permuteColumns columnPerm_0363
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0363 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0363 = targetTop_0363 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0363 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 7)) 9 := by
  have htop : targetTop_0363 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0363

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 2, 3, 3)`. -/
def targetTop_0364 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0364 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0364 :
    TopRowRelation targetTop_0364 relationCoefficients_0364 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0364, relationCoefficients_0364, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0364 : BottomDetBound targetTop_0364 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0364

theorem canonicalBound_0364 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 3)) 9 := by
  have htop : targetTop_0364 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0364

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 3, 4)`. -/
def targetTop_0365 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0365 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0365 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0365 : BottomDetBound targetTop_0365 9 := by
  have hU : rowTransform_0365.det.natAbs = 1 := by
    have hdet : rowTransform_0365.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0365 hU
  have hcols := hrows.permuteColumns columnPerm_0365
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0365 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0365 = targetTop_0365 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0365 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 4)) 9 := by
  have htop : targetTop_0365 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0365

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 3, 5)`. -/
def targetTop_0366 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0366 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0366 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0366 : BottomDetBound targetTop_0366 9 := by
  have hU : rowTransform_0366.det.natAbs = 1 := by
    have hdet : rowTransform_0366.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0366 hU
  have hcols := hrows.permuteColumns columnPerm_0366
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0366 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0366 = targetTop_0366 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0366 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 5)) 9 := by
  have htop : targetTop_0366 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0366

/-- Explicit target top block for canonical pattern `(0, 1, 1, 2, 3, 6)`. -/
def targetTop_0367 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0367 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0367 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0367 : BottomDetBound targetTop_0367 9 := by
  have hU : rowTransform_0367.det.natAbs = 1 := by
    have hdet : rowTransform_0367.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0367 hU
  have hcols := hrows.permuteColumns columnPerm_0367
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0367 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0367 = targetTop_0367 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0367 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 6)) 9 := by
  have htop : targetTop_0367 =
      topOfPattern (R := ℤ) (angle6 0 1 1 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0367

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022
