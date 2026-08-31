-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 1, 7)`. -/
def targetTop_0336 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0336 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0336 :
    TopRowRelation targetTop_0336 relationCoefficients_0336 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0336, relationCoefficients_0336, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0336 : BottomDetBound targetTop_0336 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0336

theorem canonicalBound_0336 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 7)) 9 := by
  have htop : targetTop_0336 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 1 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0336

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 2, 2)`. -/
def targetTop_0337 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0337 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0337 :
    TopRowRelation targetTop_0337 relationCoefficients_0337 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0337, relationCoefficients_0337, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0337 : BottomDetBound targetTop_0337 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0337

theorem canonicalBound_0337 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 2)) 9 := by
  have htop : targetTop_0337 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0337

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 2, 3)`. -/
def targetTop_0338 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0338 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0338 :
    TopRowRelation targetTop_0338 relationCoefficients_0338 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0338, relationCoefficients_0338, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0338 : BottomDetBound targetTop_0338 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0338

theorem canonicalBound_0338 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 3)) 9 := by
  have htop : targetTop_0338 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0338

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 2, 4)`. -/
def targetTop_0339 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0339 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0339 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0339 : BottomDetBound targetTop_0339 9 := by
  have hU : rowTransform_0339.det.natAbs = 1 := by
    have hdet : rowTransform_0339.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0339 hU
  have hcols := hrows.permuteColumns columnPerm_0339
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0339 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0339 = targetTop_0339 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0339 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 4)) 9 := by
  have htop : targetTop_0339 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0339

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 2, 5)`. -/
def targetTop_0340 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0340 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0340 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0340 : BottomDetBound targetTop_0340 9 := by
  have hU : rowTransform_0340.det.natAbs = 1 := by
    have hdet : rowTransform_0340.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0340 hU
  have hcols := hrows.permuteColumns columnPerm_0340
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0340 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0340 = targetTop_0340 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0340 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 5)) 9 := by
  have htop : targetTop_0340 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0340

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 2, 6)`. -/
def targetTop_0341 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0341 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0341 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0341 : BottomDetBound targetTop_0341 9 := by
  have hU : rowTransform_0341.det.natAbs = 1 := by
    have hdet : rowTransform_0341.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0341 hU
  have hcols := hrows.permuteColumns columnPerm_0341
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0341 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0341 = targetTop_0341 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0341 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 6)) 9 := by
  have htop : targetTop_0341 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0341

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 2, 7)`. -/
def targetTop_0342 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0342 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0342 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0342 : BottomDetBound targetTop_0342 9 := by
  have hU : rowTransform_0342.det.natAbs = 1 := by
    have hdet : rowTransform_0342.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0342 hU
  have hcols := hrows.permuteColumns columnPerm_0342
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0342 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0342 = targetTop_0342 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0342 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 7)) 9 := by
  have htop : targetTop_0342 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0342

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 3, 3)`. -/
def targetTop_0343 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0343 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0343 :
    TopRowRelation targetTop_0343 relationCoefficients_0343 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0343, relationCoefficients_0343, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0343 : BottomDetBound targetTop_0343 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0343

theorem canonicalBound_0343 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 3)) 9 := by
  have htop : targetTop_0343 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0343

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 3, 4)`. -/
def targetTop_0344 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0344 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0344 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0344 : BottomDetBound targetTop_0344 9 := by
  have hU : rowTransform_0344.det.natAbs = 1 := by
    have hdet : rowTransform_0344.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0344 hU
  have hcols := hrows.permuteColumns columnPerm_0344
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0344 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0344 = targetTop_0344 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0344 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 4)) 9 := by
  have htop : targetTop_0344 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0344

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 3, 5)`. -/
def targetTop_0345 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0345 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 0, 1]

def columnPerm_0345 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0345 : BottomDetBound targetTop_0345 9 := by
  have hU : rowTransform_0345.det.natAbs = 1 := by
    have hdet : rowTransform_0345.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0345 hU
  have hcols := hrows.permuteColumns columnPerm_0345
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0345 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0345 = targetTop_0345 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0345 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 5)) 9 := by
  have htop : targetTop_0345 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0345

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 3, 6)`. -/
def targetTop_0346 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0346 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0346 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0346 : BottomDetBound targetTop_0346 9 := by
  have hU : rowTransform_0346.det.natAbs = 1 := by
    have hdet : rowTransform_0346.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0346 hU
  have hcols := hrows.permuteColumns columnPerm_0346
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0346 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0346 = targetTop_0346 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0346 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 6)) 9 := by
  have htop : targetTop_0346 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0346

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 3, 7)`. -/
def targetTop_0347 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0347 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 1;
     0, 0, 1]

def columnPerm_0347 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0347 : BottomDetBound targetTop_0347 9 := by
  have hU : rowTransform_0347.det.natAbs = 1 := by
    have hdet : rowTransform_0347.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0347 hU
  have hcols := hrows.permuteColumns columnPerm_0347
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0347 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0347 = targetTop_0347 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0347 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 7)) 9 := by
  have htop : targetTop_0347 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0347

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 4, 4)`. -/
def targetTop_0348 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0348 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0348 :
    TopRowRelation targetTop_0348 relationCoefficients_0348 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0348, relationCoefficients_0348, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0348 : BottomDetBound targetTop_0348 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0348

theorem canonicalBound_0348 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 4 4)) 9 := by
  have htop : targetTop_0348 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0348

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 1, 4, 5)`. -/
def targetTop_0349 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0349 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0349 :
    TopRowRelation targetTop_0349 relationCoefficients_0349 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0349, relationCoefficients_0349, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0349 : BottomDetBound targetTop_0349 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0349

theorem canonicalBound_0349 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 4 5)) 9 := by
  have htop : targetTop_0349 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0349

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 4, 6)`. -/
def targetTop_0350 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0350 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0350 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0350 : BottomDetBound targetTop_0350 9 := by
  have hU : rowTransform_0350.det.natAbs = 1 := by
    have hdet : rowTransform_0350.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0350 hU
  have hcols := hrows.permuteColumns columnPerm_0350
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0350 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0350 = targetTop_0350 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0350 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 4 6)) 9 := by
  have htop : targetTop_0350 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0350

/-- Explicit target top block for canonical pattern `(0, 1, 1, 1, 4, 7)`. -/
def targetTop_0351 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0351 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0351 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0351 : BottomDetBound targetTop_0351 9 := by
  have hU : rowTransform_0351.det.natAbs = 1 := by
    have hdet : rowTransform_0351.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0351 hU
  have hcols := hrows.permuteColumns columnPerm_0351
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0351 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0351 = targetTop_0351 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0351 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 4 7)) 9 := by
  have htop : targetTop_0351 =
      topOfPattern (R := ℤ) (angle6 0 1 1 1 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0351

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021
