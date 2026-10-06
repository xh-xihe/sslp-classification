-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 5, 7)`. -/
def targetTop_0400 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0400 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0400 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0400 : BottomDetBound targetTop_0400 9 := by
  have hU : rowTransform_0400.det.natAbs = 1 := by
    have hdet : rowTransform_0400.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0400 hU
  have hcols := hrows.permuteColumns columnPerm_0400
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0400 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0400 = targetTop_0400 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0400 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 5 7)) 9 := by
  have htop : targetTop_0400 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0400

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 6, 6)`. -/
def targetTop_0401 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0401 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0401 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0401 : BottomDetBound targetTop_0401 9 := by
  have hU : rowTransform_0401.det.natAbs = 1 := by
    have hdet : rowTransform_0401.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0401 hU
  have hcols := hrows.permuteColumns columnPerm_0401
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0401 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0401 = targetTop_0401 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0401 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 6 6)) 9 := by
  have htop : targetTop_0401 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0401

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 6, 7)`. -/
def targetTop_0402 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0402 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0402 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0402 : BottomDetBound targetTop_0402 9 := by
  have hU : rowTransform_0402.det.natAbs = 1 := by
    have hdet : rowTransform_0402.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0402 hU
  have hcols := hrows.permuteColumns columnPerm_0402
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0402 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0402 = targetTop_0402 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0402 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 6 7)) 9 := by
  have htop : targetTop_0402 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0402

/-- Explicit target top block for canonical pattern `(0, 1, 1, 4, 7, 7)`. -/
def targetTop_0403 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0403 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0403 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0403 : BottomDetBound targetTop_0403 9 := by
  have hU : rowTransform_0403.det.natAbs = 1 := by
    have hdet : rowTransform_0403.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0403 hU
  have hcols := hrows.permuteColumns columnPerm_0403
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0403 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0403 = targetTop_0403 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0403 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 7 7)) 9 := by
  have htop : targetTop_0403 =
      topOfPattern (R := ℤ) (angle6 0 1 1 4 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0403

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 5, 5, 5)`. -/
def targetTop_0404 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0404 : Fin 3 → ℤ :=
  ![0, 1, 0]

theorem topRelation_0404 :
    TopRowRelation targetTop_0404 relationCoefficients_0404 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0404, relationCoefficients_0404, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0404 : BottomDetBound targetTop_0404 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0404

theorem canonicalBound_0404 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 5 5)) 9 := by
  have htop : targetTop_0404 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0404

/-- Explicit target top block for canonical pattern `(0, 1, 1, 5, 5, 6)`. -/
def targetTop_0405 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0405 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 0;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0405 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0405 : BottomDetBound targetTop_0405 9 := by
  have hU : rowTransform_0405.det.natAbs = 1 := by
    have hdet : rowTransform_0405.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0405 hU
  have hcols := hrows.permuteColumns columnPerm_0405
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0405 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0405 = targetTop_0405 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0405 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 5 6)) 9 := by
  have htop : targetTop_0405 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0405

/-- Explicit target top block for canonical pattern `(0, 1, 1, 5, 5, 7)`. -/
def targetTop_0406 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0406 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 0, 1;
     0, 1, 1]

def columnPerm_0406 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0406 : BottomDetBound targetTop_0406 9 := by
  have hU : rowTransform_0406.det.natAbs = 1 := by
    have hdet : rowTransform_0406.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0406 hU
  have hcols := hrows.permuteColumns columnPerm_0406
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0406 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0406 = targetTop_0406 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0406 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 5 7)) 9 := by
  have htop : targetTop_0406 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0406

/-- Explicit target top block for canonical pattern `(0, 1, 1, 5, 6, 6)`. -/
def targetTop_0407 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0407 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0407 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0407 : BottomDetBound targetTop_0407 9 := by
  have hU : rowTransform_0407.det.natAbs = 1 := by
    have hdet : rowTransform_0407.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0407 hU
  have hcols := hrows.permuteColumns columnPerm_0407
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0407 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0407 = targetTop_0407 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0407 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 6 6)) 9 := by
  have htop : targetTop_0407 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0407

/-- Explicit target top block for canonical pattern `(0, 1, 1, 5, 6, 7)`. -/
def targetTop_0408 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0408 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0408 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0408 : BottomDetBound targetTop_0408 9 := by
  have hU : rowTransform_0408.det.natAbs = 1 := by
    have hdet : rowTransform_0408.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0408 hU
  have hcols := hrows.permuteColumns columnPerm_0408
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0408 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0408 = targetTop_0408 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0408 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 6 7)) 9 := by
  have htop : targetTop_0408 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0408

/-- Explicit target top block for canonical pattern `(0, 1, 1, 5, 7, 7)`. -/
def targetTop_0409 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0409 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1, 1;
     0, 1, 0;
     0, 1, 1]

def columnPerm_0409 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0409 : BottomDetBound targetTop_0409 9 := by
  have hU : rowTransform_0409.det.natAbs = 1 := by
    have hdet : rowTransform_0409.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0409 hU
  have hcols := hrows.permuteColumns columnPerm_0409
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0409 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0409 = targetTop_0409 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0409 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 5 7 7)) 9 := by
  have htop : targetTop_0409 =
      topOfPattern (R := ℤ) (angle6 0 1 1 5 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0409

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 6, 6, 6)`. -/
def targetTop_0410 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0410 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0410 :
    TopRowRelation targetTop_0410 relationCoefficients_0410 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0410, relationCoefficients_0410, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0410 : BottomDetBound targetTop_0410 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0410

theorem canonicalBound_0410 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 6 6 6)) 9 := by
  have htop : targetTop_0410 =
      topOfPattern (R := ℤ) (angle6 0 1 1 6 6 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0410

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 6, 6, 7)`. -/
def targetTop_0411 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0411 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0411 :
    TopRowRelation targetTop_0411 relationCoefficients_0411 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0411, relationCoefficients_0411, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0411 : BottomDetBound targetTop_0411 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0411

theorem canonicalBound_0411 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 6 6 7)) 9 := by
  have htop : targetTop_0411 =
      topOfPattern (R := ℤ) (angle6 0 1 1 6 6 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0411

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 6, 7, 7)`. -/
def targetTop_0412 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 0, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0412 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0412 :
    TopRowRelation targetTop_0412 relationCoefficients_0412 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0412, relationCoefficients_0412, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0412 : BottomDetBound targetTop_0412 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0412

theorem canonicalBound_0412 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 6 7 7)) 9 := by
  have htop : targetTop_0412 =
      topOfPattern (R := ℤ) (angle6 0 1 1 6 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0412

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 1, 7, 7, 7)`. -/
def targetTop_0413 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 1, 1, 1]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0413 : Fin 3 → ℤ :=
  ![0, 1, (-1)]

theorem topRelation_0413 :
    TopRowRelation targetTop_0413 relationCoefficients_0413 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0413, relationCoefficients_0413, Fin.sum_univ_succ]
  · refine ⟨1, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0413 : BottomDetBound targetTop_0413 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0413

theorem canonicalBound_0413 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 7 7 7)) 9 := by
  have htop : targetTop_0413 =
      topOfPattern (R := ℤ) (angle6 0 1 1 7 7 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0413

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 2, 2, 2, 2)`. -/
def targetTop_0414 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0414 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0414 :
    TopRowRelation targetTop_0414 relationCoefficients_0414 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0414, relationCoefficients_0414, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0414 : BottomDetBound targetTop_0414 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0414

theorem canonicalBound_0414 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 2)) 9 := by
  have htop : targetTop_0414 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0414

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 2, 2, 2, 3)`. -/
def targetTop_0415 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0415 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0415 :
    TopRowRelation targetTop_0415 relationCoefficients_0415 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0415, relationCoefficients_0415, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0415 : BottomDetBound targetTop_0415 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0415

theorem canonicalBound_0415 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 3)) 9 := by
  have htop : targetTop_0415 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0415

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025
