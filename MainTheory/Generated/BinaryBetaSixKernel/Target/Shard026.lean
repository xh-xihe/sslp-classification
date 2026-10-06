-- Generated independently checked transports and rank relations.
import MainTheory.BinaryDetTopUnimodular
import MainTheory.BinaryBetaSixCanonical
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate
import MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate

namespace MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 2, 4)`. -/
def targetTop_0416 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0416 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0416 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0416 : BottomDetBound targetTop_0416 9 := by
  have hU : rowTransform_0416.det.natAbs = 1 := by
    have hdet : rowTransform_0416.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0416 hU
  have hcols := hrows.permuteColumns columnPerm_0416
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0416 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0416 = targetTop_0416 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0416 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 4)) 9 := by
  have htop : targetTop_0416 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0416

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 2, 5)`. -/
def targetTop_0417 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0417 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0417 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0417 : BottomDetBound targetTop_0417 9 := by
  have hU : rowTransform_0417.det.natAbs = 1 := by
    have hdet : rowTransform_0417.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0417 hU
  have hcols := hrows.permuteColumns columnPerm_0417
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0417 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0417 = targetTop_0417 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0417 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 5)) 9 := by
  have htop : targetTop_0417 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0417

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 2, 6)`. -/
def targetTop_0418 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0418 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0418 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0418 : BottomDetBound targetTop_0418 9 := by
  have hU : rowTransform_0418.det.natAbs = 1 := by
    have hdet : rowTransform_0418.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0418 hU
  have hcols := hrows.permuteColumns columnPerm_0418
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0418 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0418 = targetTop_0418 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0418 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 6)) 9 := by
  have htop : targetTop_0418 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0418

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 2, 7)`. -/
def targetTop_0419 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0419 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0419 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0419 : BottomDetBound targetTop_0419 9 := by
  have hU : rowTransform_0419.det.natAbs = 1 := by
    have hdet : rowTransform_0419.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Aggregate.bottomBound.transformTopRows rowTransform_0419 hU
  have hcols := hrows.permuteColumns columnPerm_0419
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0419 MainTheory.Generated.BinaryBetaSixKernel.Representative.R009.Base.explicitTop)
          columnPerm_0419 = targetTop_0419 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0419 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 7)) 9 := by
  have htop : targetTop_0419 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 2 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0419

/-- Explicit rank-deficient target for canonical pattern `(0, 1, 2, 2, 3, 3)`. -/
def targetTop_0420 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 0]

/-- A checked nonzero integral relation among the three fixed top rows. -/
def relationCoefficients_0420 : Fin 3 → ℤ :=
  ![0, 0, 1]

theorem topRelation_0420 :
    TopRowRelation targetTop_0420 relationCoefficients_0420 := by
  constructor
  · funext j
    fin_cases j <;>
      norm_num [targetTop_0420, relationCoefficients_0420, Fin.sum_univ_succ]
  · refine ⟨2, ?_⟩
    change (1 : ℤ) ≠ 0
    norm_num

theorem literalBound_0420 : BottomDetBound targetTop_0420 9 :=
  BottomDetBound.ofTopRowRelation (B := 9) topRelation_0420

theorem canonicalBound_0420 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 3 3)) 9 := by
  have htop : targetTop_0420 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 3 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0420

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 3, 4)`. -/
def targetTop_0421 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0421 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0421 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0421 : BottomDetBound targetTop_0421 9 := by
  have hU : rowTransform_0421.det.natAbs = 1 := by
    have hdet : rowTransform_0421.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0421 hU
  have hcols := hrows.permuteColumns columnPerm_0421
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0421 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0421 = targetTop_0421 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0421 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 3 4)) 9 := by
  have htop : targetTop_0421 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 3 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0421

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 3, 5)`. -/
def targetTop_0422 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0422 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0422 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0422 : BottomDetBound targetTop_0422 9 := by
  have hU : rowTransform_0422.det.natAbs = 1 := by
    have hdet : rowTransform_0422.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0422 hU
  have hcols := hrows.permuteColumns columnPerm_0422
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0422 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0422 = targetTop_0422 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0422 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 3 5)) 9 := by
  have htop : targetTop_0422 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 3 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0422

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 3, 6)`. -/
def targetTop_0423 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0423 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0423 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0423 : BottomDetBound targetTop_0423 9 := by
  have hU : rowTransform_0423.det.natAbs = 1 := by
    have hdet : rowTransform_0423.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0423 hU
  have hcols := hrows.permuteColumns columnPerm_0423
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0423 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0423 = targetTop_0423 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0423 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 3 6)) 9 := by
  have htop : targetTop_0423 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 3 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0423

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 3, 7)`. -/
def targetTop_0424 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 1, 1;
     0, 0, 0, 0, 0, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0424 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 1;
     0, 0, 1]

def columnPerm_0424 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0424 : BottomDetBound targetTop_0424 9 := by
  have hU : rowTransform_0424.det.natAbs = 1 := by
    have hdet : rowTransform_0424.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0424 hU
  have hcols := hrows.permuteColumns columnPerm_0424
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0424 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0424 = targetTop_0424 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0424 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 3 7)) 9 := by
  have htop : targetTop_0424 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 3 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0424

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 4, 4)`. -/
def targetTop_0425 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0425 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0425 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0425 : BottomDetBound targetTop_0425 9 := by
  have hU : rowTransform_0425.det.natAbs = 1 := by
    have hdet : rowTransform_0425.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0425 hU
  have hcols := hrows.permuteColumns columnPerm_0425
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0425 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0425 = targetTop_0425 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0425 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 4 4)) 9 := by
  have htop : targetTop_0425 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 4 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0425

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 4, 5)`. -/
def targetTop_0426 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0426 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0426 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0426 : BottomDetBound targetTop_0426 9 := by
  have hU : rowTransform_0426.det.natAbs = 1 := by
    have hdet : rowTransform_0426.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Aggregate.bottomBound.transformTopRows rowTransform_0426 hU
  have hcols := hrows.permuteColumns columnPerm_0426
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0426 MainTheory.Generated.BinaryBetaSixKernel.Representative.R012.Base.explicitTop)
          columnPerm_0426 = targetTop_0426 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0426 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 4 5)) 9 := by
  have htop : targetTop_0426 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0426

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 4, 6)`. -/
def targetTop_0427 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0427 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0427 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0427 : BottomDetBound targetTop_0427 9 := by
  have hU : rowTransform_0427.det.natAbs = 1 := by
    have hdet : rowTransform_0427.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0427 hU
  have hcols := hrows.permuteColumns columnPerm_0427
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0427 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0427 = targetTop_0427 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0427 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 4 6)) 9 := by
  have htop : targetTop_0427 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 4 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0427

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 4, 7)`. -/
def targetTop_0428 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 0, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0428 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0428 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0428 : BottomDetBound targetTop_0428 9 := by
  have hU : rowTransform_0428.det.natAbs = 1 := by
    have hdet : rowTransform_0428.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Aggregate.bottomBound.transformTopRows rowTransform_0428 hU
  have hcols := hrows.permuteColumns columnPerm_0428
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0428 MainTheory.Generated.BinaryBetaSixKernel.Representative.R013.Base.explicitTop)
          columnPerm_0428 = targetTop_0428 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0428 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 4 7)) 9 := by
  have htop : targetTop_0428 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 4 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0428

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 5, 5)`. -/
def targetTop_0429 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0429 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0429 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0429 : BottomDetBound targetTop_0429 9 := by
  have hU : rowTransform_0429.det.natAbs = 1 := by
    have hdet : rowTransform_0429.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Aggregate.bottomBound.transformTopRows rowTransform_0429 hU
  have hcols := hrows.permuteColumns columnPerm_0429
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0429 MainTheory.Generated.BinaryBetaSixKernel.Representative.R010.Base.explicitTop)
          columnPerm_0429 = targetTop_0429 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0429 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 5 5)) 9 := by
  have htop : targetTop_0429 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 5 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0429

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 5, 6)`. -/
def targetTop_0430 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0430 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
     1, 0, 0;
     0, 0, 1]

def columnPerm_0430 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0430 : BottomDetBound targetTop_0430 9 := by
  have hU : rowTransform_0430.det.natAbs = 1 := by
    have hdet : rowTransform_0430.det = (-1) := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Aggregate.bottomBound.transformTopRows rowTransform_0430 hU
  have hcols := hrows.permuteColumns columnPerm_0430
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0430 MainTheory.Generated.BinaryBetaSixKernel.Representative.R014.Base.explicitTop)
          columnPerm_0430 = targetTop_0430 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0430 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 5 6)) 9 := by
  have htop : targetTop_0430 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 5 6) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0430

/-- Explicit target top block for canonical pattern `(0, 1, 2, 2, 5, 7)`. -/
def targetTop_0431 : Matrix (Fin 3) (Fin 6) ℤ :=
  !![0, 1, 0, 0, 1, 1;
     0, 0, 1, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Proposed integral change of basis; determinant `+-1` is checked below. -/
def rowTransform_0431 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 1;
     1, 0, 0;
     0, 1, 0]

def columnPerm_0431 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem literalBound_0431 : BottomDetBound targetTop_0431 9 := by
  have hU : rowTransform_0431.det.natAbs = 1 := by
    have hdet : rowTransform_0431.det = 1 := by decide
    simp [hdet]
  have hrows :=
    MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Aggregate.bottomBound.transformTopRows rowTransform_0431 hU
  have hcols := hrows.permuteColumns columnPerm_0431
  have htop :
      permuteTopColumns
          (transformTopRows rowTransform_0431 MainTheory.Generated.BinaryBetaSixKernel.Representative.R011.Base.explicitTop)
          columnPerm_0431 = targetTop_0431 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [htop] at hcols
  exact hcols

theorem canonicalBound_0431 :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 5 7)) 9 := by
  have htop : targetTop_0431 =
      topOfPattern (R := ℤ) (angle6 0 1 2 2 5 7) := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← htop]
  exact literalBound_0431

end MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026
